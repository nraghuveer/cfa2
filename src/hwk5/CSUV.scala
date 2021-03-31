package hwk5
import common._


case class Context(call_strings: List[Long]) {
  val k = 2
  def extend(label: Long) = {
    val x = call_strings ++ List(label)
    Context(if (x.length > k) x.drop(1) else x)
  }
  override def toString = "[" + call_strings.mkString(",") + "]"
}


case class CSVars(vars: Set[(Context, String)]) extends Lattice[CSVars] {
  def lub(that: CSVars) = CSVars(vars.union(that.vars))

  val contexts = vars.map(x=>x._1).toSet

  def variables(ctx: Context) = vars.filter(x => x._1 == ctx).map(x=>x._2)

  def initialized(e: Expression, ctx: Context) = Util.fv(e).intersect(variables(ctx)).isEmpty

  def kill_gen(y: String, e: Expression) = {
    val gen = for(ctx <- contexts; if initialized(e, ctx)) yield (ctx, y)
    val kill = for(ctx <- contexts; if ! initialized(e, ctx)) yield (ctx, y)
    CSVars(vars -- kill ++ gen)
  }

  def gen(y: String) = CSVars(vars ++ contexts.map(ctx => (ctx, y)))

  def gen(ys: List[String]) = CSVars(vars ++ contexts.flatMap(ctx => ys.map(y=>(ctx, y))))

  def extend(lc: Long) = CSVars(contexts.map(ctx => ctx.extend(lc)).toSet.map((ctx: Context) => (ctx, Util.zero)))

  override def toString = "{"+vars.toList.sortBy(x=>x._2).mkString(", ")+"}"
}


// uninitialized variables: forward and may analysis
case class CSUV(stmt: Statement) extends Analysis[CSVars] {
  val cfg = ForwardCFG(stmt)
  val entry = real_entry
  val exit = real_exit

  val extremalValue = CSVars((Util.vars(stmt) + Util.zero).map(x => (Context(Nil), x)))
  val bottom = CSVars(Set())

  def transfer(node: Node, l: CSVars): CSVars = node match {
    case IntraNode(stmt) => transfer(stmt, l)

    // for each parameter p, if its argument is not initialized, then p is not initialized
    case CallNode(stmt, to) => {
      def h(args: List[Expression]) = {
        val Some(FunctionDecl(_, FunctionExpr(_, ps, _))) = to.f
        val params = ps.map(p => p.str)
        val ctx = l.extend(stmt.id).gen(params)
        val initliazed_vars: Map[Context, List[String]] = ctx.contexts.map(c => (c, for((p, e) <- params zip args; if initialized(e, ctx, c)) yield p)).toMap
        // kill the variables that initialized in all contexts
        ctx.vars.filter(x => !initliazed_vars(x._1).contains(x._2))
        ctx
      }

      stmt match {
        case ExprStmt(FuncCall(_, args)) => h(args)                       // f(a);
        case ExprStmt(AssignExpr(_, _, FuncCall(_, args))) => h(args)     // x = f(a);
        case VarDeclStmt(_, FuncCall(_, args)) => h(args)                 // var x = f(a);
        case _ => bottom
      }
    }
    // add variables appearing in the body of the function and the return variable
    case EntryNode(Some(FunctionDecl(_, FunctionExpr(_,ps,stmt)))) => {
      l.gen((Util.vars(stmt) -- ps.map(p=>p.str) + Util.ret).toList) // uninitialized parameters + all local variables (minus parameters) + return variable
    }

    case ExitNode(Some(_)) => {
      CSVars(l.vars.filter(x=> x._2 == Util.ret))
    } // keep the return variable if it is present

    case n@RetNode(stmt, _) => {
      val lc = entry(cfg.call_ret(n))  // dataflow facts before the call

      def h(x: String): CSVars = {
        CSVars(Set())  // TODO: compelte this
        // for each context, if the corresponding context has the return variable remove that from the entry dataflow fact of the callnode
        val gen = for(ctx <- l.contexts; if initialized(List(Util.ret), l, ctx)) yield (ctx, x)
        val kill = for(ctx <- l.contexts; if ! initialized(List(Util.ret), l, ctx)) yield (ctx, x)
        CSVars(lc.vars -- kill ++ gen)
      }

      stmt match {  // x is left hand side variable
        case ExprStmt(AssignExpr(_, LVarRef(x), FuncCall(_, _))) => h(x) // x = f(e);
        case VarDeclStmt(IntroduceVar(x), FuncCall(_, _)) => h(x)    // var x = f(e);
        case _ => lc // f(e);
      }
    }

    case _ => l
  }

  // are variables in 'e' all initialized
  def initialized(e: Expression, l: CSVars, ctx: Context): Boolean = l.variables(ctx).intersect(Util.fv(e)).isEmpty

  def initialized(vars: List[String], l: CSVars, ctx: Context) = l.variables(ctx).intersect(vars.toSet).isEmpty

  def transfer(stmt: Statement, l: CSVars) = {

    stmt match {
      case VarDeclStmt(IntroduceVar(y), e) => {
        e match {
          case EmptyExpr() => l.gen(y)   // var y;
          case _ => l.kill_gen(y, e)                 // var y = e;
        }
      }
      case ExprStmt(AssignExpr(_, LVarRef(y), e)) => l.kill_gen(y, e) // y = e;
      case ReturnStmt(e) => l.kill_gen(Util.ret, e)  // return e;
      case _ => l
    }
  }
}