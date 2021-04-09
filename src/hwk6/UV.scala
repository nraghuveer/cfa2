package hwk6

import scala.collection.immutable.Set
import common._ 
import interprocedural._

// set of variables that may be uninitialized
case class Vars(vars: Set[Tuple2[String, String]]) extends Lattice[Vars] {
  def lub(that: Vars) = Vars(vars.union(that.vars))
  
  override def toString = "{"+vars.toList.sortBy(x=>x).mkString(", ")+"}"
}

// uninitialized variables: forward and may analysis
case class UV_IFDS(stmt: Statement) extends Analysis[Vars] {
  val cfg = ForwardCFG(stmt)
  val entry = real_entry
  val exit = real_exit
  
  val extremalValue = Vars(Util.vars(stmt).map(x=>(Util.zero, x)))
  val bottom = Vars(Set())
  
  def transfer(node: Node, l: Vars) = node match {
    case IntraNode(stmt) => transfer(stmt, l)

    // for each parameter p, if its argument is not initialized, then p is not initialized 
    case CallNode(stmt, to) => {
      def h(args: List[Expression]) = {
        val Some(FunctionDecl(_, FunctionExpr(_, ps, _))) = to.f 
        val params = ps.map(p => p.str) 
        val s = for((p, e) <- params zip args; if initialized(e, l)) yield p
        Vars((params.toSet -- s).map((Util.zero, _)))     // function f(x, y) { ... }   f(10);
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
      // uninitialized parameters + all local variables (minus parameters) + return variable
      // take the uninitialized parameters and create a mapping between them, if x is uninint, then (x, x)
      Vars(l.vars.filter(_._1 == Util.zero).map(_._2)
        .map(x => (x, x)) ++ (Util.vars(stmt) -- ps.map(_.str)).map((Util.zero, _)) ++
                        Set((Util.zero, Util.zero), (Util.zero, Util.ret)))
    }
    
    case ExitNode(Some(_)) => {
      // Check if there a link to the ?r from any of the variables
      // todo, this is incomplete implementation, complete this before submitting the assignment
      Vars(l.vars.filter(_._2 == Util.ret))
    } // keep the return variable if it is present
    
    case n@RetNode(stmt, _) => {
      val lc = entry(cfg.call_ret(n))  // dataflow facts before the call
      
      def h(x: String) = {
        // Vars(if (l.vars.contains(Util.ret)) lc.vars + x else lc.vars - x)
        Vars(if (lc.vars.map(_._2).contains(Util.ret)) lc.vars ++ Set((Util.zero, x)) else lc.vars -- Set((Util.zero, x)))
      }
      
      stmt match { 
        case ExprStmt(AssignExpr(_, LVarRef(x), FuncCall(_, _))) => h(x) // x = f(e);
        case VarDeclStmt(IntroduceVar(x), FuncCall(_, _)) => h(x)    // var x = f(e);
        case _ => lc // f(e);
      } 
    }
    
    case _ => l
  }
  
  // are variables in 'e' all initialized
  def initialized(e: Expression, l: Vars) = {
    // check if the given expression has any un intialized variables
    // for each free variable in the expression check if there exists (0, x) in the l
    Util.fv(e).filter(x => l.vars.contains(Util.zero, x) || l.vars.contains(x, x)).isEmpty
  }
  
  def transfer(stmt: Statement, l: Vars) = {
    	def kill_gen(y: String, e: Expression) = {
        def get_uninitialized_vars(e: Expression, l: Vars): Set[String] ={
          Util.fv(e).filter(x => l.vars.contains((Util.zero, x)) || l.vars.contains(x, x))
        }
        if(initialized(e, l)){
          Vars(l.vars -- Set((Util.zero, y), (y,y)))
        }
        else{
          // not initialized
          val killset = Set((Util.zero, y), (y, y))
          val genset = get_uninitialized_vars(e, l).map(x => (x, y))
          Vars(l.vars -- killset ++ genset )}
      }
    	
	    stmt match {
	      case VarDeclStmt(IntroduceVar(y), e) => {     
	        e match {
	          case EmptyExpr() => Vars(l.vars ++ Set((Util.zero, y)))      // var y;
	          case _ => kill_gen(y, e)                  // var y = e;
	        }
	      }
	      case ExprStmt(AssignExpr(_, LVarRef(y), e)) => kill_gen(y, e) // y = e;
	      case ReturnStmt(e) => kill_gen(Util.ret, e)  // return e;
	      case _ => l
	    }
  }
}