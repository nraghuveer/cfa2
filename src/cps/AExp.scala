package cps

import common.InfixOp._
import common.AssignOp._
import common._
import java.io.File

// <KLam> ::= KLam(<UVar>, <CExp>)
// <ULam> ::= ULam({<UVar>}, <KVar>, <CExp>)
// <AExp> ::= <UVar>
//         |  <Num>
//         |  <Str>
//         |  <Bool>
//         |  <ULam>
//         |  <Void>
// <BExp> ::= <AExp> 
//         |  Prim(<InfixOp>, <AExp>, <AExp>)
// <CExp> ::= KLet(<KVar>, <KLam>, <CExp>)
//         |  ULet(<UVar>, <AExp>, <CExp>)
//         |  If(<UVar>, <CExp>, <CExp>)
//         |  KCall(<KVar>, <AExp>)
//         |  UCall(<UVar>, {<AExp>}, <AExp>)  
//         |  <Begin>
// <Begin> ::= Begin {<Fun>} <CExp>
// <Fun> ::= Fun(<UVar>, <ULam>) 
trait Exp {
  var height = -1
  def add(e: Exp) { e.height = height + 1 }
  def copy(e: Exp) { e.height = height }
  def space = "\t" * height
  
  override def toString = this match {
    case KVar(x) => x
    case UVar(x) => x
    case Num(x) => ""+x
    case Str(x) => x
    case Bool(x) => ""+x
    case Void => "null"
    case KLam(x, e) => s"$x => {\n$e\n$space}"
    case ULam(xs, k, e) => s"(${(xs++List(k)).mkString(", ")}) => {\n$e\n$space}"
    case Prim(op, e1, e2) => s"$e1 $op $e2"
    case KLet(x, e1, e) => s"${space}let $x = $e1\n$e"
    case ULet(x, e1, e) => s"${space}let $x = $e1\n$e"
    case Update(x, e1, e) => s"$space$x = $e1\n$e"
    case If(b, then, els) => s"${space}if ($b) {\n$then\n$space}\n${space}else {\n$els\n$space}"
    case KApp(k, arg) => s"$space$k($arg)"
    case UApp(f, args, k) => s"$space$f(${(args++List(k)).mkString(", ")})"
    case Fun(f, ULam(xs, k, e)) => s"${space}function $f (${(xs++List(k)).mkString(", ")}) {\n$e\n$space}" 
    case Begin(fs, e) => s"$space${fs.mkString("\n")}\n\n$e"
  }
  
  def prep: Unit = this match {
    case KLam(x, e) => { add(e); e.prep } 
    case ULam(xs, k, e) => { add(e); e.prep } 
    case KLet(x, e1, e) => { copy(e1); e1.prep; copy(e); e.prep } 
    case ULet(x, e1, e) => { copy(e1); e1.prep; copy(e); e.prep } 
    case Update(x, e1, e) => { copy(e1); e1.prep; copy(e); e.prep } 
    case If(b, then, els) => { add(then); then.prep; add(els); els.prep } 
    case Fun(f, lam) => { copy(lam); lam.prep } 
    case Begin(fs, e) => { fs.foreach ( f => { add(f); f.prep } ); add(e); e.prep }
    case _ => 
  }
}
trait BExp extends Exp // atomic or primitive expression
trait CExp extends Exp // complex expression  
trait AExp extends BExp // atomic expression   
case class KVar (x: String) extends Exp // continuation variable
case class UVar (x: String) extends AExp // user variable
case class KLam (x: UVar, e: CExp) extends Exp // continuation lambda
case class ULam (xs: List[UVar], k: KVar, e: CExp) extends AExp // user lambda
case class Num (x: Double) extends AExp
case class Str (x: String) extends AExp
case class Bool (x: Boolean) extends AExp 
object Void extends AExp // undefined value
case class Prim (op: InfixOp, e1: AExp, e2: AExp) extends BExp // primitive operation 
case class KLet (x: KVar, e1: KLam, e: CExp) extends CExp // continuation definition 
case class ULet (x: UVar, e1: BExp, e: CExp) extends CExp // user definition
case class Update (x: UVar, e1: BExp, e: CExp) extends CExp // assignment
case class If(b: AExp, then: CExp, els: CExp) extends CExp // branch 
case class KApp (k: KVar, arg: BExp) extends CExp // continuation call 
case class UApp (f: AExp, args: List[AExp], k: KVar) extends CExp // user call 
case class Fun(f: UVar, lam: ULam) extends Exp // function declaration (maybe recursive) 
case class Begin(fs: List[Fun], e: CExp) extends CExp // block with recursive definitions 

// map: {"return", "continue", "break"} -> KVar
object CPS {
  var count = 0
  def gensym(x: String) = {
    count = count + 1
    x + count
  }
  
  def t_k (stmts: List[Statement], kmap: Map[String, KVar], k: AExp => CExp): CExp = 
    stmts match {
      case Nil => k(Void)
      case List(stmt) => t_k(stmt, kmap, k)
      case stmt::stmts => t_k(stmt, kmap, _ => t_k (stmts, kmap, k))
    }
  
  // if 'k' is 'x => c(x)', then 'h(c)' else 'let c = x => k(x) in h(c)'
  def check_tail(k: AExp => CExp, h: KVar => CExp) = {
    val x = UVar(gensym("x"))  
    k(x) match {
      case KApp(c@KVar(_), y) if x == y => h(c)
      case _ => {
        val c = KVar(gensym("k"))
        KLet(c, KLam(x, k(x)), h(c))
      }
    }
  }
  
  def t_k (stmt: Statement, kmap: Map[String, KVar], k: AExp => CExp): CExp = {
    stmt match {
      case Script(stmts) => t_k(BlockStmt(stmts), kmap, k)
      case BlockStmt(stmts) => {
        val (funs, rest) = stmts.foldRight((List[FunctionDecl](), List[Statement]()))((stmt, c) => 
          stmt match {
            case f:FunctionDecl => (f::c._1, c._2)
            case _ => (c._1, stmt::c._2)
          }
        )
        val fs = funs.map(fun => Fun(UVar(fun.name.str), m(fun.fun).asInstanceOf[ULam])) 
        val e = t_k(rest, kmap, k)
        if (fs.isEmpty) e else Begin(fs, e)
      }
      case BreakStmt(_) => KApp(kmap("break"), Void)       // ignore label for now
      case ContinueStmt(_) => KApp(kmap("continue"), Void) // ignore label for now
      case ReturnStmt(e) => t_k(e, x => KApp(kmap("return"), x))
      case VarDeclStmt(x, e) => {
        val y = UVar(x.str)
        t_k_prim(e, z => ULet(y, z, k(y)))
      }
      case WhileStmt(cond, body) => {
        val loop_kvar = KVar(gensym("k"))
        val break_kvar = KVar(gensym("k"))
        val continue_kvar = KVar(gensym("k"))
        val kkmap = kmap ++ Map(("break", break_kvar), ("continue", continue_kvar))

        val loop_cexp = t_k(cond, b=> If(b, t_c(body, kkmap, loop_kvar), k(Void)))
        // add break continuation
        val loop_klet = KLet(loop_kvar, KLam(UVar(gensym("u")), loop_cexp), KApp(loop_kvar, Void))
        val break_klet = KLet(break_kvar, KLam(UVar(gensym("u")), k(Void)), loop_klet)
        KLet(continue_kvar, KLam(UVar(gensym("u")), KApp(loop_kvar, Void)), break_klet)



      }
      case VarDeclListStmt(decls) => t_k(decls, kmap, k)
      case IfStmt(cond, thenPart, elsePart) => {  
        val h = (c: KVar) => t_k(cond, b => If(b, t_c(thenPart, kmap, c), t_c(elsePart, kmap, c)))
        check_tail(k, h)
      }
      case ExprStmt(e) => t_k(e, k)
      
      case EmptyStmt() => k(Void)
      
      case _ => throw new Exception("wrong argument in call to t_k: " + stmt)
    }
  }
  
  def t_k (exp: Expression, k: AExp => CExp): CExp =  
    exp match {
      case InfixExpr(op, e1, e2) => t_k_prim(exp, x => { 
        val y = UVar(gensym("u"))
        ULet(y, x, k(y))
      })
      case AssignExpr(op, LVarRef(x1), e2) => {
    	    val y = UVar(x1)
    	    op match {
            case OpAssign => t_k_prim(e2, x2 => Update(y, x2, k(y)))
            case _ => t_k(e2, x2 => Update(y, Prim(AssignOp.toOp(op), y, x2), k(y)))
          }
      }
      case FuncCall(f, as) => { 
    	  val h = (c: KVar) => t_k(f, fx => t_ks(as, xs => UApp(fx, xs, c)))
    	  check_tail(k, h)
      }
      case _ => k(m(exp))
    }
  
  def t_ks (es: List[Expression], k: List[AExp] => CExp): CExp = 
    es match {
      case Nil => k(Nil)
      case e::es => t_k(e, x => t_ks(es, xs => k(x::xs)))
    }
  
  def t_k_prim (exp: Expression, k: BExp => CExp): CExp = 
    exp match {
      case InfixExpr(op, e1, e2) => t_k(e1, x1 => t_k(e2, x2 => k(Prim(op, x1, x2))))
      case _ => t_k(exp, k)
    }
  
  def t_c (stmt: Statement, kmap: Map[String, KVar], c: KVar): CExp = t_k(stmt, kmap, x => KApp(c, x)) 
  
  def t_c (exp: Expression, c: KVar): CExp = t_k(exp, x => KApp(c, x)) 
  
  def m (exp: Expression): AExp =  
    exp match {
      case NumberLit(x) => Num(x)
      case StringLit(x) => Str(x)
      case BoolLit(x) => Bool(x)
      case NullLit() => Void
      case VarRef(x) => UVar(x)
      case FunctionExpr(_, ps, body) => {
        val xs = ps.map(p => UVar(p.str))
        val c = KVar(gensym("k"))
        ULam(xs, c, t_c(body, Map("return" -> c), c))
      }
      case _ => throw new Exception("wrong argument in call to m: " + exp)
  }
}


object Main {
  def main(args: Array[String]) { 
    val ast = GenerateAST(new File("test/fact4.js"))
    val cps = CPS.t_c(ast, Map(), KVar("halt"))   
    cps.prep
    println("let halt = x => console.log(x)\n")
    println(cps)
  }
}
