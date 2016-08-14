package org.metamath.scala

import scala.language.implicitConversions
import scala.collection.mutable.{ HashMap, ListBuffer, Stack, MutableList, HashSet }
import scala.util.parsing.combinator.Parsers
import scala.util.parsing.combinator.RegexParsers
import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable.TreeSet

case class MMError(s: String) extends java.lang.Exception(s)

class Database(checkDefn: Boolean) {
  var grammar: Option[Grammar] = None
  var unambiguous = false
  def initGrammar: Grammar = {
    if (grammar.isEmpty)
      grammar = Some(new Grammar()(this))
    grammar.get
  }

  object syms extends HashMap[String, Sym] {
    def +=(s: Sym): Unit = {
      s.seq = size
      put(s.id, s)
    }
    override def apply(s: String): Sym = super.get(s).getOrElse(throw MMError(s"Symbol $s not found"))
  }

  val vartyps = new HashSet[Constant]

  object typecodes extends HashMap[Constant, Constant] {
    def put(key: String, value: String) {
      val ckey = syms(key).asInstanceOf[Constant]
      val cval = syms(value).asInstanceOf[Constant]
      if (key == value)
        vartyps += cval
      else if (!vartyps.contains(cval))
        throw MMError(s"$value must be a previously declared variable typecode")
      if (super.put(ckey, cval).isDefined)
        throw new MMError(s"Redefining typecode $key")
      ckey.tc = true
    }
  }

  val decls = new ArrayBuffer[Declaration]
  lazy val declsPar = decls.par
  lazy val axioms = decls collect { case a: Assert if a.proofUnparsed.isEmpty => a }

  object statements extends HashMap[String, Statement] {
    def +=(s: Statement): Unit = {
      if (put(s.label, s).isDefined) throw new MMError(s"Redefining statement $s")
      s.seq = size
      grammar match {
        case Some(g) =>
          g.add(s)
          g.parse(s.label, s.formula)
          s match {
            case a: Assert if a.proofUnparsed.isEmpty => defn.foreach(_.checkAxiom(a))
            case _ =>
          }
        case _ =>
      }
      decls += s
    }
    override def apply(s: String): Statement = super.get(s).getOrElse(throw MMError(s"Statement $s not found"))
  }

  def asserts(s: String): Assert = statements(s) match {
    case a: Assert => a
    case _ => throw MMError(s"Statement $s is not an assertion")
  }

  val htmldefs = new HashMap[String, String]
  val althtmldefs = new HashMap[String, String]
  val latexdefs = new HashMap[String, String]

  var defn = if (checkDefn) Some(new DefinitionChecker()(this)) else None
}

class Sym(val id: String) {
  def str = id
  var seq: Int = _
  override def toString = id
}
case class Constant(override val id: String) extends Sym(id) {
  var tc: Boolean = false
}
case class Variable(override val id: String) extends Sym(id) {
  var activeFloat: Floating = _
}

case class Formula(typecode: Constant, expr: List[Sym]) {
  require(typecode.tc)
  var parse: ParseTree = _
  override def toString = {
    var s = typecode.id
    expr foreach { e => s += " " + e.id }
    s
  }
}

case class Disjointness(v: Variable*)

class Declaration
case class Comment(text: String) extends Declaration {
  var associated: Option[Statement] = None
}

class Statement(val label: String, val formula: Formula) extends Declaration {
  var seq: Int = _
  def typecode = formula.typecode
  def parse = formula.parse
  override def toString = label
  override def equals(x: Any): Boolean = x match {
    case x: Statement => label == x.label
    case _ => false
  }
  override def hashCode = label.hashCode
  def matches(p: (Constant, Pattern)*)(implicit db: Database): Boolean = false
}
object Statement {
  def unapply(d: Declaration) = {
    if (d.isInstanceOf[Statement]) {
      val s = d.asInstanceOf[Statement]
      Some((s.label, s.formula))
    } else None
  }
}

class Hypothesis(label: String, formula: Formula) extends Statement(label, formula)
case class Floating(override val label: String, override val typecode: Constant, v: Variable)
  extends Hypothesis(label, Formula(typecode, List(v)))
case class Essential(override val label: String, override val formula: Formula)
  extends Hypothesis(label, formula)

class Frame(val dv: List[Disjointness] = Nil, val hyps: List[Hypothesis] = Nil) {
  def ::(d: Disjointness) = new Frame(d :: dv, hyps)
  def ::(h: Hypothesis) = new Frame(dv, h :: hyps)

  def disjoint = new Traversable[(Variable, Variable)] {
    def foreach[U](f: ((Variable, Variable)) => U) {
      dv.foreach(_ match {
        case Disjointness(v @ _*) => for (a <- v; b <- v) if (a != b) f(a, b)
      })
    }
  }
}

case class Assert(override val label: String, override val formula: Formula, val frame: Frame,
    val comment: Option[Comment], val proofUnparsed: Option[String] = None) extends Statement(label, formula) {
  var proof: Option[ParseTree] = None
  var syntax: Boolean = false
  if (comment.isDefined) comment.get.associated = Some(this)
  def hyps = frame.hyps
  def disjoint = frame.disjoint

  def apply(pp: Pattern*) = AssertPattern(this, pp.toList)
  override def matches(p: (Constant, Pattern)*)(implicit db: Database): Boolean = p.splitAt(p.length - 1) match {
    case (l, Seq(r)) =>
      var subst = new HashMap[Int, Floating]
      def matchPart: ((ParseTree, Pattern)) => Boolean = {
        case (AssertNode(a, child), AssertPattern(p, pchild)) if a == p => child zip pchild forall matchPart
        case (HypNode(v: Floating), VarPattern(i)) => subst.put(i, v) match {
          case None => true
          case Some(old) => v == old
        }
        case _ => false
      }
      def matchExpr: ((Statement, (Constant, Pattern))) => Boolean = {
        case (s, (t, p)) => s.typecode == t && matchPart((s.parse, p))
      }
      frame.dv.isEmpty && matchExpr((this, r)) &&
        (hyps collect { case e: Essential => e } zip l forall matchExpr) &&
        HashSet(subst.values.toSeq: _*).size == subst.size
    case _ => false
  }
}

object Assert {
  def trimFrame(formula: Formula, eframe: Frame) = {
    val usedVars = new HashSet[Variable]
    (formula :: (eframe.hyps collect {
      case e: Essential => e.formula
    })).foreach(_.expr foreach {
      case v: Variable => usedVars += v
      case _ =>
    })
    new Frame(
      eframe.dv.map { case d: Disjointness => d.v filter usedVars.contains }
        .collect { case seq if seq.length > 1 => Disjointness(seq: _*) }.reverse,
      eframe.hyps.filter {
        case h: Floating => usedVars.contains(h.v)
        case _ => true
      }.reverse)
  }
}

class ParseTree(val stmt: Statement, val child: List[ParseTree] = Nil) {
  override def toString = "(" + stmt + " " + child.mkString(" ") + ")"
  lazy val varsIn = {
    val set = new HashSet[Floating]
    def varsRec(t: ParseTree): Any = t match {
      case HypNode(v: Floating) => set += v
      case AssertNode(a, child) => child foreach varsRec
    }
    varsRec(this)
    set
  }

}
case class HypNode(v: Hypothesis) extends ParseTree(v) {
  override def toString = v.toString
}
case class AssertNode(a: Assert, override val child: List[ParseTree] = Nil) extends ParseTree(a, child)
object ParseTree {
  implicit def toHypNode(v: Hypothesis) = HypNode(v)
}

class Pattern
case class VarPattern(i: Int) extends Pattern {
  override def toString = i.toString
}
case class AssertPattern(a: Assert, child: List[Pattern] = Nil) extends Pattern {
  override def toString = "(" + a + " " + child.mkString(" ") + ")"
  def ::(newChild: Pattern) = AssertPattern(a, newChild :: child)
}
object Pattern {
  implicit def toAssertPattern(a: Assert) = AssertPattern(a)
  implicit def toVarPattern(i: Int) = VarPattern(i)
}
