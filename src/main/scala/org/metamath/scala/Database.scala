package org.metamath.scala

import scala.collection.mutable.{ HashMap, ListBuffer, Stack, MutableList, HashSet }
import scala.util.parsing.combinator.Parsers
import scala.util.parsing.combinator.RegexParsers

case class MMError(s: String) extends java.lang.Exception(s)

class Database {
  var grammatical = false
  var unambiguous = false

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

  val decls = new MutableList[Declaration]

  object statements extends HashMap[String, Statement] {
    def +=(s: Statement): Unit = {
      if (put(s.label, s).isDefined) throw new MMError(s"Redefining statement $s")
      decls += s
    }
    override def apply(s: String): Statement = super.get(s).getOrElse(throw MMError(s"Statement $s not found"))
  }

  val htmldefs = new HashMap[String, String]
  val althtmldefs = new HashMap[String, String]
  val latexdefs = new HashMap[String, String]
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
  override def toString = label
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
case class Floating(override val label: String, typecode: Constant, v: Variable)
  extends Hypothesis(label, Formula(typecode, List(v)))
case class Essential(override val label: String, override val formula: Formula)
  extends Hypothesis(label, formula)

class Frame(val dv: List[Disjointness], val hyps: List[Hypothesis]) {
  def this() = this(Nil, Nil)
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
  val comment: Option[Comment]) extends Statement(label, formula) {
  var proofUnparsed: Option[String] = None
  var proof: Option[ParseTree] = None
  if (comment.isDefined) comment.get.associated = Some(this)
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
}
case class HypNode(v: Hypothesis) extends ParseTree(v) {
  override def toString = v.toString
}
case class AssertNode(a: Assert, override val child: List[ParseTree] = Nil) extends ParseTree(a, child) {
  def ::(newChild: ParseTree) = AssertNode(a, newChild :: child)
}
