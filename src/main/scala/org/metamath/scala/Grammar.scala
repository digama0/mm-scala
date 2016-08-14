package org.metamath.scala

import scala.collection.mutable.HashMap
import scala.collection.mutable.MutableList
import scala.util.parsing.combinator.Parsers
import scala.util.parsing.input.Position
import scala.util.parsing.input.Reader

class Grammar(implicit db: Database) extends Parsers {
  type Elem = Sym
  val _parsers = new HashMap[Constant, Parser[ParseTree]]
  val axiomByTC = new HashMap[Constant, MutableList[(Assert, List[Sym])]]
  val reorderMap = new HashMap[Assert, List[Int]]
  def add(d: Declaration) = d match {
    case a: Assert if a.proofUnparsed.isEmpty && db.vartyps.contains(a.typecode) => {
      for (_ <- a.disjoint) throw new MMError(s"Syntax axiom ${a.label} has a DV condition")
      a.hyps.foreach {
        case _: Essential => throw new MMError(s"Syntax axiom ${a.label} has a hypothesis")
        case _ =>
      }
      a.syntax = true
      axiomByTC.getOrElseUpdate(a.typecode, new MutableList) += ((a, a.formula.expr))
      val vars = a.formula.expr collect { case v: Variable => v }
      reorderMap.put(a, a.hyps collect { case h: Floating => vars.indexOf(h.v) })
      _parsers.clear
    }
    case _ =>
  }

  def parsers(c: Constant) = _parsers.getOrElseUpdate(c, {
    var varP: Parser[ParseTree] = acceptMatch(c.id + " var", {
      case vr: Variable if vr.activeFloat.typecode == c => vr.activeFloat
    })
    axiomByTC.get(c) match {
      case None => varP
      case Some(l) => varP | (buildParser(c.id, l) ^^ { case (a, l) => AssertNode(a, reorderMap(a) map l) })
    }
  })

  def buildParser(name: String, axioms: Seq[(Assert, List[Sym])]): Parser[(Assert, List[ParseTree])] = {
    val out = new MutableList[Parser[(Assert, List[ParseTree])]]
    val constants = new HashMap[Constant, MutableList[(Assert, List[Sym])]]
    val variables = new HashMap[Constant, MutableList[(Assert, List[Sym])]]
    for ((a, l) <- axioms)
      l.headOption match {
        case None => out += success((a, Nil))
        case Some(s) => (s match {
          case c: Constant => constants.getOrElseUpdate(c, new MutableList)
          case v: Variable => variables.getOrElseUpdate(v.activeFloat.typecode, new MutableList)
        }) += ((a, l.tail))
      }
    if (!constants.isEmpty) {
      val constantsLookup = new HashMap[Sym, Parser[(Assert, List[ParseTree])]]
      for ((c, l) <- constants) constantsLookup.put(c, buildParser(name + " " + c.id, l))
      out += Parser { in =>
        constantsLookup.get(in.first) match {
          case Some(p) => p(in.rest)
          case None => Failure("No match", in)
        }
      }
    }
    for ((c, l) <- variables) {
      val sub = buildParser(s"$name <${c.id}>", l)
      out += parsers(c) ~ sub ^^ { case v ~ al => al match { case (a, l) => (a, v :: l) } }
    }
    out.tail.foldRight(out.head)(_ | _).named(name)
  }

  def asConst(s: Sym): Option[Constant] = s match {
    case c: Constant => Some(c)
    case _ => None
  }

  def parse(label: String, formula: Formula) {
    val c = formula.typecode
    val result = phrase(parsers(db.typecodes(c))).apply(new SeqReader(formula.expr))
    formula.parse = if (result.successful) result.get else throw new MMError(s"$result - while parsing $label: $formula")
  }
}

class SeqReader[T](seq: Seq[T], offset: Int = 1) extends Reader[T] {
  def atEnd = seq.isEmpty
  def first = seq.head
  def pos = new Position {
    def line = 1
    def column = offset
    override def toString = column.toString
    override def longString = toString
    def lineContents = ""
  }
  def rest = new SeqReader(seq.tail, offset + 1)
  override def toString = {
    var delim = ""
    var str = ""
    seq foreach { s =>
      str += delim + s
      delim = " "
    }
    str
  }
}
