package org.metamath.scala

import scala.collection.mutable.HashMap
import scala.collection.mutable.MutableList
import scala.util.parsing.combinator.Parsers
import scala.util.parsing.input.Position
import scala.util.parsing.input.Reader


class Grammar(db: Database) extends Parsers {
  type Elem = Sym
  val parsers = new HashMap[Constant, Parser[ParseTree]]
  val axiomByTC = new HashMap[Constant, MutableList[(Assert, List[Sym])]]
  db.decls foreach {
    case a: Assert if a.proofUnparsed.isEmpty && db.vartyps.contains(a.formula.typecode) => {
      a.frame.dv.foreach(_ => throw new MMError(s"Syntax axiom ${a.label} has a DV condition"))
      a.frame.hyps.foreach {
        case _: Essential => throw new MMError(s"Syntax axiom ${a.label} has a hypothesis")
        case _ =>
      }
      axiomByTC.getOrElseUpdate(a.formula.typecode, new MutableList) += ((a, a.formula.expr))
    }
    case _ =>
  }
  db.vartyps foreach { c =>
    var varP = acceptMatch(c.id+" var", { case vr: Variable
      if vr.activeFloat.typecode == c => HypNode(vr.activeFloat) })
    parsers(c) = axiomByTC.get(c) match {
      case None => varP
      case Some(l) => varP | buildParser(c.id, l)
    }
  }


  def buildParser(name: String, axioms: Seq[(Assert, List[Sym])]): Parser[AssertNode] = {
    val out = new MutableList[Parser[AssertNode]]
    val constants = new HashMap[Constant, MutableList[(Assert, List[Sym])]]
    val variables = new HashMap[Constant, MutableList[(Assert, List[Sym])]]
    axioms foreach { case (a, l) =>
      l.headOption match {
        case None => out += success(AssertNode(a))
        case Some(s) => (s match {
          case c: Constant => constants.getOrElseUpdate(c, new MutableList)
          case v: Variable => variables.getOrElseUpdate(v.activeFloat.typecode, new MutableList)
        }) += ((a, l.tail))
      }
    }
    if (!constants.isEmpty) {
      val constantsLookup = new HashMap[Sym, Parser[AssertNode]]
      constants foreach { case (c, l) => constantsLookup.put(c, buildParser(name + " " + c.id, l)) }
      out += Parser { in =>
        constantsLookup.get(in.first) match {
          case Some(p) => p(in.rest)
          case None => Failure("No match", in)
        }
      }
    }    
    variables foreach { case (c, l) =>
      val sub = buildParser(s"$name <${c.id}>", l)
      out += parsers(c) ~ sub ^^ { case v ~ t => v :: t }
    }
    out.tail.foldRight(out.head)((a,b) => a | b).named(name)
  }
  
  def asConst(s: Sym): Option[Constant] = s match {
    case c: Constant => Some(c)
    case _ => None
  }

  def parseAll {
    db.decls foreach {
      case Statement(label, formula) => parse(label, formula)
      case _ =>
    }
  }

  def parse(label: String, formula: Formula) {
    val c = formula.typecode
    val result = phrase(parsers.get(db.typecodes(c)).get).apply(new SeqReader(formula.expr))
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
