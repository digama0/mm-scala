package org.metamath.scala

import scala.collection.mutable.Stack
import scala.collection.mutable.ArrayBuffer
import org.metamath.scala._
import scala.collection.mutable.ArrayBuilder
import scala.collection.mutable.HashMap
import scala.collection.mutable.HashSet

class Verifier(db: Database) {
  var current: Assert = _
  val substs = new HashMap[Floating, ParseTree]
  val varsIn = new HashMap[Floating, HashSet[Floating]]
  def error = MMError(s"verify $current failed")
  
  db.decls foreach {
    case a: Assert if a.proofUnparsed.isDefined =>
      current = a
      try { a.proof = Some(verify(a.proofUnparsed.get.split("\\s+").filter(_.nonEmpty))) }
      catch { case e: NoSuchElementException => throw error.initCause(e) }
    case _ =>
  }
  
  private def getVarsIn(v: Floating) = varsIn.getOrElseUpdate(v, {
    val set = new HashSet[Floating]
    def varsRec(t: ParseTree): Any = t match {
      case HypNode(v: Floating) => set += v
      case AssertNode(a, child) => child foreach varsRec
    }
    varsRec(substs(v)); set
  })

  private def subst: ParseTree => ParseTree = {
    case HypNode(v: Floating) => substs(v)
    case AssertNode(a, child) => AssertNode(a, child map subst) 
    case _ => throw error
  }

  private def entry(s: String) = db.statements(s) match {
    case h: Hypothesis => new TreeEntry(h.formula)
    case a: Assert => AssertEntry(a)
  }

  def verify(unparsed: Array[String]): ParseTree = {
    val stack = new Stack[TreeEntry]
    def applyStep(e: DictionaryEntry) = e match {
      case AssertEntry(a) =>
        var top: List[TreeEntry] = Nil
        substs.clear; varsIn.clear
        for (h <- a.frame.hyps) top = stack.pop :: top
        for ((h, TreeEntry(tc, expr)) <- a.frame.hyps zip top) {
          if (h.formula.typecode != tc) throw error
          h match {
            case v: Floating => substs.put(v, expr)
            case e: Essential => assert(subst(e.formula.parse) == expr, throw error)
          }
        }
        for ((x, y) <- a.frame.disjoint;
            z <- getVarsIn(x.activeFloat); w <- getVarsIn(y.activeFloat))
          current.frame.disjoint.exists(_ == (z, w))
        stack push TreeEntry(a.formula.typecode, subst(a.formula.parse))
      case t: TreeEntry => stack push t
    }
    if (unparsed.head == "(") {
      val dictionary = new ArrayBuffer[DictionaryEntry]
      for (h <- current.frame.hyps) dictionary += new TreeEntry(h.formula)
      var i = unparsed.iterator.drop(1)
      def breakpoint: Unit = for (s <- i) {
        if (s == ")") return
        dictionary += entry(s)
      }; breakpoint // This is using return to break out of the loop early
      var k = 0
      for (s <- i; c <- s) {
        c match {
          case c if 'A' to 'T' contains c =>
            val x = 20 * k + (c - 'A')
            if (x >= dictionary.length)
              throw error
            applyStep(dictionary(x))
            k = 0
          case c if 'U' to 'Y' contains c => k = 5 * k + (c - 'T')
          case 'Z' => dictionary += stack.top
        }
      }
      for (h <- current.frame.hyps) dictionary += new TreeEntry(h.formula)
    } else {
      for (s <- unparsed) applyStep(entry(s))
    }
    stack match {
      case Stack(t) if t.tc == current.formula.typecode => t.expr
      case _ => throw error
    }
  }
}

private class DictionaryEntry
private case class AssertEntry(a: Assert) extends DictionaryEntry {
  override def toString = a.toString
}
private case class TreeEntry(tc: Constant, expr: ParseTree) extends DictionaryEntry {
  def this(f: Formula) = this(f.typecode, f.parse)
  override def toString = tc + " " + expr
}