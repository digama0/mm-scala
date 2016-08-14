package org.metamath.scala

import scala.collection.mutable.Stack
import scala.collection.mutable.ArrayBuffer
import org.metamath.scala._
import scala.collection.mutable.ArrayBuilder
import scala.collection.mutable.HashMap
import scala.collection.mutable.HashSet
import scala.collection.mutable.PriorityQueue
import scala.collection.mutable.MutableList

class Verifier(implicit db: Database) {
  db.declsPar foreach {
    case a: Assert if a.proofUnparsed.isDefined => new VerifyOne(a)
    case _ =>
  }

  private class VerifyOne(current: Assert) {
    val substs = new HashMap[Floating, ParseTree]
    val varsIn = new HashMap[Floating, HashSet[Floating]]
    def error = MMError(s"verify $current failed")

    private def getVarsIn(v: Floating) = varsIn.getOrElseUpdate(v, substs(v).varsIn)

    private def subst: ParseTree => ParseTree = {
      case HypNode(v: Floating) => substs(v)
      case AssertNode(a, child) => AssertNode(a, child map subst)
      case _ => throw error
    }

    private def entry(s: String) = db.statements(s) match {
      case h: Hypothesis => new TreeEntry(h.formula)
      case a: Assert => AssertEntry(a)
    }

    val stack = new Stack[TreeEntry]
    def applyStep(e: DictionaryEntry) = {
      stack.push(e match {
        case AssertEntry(a) =>
          var top: List[TreeEntry] = Nil
          substs.clear; varsIn.clear
          for (h <- a.hyps) top = stack.pop :: top
          for ((h, TreeEntry(tc, expr)) <- a.hyps zip top) {
            if (h.typecode != tc) throw error
            h match {
              case v: Floating => substs.put(v, expr)
              case e: Essential => if (subst(e.parse) != expr) throw error
            }
          }
          for (
            (x, y) <- a.disjoint;
            z <- getVarsIn(x.activeFloat); w <- getVarsIn(y.activeFloat)
          ) current.disjoint.exists(_ == (z, w))
          TreeEntry(a.typecode, subst(a.parse))
        case t: TreeEntry => t
      })
    }

    val unparsed = current.proofUnparsed.get.split("\\s+").filter(_.nonEmpty)

    if (unparsed.head == "(") {
      val dictionary = new ArrayBuffer[DictionaryEntry]
      for (h <- current.hyps) dictionary += new TreeEntry(h.formula)
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
      for (h <- current.hyps) dictionary += new TreeEntry(h.formula)
    } else {
      for (s <- unparsed) applyStep(entry(s))
    }

    stack match {
      case Stack(t) if t.tc == current.typecode =>
        current.proof = Some(t.expr)
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