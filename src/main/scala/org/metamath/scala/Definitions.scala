package org.metamath.scala

import scala.collection.mutable.MutableList
import scala.collection.mutable.ListBuffer
import scala.collection.mutable.HashSet
import scala.collection.mutable.HashMap
import scala.collection.mutable.ArrayBuffer

class DefinitionChecker(implicit db: Database) {
  val equalities = new HashMap[Constant, Equality]
  val definitions = new HashMap[Assert, Assert]
  val primitives = new HashMap[Assert, Primitive]
  val syntax = new HashMap[Assert, Syntax]
  val justifications = new HashMap[Assert, Assert]
  val deferredErrors = new ArrayBuffer[Exception]

  def addEquality(eq: Assert, refl: Assert, sym: Assert, trans: Assert) {
    eq.hyps match {
      case List(h1, h2) if h1.typecode == h2.typecode =>
        equalities.put(h1.typecode, Equality(eq, refl, sym, trans))
      case _ => throw MMError(s"$eq does not have the right type for an equality")
    }
  }

  def addPrimitive(p: Assert) {
    primitives.put(p, Primitive())
    syntax.get(p) match {
      case Some(s) => s.valid = true
      case _ =>
    }
  }

  def addCongruence(a: Assert) {
    a.parse match {
      case AssertNode(eqeq, List(AssertNode(ax, _), AssertNode(ax2, _))) if ax == ax2 && {
        var eq = equalities(ax.typecode)
        eq.eq == eqeq && {
          val patt = new ListBuffer[(Constant, Pattern)]
          val left = new ListBuffer[Pattern]
          val right = new ListBuffer[Pattern]
          var i = 0
          for (v <- ax.hyps) {
            left += i
            equalities.get(v.typecode) match {
              case Some(e) =>
                patt += ((e.tc, e.eq(i, i + 1)))
                i += 1
              case _ =>
            }
            right += i
            i += 1
          }
          patt += ((eq.tc, eqeq(AssertPattern(ax, left.toList), AssertPattern(ax, right.toList))))
          a.matches(patt: _*)
        }
      } => primitives.get(ax) match {
        case Some(p) => p.congruence = Some(a)
        case _ =>
      }
      case _ => throw MMError(s"invalid 'congruence' invocation for $a")
    }
  }

  def checkEqValid: Boolean = {
    for (e <- equalities.values) {
      for (
        (a, p) <- primitives if p.congruence.isEmpty;
        h <- a.hyps if equalities contains h.typecode
      ) return false
    }
    true
  }

  def unify(subst: HashMap[Floating, ParseTree] = new HashMap[Floating, ParseTree]): ((ParseTree, ParseTree)) => Boolean = {
    case (AssertNode(a, l), AssertNode(a2, l2)) if a == a2 => l zip l2 forall unify(subst)
    case (HypNode(v: Floating), t) => subst.put(v, t) match {
      case Some(old) => old == t
      case _ => true
    }
    case _ => false
  }

  def inferDefinition(a: Assert): Option[Assert] = {
    if (a.syntax || a.hyps.exists(_.isInstanceOf[Essential]))
      return None
    a.parse match {
      case AssertNode(eq, List(AssertNode(ax, child), p)) if (equalities.get(ax.typecode) match {
        case Some(e) => eq == e.eq
        case _ => false
      }) => {
        val used = new HashSet[Variable]
        child foreach {
          case HypNode(h: Floating) if used.add(h.v) =>
          case _ => return None
        }
        for ((x, y) <- a.disjoint if used.contains(x) && used.contains(y)) return None
        Some(ax)
      }
      case _ => None
    }
  }

  def addDefinition(defn: Assert, syn: Option[Assert] = None): Option[Assert] = {
    val in = inferDefinition(defn)
    if (syn.isDefined && in != syn)
      throw MMError(s"$defn claims to be a definition for ${syn.get} but it doesn't look like one")
    in match {
      case Some(ax) => definitions.put(ax, defn) match {
        case Some(old) => throw MMError(s"$ax is defined twice, in $old and $defn")
        case _ =>
          def usesPrevious: ParseTree => Unit = {
            case AssertNode(stmt, child) =>
              if (stmt.seq >= ax.seq)
                throw MMError(s"In the definition $defn, $ax uses the future statement $stmt")
              child foreach usesPrevious
            case _ =>
          }
          usesPrevious(defn.parse.child(1))
          Some(ax)
      }
      case _ => None
    }
  }

  def addJustification(syn: Assert, thm: Assert) {
    justifications.put(syn, thm)
  }

  def appliesToAxiom(target: Assert): ((Assert, Assert)) => Boolean = {
    case (syn, thm) =>
      val subst = new HashMap[ParseTree, ParseTree]
      def unify2: ((ParseTree, ParseTree)) => Boolean = {
        case (AssertNode(a, l), AssertNode(a2, l2)) if a == a2 => l zip l2 forall unify2
        case (x, y) => subst.put(x, y) match {
          case Some(old) => old == x
          case _ => true
        }
      }
      unify2((thm.parse, target.parse)) &&
        (thm.hyps zip target.hyps forall { case (x, y) => unify2((x.parse, y.parse)) }) &&
        (subst forall {
          case (AssertNode(a, child), out) =>
            val used = new HashSet[Variable]
            (child forall {
              case HypNode(h: Floating) if used.add(h.v) => true
              case _ => false
            }) && (out.varsIn forall { h => used contains h.v })
          case _ => true
        })
  }

  def checkAxiom(a: Assert) {
    if (a.syntax)
      syntax.put(a, Syntax())
    else {
      def checkValid(t: ParseTree): Unit = t match {
        case AssertNode(stmt, l) =>
          if (!syntax(stmt).valid) {
            for ((a, p) <- primitives if !a.syntax) {
              val subst = new HashMap[Floating, ParseTree]
              if (unify(subst)((a.parse, t)))
                return subst.values foreach checkValid
            }
            throw new AxiomUsesInvalid(a, stmt)
          }
          l foreach checkValid
        case _ =>
      }
      addDefinition(a) match {
        case Some(syn) => syntax(syn).valid = true
        case _ =>
      }
      try {
        checkValid(a.parse)
      } catch {
        case e: AxiomUsesInvalid =>
//          if (!justifications.exists(appliesToAxiom(a)))
            deferredErrors += e
      }

    }
  }

  def finish =
    for (e <- deferredErrors)
      throw e

  //  for (a <- db.axioms if a.syntax && !primitives.contains(a) && !definitions.contains(a))
  //    println(s"Could not find a definition for $a, but it wasn't marked as primitive")

  //  val definitionss = HashSet(definitions.values.toSeq: _*)
  //  for (a <- db.axioms if !a.syntax && !definitionss.contains(a) && !a.label.startsWith("ax-")) println(a)

  case class Equality(eq: Assert, refl: Assert, sym: Assert, trans: Assert) {
    import Pattern._
    val tc = refl.typecode
    assert(refl.matches((tc, eq(0, 0))) &&
      sym.matches((tc, eq(0, 1)), (tc, eq(1, 0))) &&
      trans.matches((tc, eq(0, 1)), (tc, eq(1, 2)), (tc, eq(0, 2))),
      throw MMError(s"unable to verify equality properties of $eq"))

    val congruences = new HashMap[Assert, Assert]
  }

  case class Primitive() {
    var congruence: Option[Assert] = None
  }

  case class Syntax(var valid: Boolean = false)

  case class AxiomUsesInvalid(a: Assert, stmt: Assert) extends Exception(s"Axiom $a uses syntax $stmt which is not valid at this point")
}

