package org.metamath.scala

import java.io
import java.io.LineNumberReader

import scala.collection.mutable.MutableList
import scala.collection.mutable.Stack
import scala.util.parsing.combinator.RegexParsers

case class MMParser(in: io.Reader, strict: Boolean = false, checkDefn: Boolean = false) {
  private val frames = Stack(new Frame)
  val reader = new LineNumberReader(in)

  def parse: Database = {
    implicit var db = new Database(checkDefn)
    if (!strict) db.initGrammar
    var lastComment: Option[Comment] = None
    val cparser = new CommentParser
    while (true) {
      var tok = getToken
      tok match {
        case "" =>
          if (frames.size > 1)
            throw MMError("Extra open scope")
          db.defn.foreach(_.finish)
          return db
        case "$(" =>
          val newComment = readUntilRaw("$)")
          lastComment = if (cparser parseComment newComment) None else Some(Comment(newComment))
          if (lastComment.isDefined) db.decls += lastComment.get
        case "$c" =>
          for (s <- readUntil("$.")) db.syms += Constant(s)
          lastComment = None
        case "$v" =>
          for (s <- readUntil("$.")) db.syms += Variable(s)
          lastComment = None
        case "$d" =>
          val vars = for (s <- readUntil("$.")) yield db.syms(s).asInstanceOf[Variable]
          frames push Disjointness(vars: _*) :: frames.pop
          lastComment = None
        case "${" =>
          frames push frames.head
          lastComment = None
        case "$}" =>
          frames.pop
          if (frames.isEmpty)
            throw MMError("Cannot end global scope!")
          lastComment = None
        case _ =>
          getToken match {
            case "$f" =>
              readUntil("$.") match {
                case List(cs, vs) => {
                  val v = db.syms(vs).asInstanceOf[Variable]
                  val typ = db.syms(cs).asInstanceOf[Constant]
                  if (!db.vartyps.contains(typ)) {
                    if (strict)
                      throw MMError(s"variable $v should have a variable typecode in $tok")
                    db.typecodes.put(cs, cs)
                  }
                  val stmt = Floating(tok, typ, v)
                  v.activeFloat = stmt
                  db.statements += stmt
                  frames push stmt :: frames.pop
                }
                case _ => throw MMError("Incorrect $f statement")
              }
            case "$e" =>
              val stmt = Essential(tok, readFormula(tok, "$."))
              db.statements += stmt
              frames push stmt :: frames.pop
            case "$a" =>
              val formula = readFormula(tok, "$.")
              db.statements += Assert(tok, formula, Assert.trimFrame(formula, frames.head), lastComment)
            case "$p" =>
              val formula = readFormula(tok, "$=")
              db.statements += Assert(tok, formula, Assert.trimFrame(formula, frames.head), lastComment, Some(readUntilRaw("$.")))
            case k => throw MMError(s"Not a valid metamath command: $k at line ${reader.getLineNumber}")
          }
          lastComment = None
      }
    }

    def readFormula(label: String, s: String) = {
      val ls = readUntil(s).map(db.syms)
      val tc = ls.head.asInstanceOf[Constant]
      if (!tc.tc) {
        if (strict)
          throw MMError(s"formula $label should start with a declared typecode")
        else if (db.vartyps.size == 1)
          db.typecodes.put(tc.id, db.vartyps.head.id)
        else
          db.typecodes.put(tc.id, tc.id)
      }
      Formula(tc, ls.tail)
    }
    db
  }

  private def getToken: String = {
    var ret = new StringBuilder
    var ch: Char = 0
    do {
      val r = reader.read; if (r == -1) return ""
      ch = r.toChar
    } while (ch.isWhitespace)
    do {
      ret += ch
      val r = reader.read; if (r == -1) return ret.toString
      ch = r.toChar
    } while (!ch.isWhitespace)
    ret.toString
  }

  private def readUntilRaw(s: String): String = {
    var ret = new StringBuilder
    var i = 0
    while (i < s.length) {
      val r = reader.read
      if (r == -1) return ret.toString
      val ch = r.toChar
      ret += ch
      if (ch == s.charAt(i)) i += 1
      else i = 0
    }
    ret.length -= s.length
    ret.toString
  }

  private def readUntil(s: String) = {
    var active = true
    var out = new MutableList[String]
    for (
      tok <- readUntilRaw(s).split("\\s+")
    ) {
      tok match {
        case "$(" => active = false
        case "$)" => active = true
        case t if active && !t.isEmpty => out += t
        case _ =>
      }
    }
    out.toList
  }
}

class CommentParser(implicit db: Database) extends RegexParsers {
  var commentTyp: String = _
  lazy val specialCommentStart = "$j" | "$t"
  lazy val specialComment = rep(command) <~ blockComment
  lazy val command = keyword ~ rep(commandElement) <~ ";"
  lazy val commandElement: Parser[CommandElement] = keyword | (stringExpr ^^ Arg)
  lazy val keyword = blockComment ~> ("[A-Za-z0-9_]+".r ^^ Keyword) <~ blockComment
  lazy val stringExpr = rep1sep(literal, "+") ^^ (_.mkString)
  lazy val literal = blockComment ~>
    ("'([^']*)'|\"([^\"]*)\"".r ^^ { s => s.substring(1, s.length - 1) }) <~ blockComment
  lazy val blockComment = rep("""/\*(?>(?:(?>[^*]+)|\*(?!/))*)\*/""".r)

  class CommandElement
  case class Keyword(s: String) extends CommandElement
  case class Arg(s: String) extends CommandElement

  def parseComment(str: String): Boolean = {
    parse(specialCommentStart, str) match {
      case Success(s, continuation) =>
        parseAll(specialComment, continuation) match {
          case Success(cs, _) =>
            cs foreach { case k ~ l => handleCommand(s, k, l) }
            true
          case NoSuccess(e, _) => throw MMError(e.toString)
        }
      case _ => false
    }
  }

  def handleCommand(s: String, k: Keyword, l: List[CommandElement]) {
    (s, k.s) match {
      case ("$j", "syntax") =>
        db.initGrammar
        l match {
          case List(Arg(typ), Keyword("as"), Arg(vtyp)) => db.typecodes.put(typ, vtyp)
          case _ => l foreach {
            case Arg(typ) => db.typecodes.put(typ, typ)
            case _ => throw MMError("Invalid $j 'syntax' invocation")
          }
        }
      case ("$j", "grammar") => db.initGrammar
      case ("$j", "unambiguous") =>
        db.initGrammar
        db.unambiguous = true
        l match {
          case List() =>
          case List(Arg(parser)) =>
          case _ => throw MMError("Invalid $j 'unambiguous' invocation")
        }
      case ("$j", "equality") => l match {
        case List(Arg(eq), Keyword("from"), Arg(refl), Arg(sym), Arg(trans)) =>
          db.defn.foreach(_.addEquality(db.asserts(eq), db.asserts(refl), db.asserts(sym), db.asserts(trans)))
        case _ => throw MMError("Invalid $j 'equality' invocation")
      }
      case ("$j", "primitive") => l foreach {
        case Arg(str) => db.defn.foreach(_ addPrimitive db.asserts(str))
        case _ => throw MMError("Invalid $j 'primitive' invocation")
      }
      case ("$j", "congruence") => l foreach {
        case Arg(str) => db.defn.foreach(_ addCongruence db.asserts(str))
        case _ => throw MMError("Invalid $j 'congruence' invocation")
      }
      case ("$j", "definition") => l match {
        case List(Arg(defn), Keyword("for"), Arg(syn)) =>
          db.defn.foreach(_.addDefinition(db.asserts(defn), Some(db.asserts(syn))))
        case _ => throw MMError("Invalid $j 'definition' invocation")
      }
      case ("$j", "justification") => l match {
        case List(Arg(thm), Keyword("for"), Arg(syn)) =>
          db.defn.foreach(_.addJustification(db.asserts(syn), db.asserts(thm)))
        case _ => throw MMError("Invalid $j 'definition' invocation")
      }
      case ("$j", _) =>
      case ("$t", "htmldef") => l match {
        case List(Arg(sym), Keyword("as"), Arg(value)) => db.htmldefs.put(sym, value)
        case _ => throw MMError("Invalid $t 'latexdef' invocation")
      }
      case ("$t", "althtmldef") => l match {
        case List(Arg(sym), Keyword("as"), Arg(value)) => db.althtmldefs.put(sym, value)
        case _ => throw MMError("Invalid $t 'althtmldef' invocation")
      }
      case ("$t", "latexdef") => l match {
        case List(Arg(sym), Keyword("as"), Arg(value)) => db.latexdefs.put(sym, value)
        case _ => throw MMError("Invalid $t 'htmldef' invocation")
      }
      case ("$t", "htmlvarcolor") =>
      case ("$t", "htmltitle") =>
      case ("$t", "htmlhome") =>
      case ("$t", "exthtmltitle") =>
      case ("$t", "exthtmlhome") =>
      case ("$t", "exthtmllabel") =>
      case ("$t", "htmldir") =>
      case ("$t", "althtmldir") =>
      case ("$t", "htmlbibliography") =>
      case ("$t", "exthtmlbibliography") =>
      case ("$t", "htmlcss") =>
      case ("$t", "htmlfont") =>
      case _ => throw MMError(s"Unknown keyword '${k.s}'")
    }
  }
}
