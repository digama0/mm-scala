package org.metamath.scala

import java.io
import java.io.LineNumberReader

import scala.collection.mutable.MutableList
import scala.collection.mutable.Stack
import scala.util.parsing.combinator.RegexParsers

case class MMParser(in: io.Reader) {
  private val frames = Stack(new Frame)
  val reader = new LineNumberReader(in)

  def parse: Database = {
    var db = new Database
    var lastComment: Option[Comment] = None
    val cparser = new CommentParser(db)
    while (true) {
      var tok = getToken
      tok match {
        case "" => return db
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
          lastComment = None
        case _ =>
          getToken match {
            case "$f" =>
              readUntil("$.") match {
                case List(cs, vs) => {
                  val v = db.syms(vs).asInstanceOf[Variable]
                  val stmt = Floating(tok, db.syms(cs).asInstanceOf[Constant], v)
                  if (!db.vartyps.contains(stmt.typecode))
                    throw MMError(s"variable $v should have a variable typecode in ${stmt.label}")
                  v.activeFloat = stmt
                  db.statements += stmt
                  frames push stmt :: frames.pop
                }
                case _ => throw MMError("Incorrect $f statement")
              }
            case "$e" =>
              val stmt = Essential(tok, readFormula("$."))
              db.statements += stmt
              frames push stmt :: frames.pop
            case "$a" =>
              val formula = readFormula("$.")
              db.statements += Assert(tok, formula, Assert.trimFrame(formula, frames.head), lastComment)
            case "$p" =>
              val formula = readFormula("$=")
              val th = Assert(tok, formula, Assert.trimFrame(formula, frames.head), lastComment)
              th.proofUnparsed = Some(readUntilRaw("$."))
              db.statements += th
              
            case k => throw MMError(s"Not a valid metamath command: $k at line ${reader.getLineNumber}")
          }
          lastComment = None
      }
    }

    def readFormula(s: String) = {
      val ls = readUntil(s).map(db.syms)
      Formula(ls.head.asInstanceOf[Constant], ls.tail)
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

class CommentParser(db: Database) extends RegexParsers {
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
        db.grammatical = true
        l match {
          case List(Arg(typ), Keyword("as"), Arg(vtyp)) => db.typecodes.put(typ, vtyp)
          case _ => l foreach {
            case Arg(typ) => db.typecodes.put(typ, typ)
            case _ => throw MMError("Invalid $j 'syntax' invocation")
          }
        }
      case ("$j", "grammar") => db.grammatical = true
      case ("$j", "unambiguous") =>
        db.grammatical = true
        db.unambiguous = true
        l match {
          case List() =>
          case List(Arg(parser)) =>
          case _ => throw MMError("Invalid $j 'unambiguous' invocation")
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
