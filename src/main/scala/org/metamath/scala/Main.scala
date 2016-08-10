package org.metamath.scala

import java.io.FileReader

object Main {
  def main(args: Array[String]) {
    args match {
      case Array(file) =>
        val parser = new MMParser(new FileReader(file))
        println("File parsing...")
        val db = parser.parse
        println("Math parsing...")
        new Grammar(db).parseAll
        println("Verify...")
        new Verifier(db)
      case _ => println("Usage: mm-scala file.mm")
    }
  }
}