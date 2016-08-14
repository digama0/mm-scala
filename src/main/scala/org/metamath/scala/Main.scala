package org.metamath.scala

import java.io.FileReader

object Main {
  def main(args: Array[String]) {
    args match {
      case Array(file) =>
        val parser = new MMParser(new FileReader(file))
        println("File parsing...")
        implicit val db = parser.parse
        println("Verify...")
        new Verifier
        //println("Check definitions...")
        //new DefinitionChecker
      case _ => println("Usage: mm-scala file.mm")
    }
  }
}