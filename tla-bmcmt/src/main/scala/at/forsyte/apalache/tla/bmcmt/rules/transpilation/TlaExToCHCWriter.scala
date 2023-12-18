package at.forsyte.apalache.tla.bmcmt.rules.transpilation

import at.forsyte.apalache.io.OutputManager
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.formulas._
import at.forsyte.apalache.tla.pp.UniqueNameGenerator

/**
 * TlaExToCHCWriter handles the last step of transpiling: assembling the .smt2 output file.
 *
 * Given a disassembled module (extracted init, next, inv, etc.), CHCWriter determines which parts get which `VMTExpr`
 * wrappers. Then, using TermToCHCWriter, it translates the terms to output strings, and adds sort/function declarations
 * and definitions.
 *
 * @author
 *   Rahil Doshi
 */
class TlaExToCHCWriter(gen: UniqueNameGenerator) extends TlaExToVMTWriter(gen) {
  // Main entry point.
  override val TermToWriter: parentTermToCHCWriter = TermToCHCWriter

  override def toTermRewriterImpl(setConstants: Map[String, UninterpretedSort]): ToTermRewriterImpl = {
    new ToTermRewriterImplForCHC(setConstants, gen)
  }

  override def annotateAndWrite2(
      varDecls: Seq[TlaVarDecl],
      setConstants: Map[String, UninterpretedSort],
      initStrs: List[String],
      transStrs: List[String],
      invStrs: List[String],
      smtVarDecls: Seq[String],
      smtDecls: SmtDeclarations): Unit = {

    // Prime variable declarations // added
    val smtVarDeclsPrime = varDecls.map(TermToWriter.mkSMTDeclPrime)

    // Variable type declaration
    val smtVarType = varDecls.map(TermToWriter.mkSMTVarType)

    // Variable declaration
    val smtVar = varDecls.map(TermToWriter.mkSMTVar)

    // Prime variable declaration
    val smtVarPrime = varDecls.map(TermToWriter.mkSMTVarPrime)

    OutputManager.withWriterInRunDir(TlaExToCHCWriter.outFileName) { writer =>
      writer.println("(set-logic HORN)")
      writer.print(s"(declare-fun pred (")
      smtVarType.foreach(writer.print)
      writer.println(s") Bool)")

      writer.println(";Init")
      writer.print(s"(assert\n\t(forall (")
      smtVarDecls.foreach(writer.print)
      writer.print(s")\n\t\t(=>\n\t\t\t")
      initStrs.foreach(writer.print)
      writer.print(s"\n\t\t\t(pred ")
      smtVar.foreach(writer.print)
      writer.println(s")\n\t\t)\n\t)\n)")

      for ((transStrs, _) <- transStrs.zipWithIndex) {
        writer.println(";Next")
        writer.print(s"(assert\n\t(forall (")
        smtVarDecls.foreach(writer.print)
        smtVarDeclsPrime.foreach(writer.print)
        writer.print(s")\n\t\t(=>\n\t\t\t(and (pred ")
        smtVar.foreach(writer.print)
        writer.print(s")\n\t\t\t")
        writer.print(s"$transStrs")
        writer.print(s")\n\t\t\t(pred ")
        smtVarPrime.foreach(writer.print)
        writer.println(s")\n\t\t)\n\t)\n)")
      }

      writer.println(";Invariant")
      if (invStrs.nonEmpty) {
        writer.print(s"(assert\n\t(forall (")
        smtVarDecls.foreach(writer.print)
        writer.print(s")\n\t\t(=>\n\t\t\t(and (pred ")
        smtVar.foreach(writer.print)
        writer.print(s")\n\t\t\t(not (and ")
        invStrs.foreach(writer.print)
        writer.println(s")))\n\t\t\tfalse\n\t\t)\n\t)\n)")
      }
      writer.println(s"(check-sat)")
      writer.println(s"(exit)")
    }
  }

}

object TlaExToCHCWriter {
  val outFileName = "output.smt2"
}
