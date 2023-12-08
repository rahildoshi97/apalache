package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.io.OutputManager
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.formulas._
import at.forsyte.apalache.tla.pp.UniqueNameGenerator
import scalaz.unused

/**
 * TlaExToCHCWriter handles the last step of transpiling: assembling the .chc output file.
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
  override def annotateAndWrite(
      varDecls: Seq[TlaVarDecl],
      constDecls: Seq[TlaConstDecl],
      @unused cInit: Seq[(String, TlaEx)],
      initTransitions: Seq[(String, TlaEx)],
      nextTransitions: Seq[(String, TlaEx)],
      invariants: Seq[(String, TlaEx)]): Unit = {

    // First, we parse the constant declarations, to extract all restricted sets, i.e.,
    // constants typed with SetT1(ConsT1(_))
    val setConstants = constDecls
      .map { d => (d.name, d.typeTag) }
      .collect {
        case (name, Typed(SetT1(ConstT1(sortName)))) => (name, UninterpretedSort(sortName))
        case (name, Typed(SetT1(StrT1)))             => (name, UninterpretedSort(StrT1.toString))
      }
      .toMap[String, UninterpretedSort]

    val rewriter = new ToTermRewriterImplForCHC(setConstants, gen)

    // convenience shorthand
    def rewrite: TlaEx => TermBuilderT = rewriter.rewrite

    // Each transition in initTransitions needs the VMT wrapper Init
    val initCmps = cmpSeq(initTransitions.map { case (name, ex) =>
      rewrite(ex).map { Init(name, _) }
    })

    // Each transition in nextTransitions needs the VMT wrapper Trans
    val transitionCmps = cmpSeq(nextTransitions.map { case (name, ex) =>
      rewrite(ex).map { Trans(name, _) }
    })

    // Each invariant in invariants needs the VMT wrapper Invar
    val invCmps = cmpSeq(invariants.zipWithIndex.map { case ((name, ex), i) =>
      rewrite(ex).map { Invar(name, i, _) }
    })

    val (_, (inits, transitions, invs)) = (for {
      initTerms <- initCmps
      transitionTerms <- transitionCmps
      invTerms <- invCmps
    } yield (initTerms, transitionTerms, invTerms)).run(SmtDeclarations.init)

    val initStrs = inits.map(TermToCHCWriter.mkVMTString)

    val transStrs = transitions.map(TermToCHCWriter.mkVMTString)

    val invStrs = invs.map(TermToCHCWriter.mkVMTString)

    // Variable declarations
    val smtVarDecls = varDecls.map(TermToCHCWriter.mkSMTDecl)

    // Prime variable declarations // added
    val smtVarDeclsPrime = varDecls.map(TermToCHCWriter.mkSMTDeclPrime)

    // Variable type declaration
    val smtVarType = varDecls.map(TermToCHCWriter.mkSMTVarType)

    // Variable declaration
    val smtVar = varDecls.map(TermToCHCWriter.mkSMTVar)

    // Prime variable declaration
    val smtVarPrime = varDecls.map(TermToCHCWriter.mkSMTVarPrime)

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
      // writer.println(s"(check-sat)")
      // writer.println(s"(exit)")
    }
  }

}

object TlaExToCHCWriter {
  val outFileName = "output.chc"
}
