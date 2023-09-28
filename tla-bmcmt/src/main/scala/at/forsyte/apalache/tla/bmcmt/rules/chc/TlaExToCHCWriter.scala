package at.forsyte.apalache.tla.bmcmt.rules.chc

import at.forsyte.apalache.io.OutputManager
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.formulas._
import at.forsyte.apalache.tla.pp.UniqueNameGenerator
import scalaz.unused

/**
 * TlaExToCHCWriter handles the last step of transpiling: assembling the .vmt output file.
 *
 * Given a disassembled module (extracted init, next, inv, etc.) VMTWriter determines which parts get which `VMTExpr`
 * wrappers. Then, using TermToCHCWriter, it translates the VMT terms to output strings, and adds sort/function
 * declarations and definitions.
 *
 * @author
 *   Jure Kukovec
 */
class TlaExToCHCWriter(gen: UniqueNameGenerator) {
  // Main entry point.
  def annotateAndWrite(
      // funDecls: Seq[FunDef], // not working
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

    // Not sure what to do with CInits yet, we might want to add them ass axioms later
//    val cinits = cInit.map { case (_, ex) =>
//      rewriter.rewrite(ex)
//    }
//    val cinitStrs = cinits.map(TlaExToCHCWriter.mkSMT2String)

    // convenience shorthand
    def rewrite: TlaEx => TermBuilderTForCHC = rewriter.rewrite

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

    val (smtDeclsForCHC@_, (inits, transitions, invs@_)) = (for {
      initTerms <- initCmps
      transitionTerms <- transitionCmps
      invTerms <- invCmps
    } yield (initTerms, transitionTerms, invTerms)).run(SmtDeclarationsForCHC.init)

    val initStrs = inits.map(TermToCHCWriter.mkVMTString)

    val transStrs = transitions.map(TermToCHCWriter.mkVMTString)

    /*val invStrs = invs.map(TermToCHCWriter.mkVMTString)

    // Each variable v in varDecls needs the VMT binding Next(v, v')
    val nextBindings = varDecls.map { case d @ TlaVarDecl(name) =>
      val sort = TlaType1ToSortConverterForCHC.sortFromType(d.typeTag.asTlaType1())
      Next(nextName(name), mkVariable(name, sort), mkVariable(CHCprimeName(name), sort))
    }

    //val nextStrs = nextBindings.map(TermToCHCWriter.mkVMTString)*/

    // Variable declarations
    val smtVarDecls = varDecls.map(TermToCHCWriter.mkSMTDecl)

    /*// Sort declaration
    val allSorts = setConstants.values.toSet ++ smtDeclsForCHC.uninterpretedSorts.map(UninterpretedSort)
    val sortDecls = allSorts.map(TermToCHCWriter.mkSortDecl)

    // Uninterpreted literal declaration and uniqueness assert
    val ulitDecls = smtDeclsForCHC.uninterpretedLiterals.values.map(TermToCHCWriter.mkConstDecl)
    val disticntAsserts = allSorts.flatMap { s =>
      val litsForSortS = smtDeclsForCHC.uninterpretedLiterals.values.filter {
        _.sort == s
      }
      (if (litsForSortS.size > 1) Some(litsForSortS) else None).map(TermToCHCWriter.assertDistinct)
    }*/

    // Prime variable declarations // added
    val smtVarDeclsPrime = varDecls.map(TermToCHCWriter.mkSMTDeclPrime) // added

    // Variable type declaration
    val smtVarType = varDecls.map(TermToCHCWriter.mkSMTVarType) // added

    // Variable declaration
    val smtVar = varDecls.map(TermToCHCWriter.mkSMTVar) // added

    // Prime variable declaration
    val smtVarPrime = varDecls.map(TermToCHCWriter.mkSMTVarPrime) // added

    OutputManager.withWriterInRunDir(TlaExToCHCWriter.outFileName) { writer =>

      // smtVarDecls.foreach(writer.println) // (val1 Bool) (val2 Int)
      // smtVarDeclsPrime.foreach(writer.println) // (val1.prime Bool) (val2.prime Int)
      // smtVarType.foreach(writer.println) // BoolInt
      // smtVar.foreach(writer.println) // var1var2
      // smtVarPrime.foreach(writer.println) //val1.prime val2.prime
      writer.println("(set-logic HORN)")
      writer.println()
      writer.print(s"(declare-fun pred (")
      smtVarType.foreach(writer.print)
      writer.print(s") Bool)")

      writer.println()
      writer.println()

      writer.println(";Init")
      writer.print(s"(assert\n\t(forall (")
      smtVarDecls.foreach(writer.print)
      writer.print(s")\n\t\t(=>\n\t\t\t")
      initStrs.foreach(writer.print)
      writer.print(s"\n\t\t\t(pred ")
      smtVar.foreach(writer.print)
      writer.print(s")\n\t\t)\n\t)\n)")

      writer.println()
      writer.println()
      /*
      for ((transStrs, index) <- transStrs.zipWithIndex) { // testing
        //writer.print(s"Element at index $index: $transStrs")
        writer.print(s"$transStrs")
      }
      */
      for ((transStrs, index) <- transStrs.zipWithIndex) {
        writer.println(";Next")
        writer.print(s"(assert\n\t(forall (")
        smtVarDecls.foreach(writer.print)
        smtVarDeclsPrime.foreach(writer.print)
        writer.print(s")\n\t\t(=>\n\t\t\t(and (pred ")
        smtVar.foreach(writer.print)
        writer.print(s")") // )\n\t\t\t
        //transStrs.foreach(writer.print)
        writer.print(s"$transStrs")
        writer.print(s")\n\t\t\t(pred ")
        smtVarPrime.foreach(writer.print)
        writer.print(s")\n\t\t)\n\t)\n)\n")
      }

      writer.println()
      /*
      for (index <- 0 until transStrs.size) { // testing
        val element = transStrs(index)
        //writer.print(s"Element at index $index: $element")
        writer.print(s"$element")
      }

      for (index <- 0 until transStrs.size) {
        val element = transStrs(index)
        //writer.print(s"Element at index $index: $transStrs")
        //writer.print(s"$transStrs")
        writer.println(";Next")
        writer.print(s"(assert\n\t(forall (")
        smtVarDecls.foreach(writer.print)
        smtVarDeclsPrime.foreach(writer.print)
        writer.print(s")\n\t\t(=>\n\t\t\t(and (pred ")
        smtVar.foreach(writer.print)
        writer.print(s")") // )\n\t\t\t
        //transStrs.foreach(writer.print)
        writer.print(s"$element")
        writer.print(s")\n\t\t\t(pred ")
        smtVarPrime.foreach(writer.print)
        writer.print(s")\n\t\t)\n\t)\n)\n")
      }
      */
      writer.println(s"(check-sat)")
      //writer.println(s"(get-model)")
      writer.println(s"(exit)")

      /*writer.println(s"transStr size")
      writer.println(transStrs.size)
      writer.println(s"nextTransitions size")
      writer.println(nextTransitions.size)*/

      /*writer.println(";Sorts")
      sortDecls.foreach(writer.println)
      writer.println()
      writer.println(";Constants")
      ulitDecls.foreach(writer.println)
      writer.println()
      disticntAsserts.foreach(writer.println)
      writer.println()
      writer.println(";Variables")
      smtVarDecls.foreach(writer.println)
      writer.println()
      writer.println(";Variable bindings")
      nextStrs.foreach(writer.println)
      writer.println()
//      writer.println(";TLA constant initialization")
//      cinitStrs.foreach(writer.println)
//      writer.println()
      writer.println(";Initial states")
      initStrs.foreach(writer.println)
      writer.println()
      writer.println(";Transitions")
      transStrs.foreach(writer.println)
      writer.println()
      writer.println(";Invariants")
      invStrs.foreach(writer.println)*/
    }
  }

}

object TlaExToCHCWriter {
  val outFileName = "output.chc"
}
