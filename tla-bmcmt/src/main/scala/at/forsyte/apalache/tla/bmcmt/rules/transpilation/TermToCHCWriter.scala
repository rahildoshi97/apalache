package at.forsyte.apalache.tla.bmcmt.rules.transpilation

import at.forsyte.apalache.tla.lir.{TlaType1, TlaVarDecl, Typed}
import at.forsyte.apalache.tla.lir.formulas.Integers._
import at.forsyte.apalache.tla.lir.formulas._

/**
 * TermToCHCWriter manages the translation of Terms to strings, to be written to the final output file.
 *
 * @author
 *   Rahil Doshi
 */
object TermToCHCWriter extends parentTermToCHCWriter {}

abstract class parentTermToCHCWriter extends parentTermToVMTWriter {
  // Main entry point, does the translation recursively
  override def ex1(term: Term): String =
    term match {
      case Lt(a, b)    => s"(< ${tr(a)} ${tr(b)})"
      case Le(a, b)    => s"(<= ${tr(a)} ${tr(b)})"
      case Gt(a, b)    => s"(> ${tr(a)} ${tr(b)})"
      case Ge(a, b)    => s"(>= ${tr(a)} ${tr(b)})"
      case Plus(a, b)  => s"(+ ${tr(a)} ${tr(b)})"
      case Minus(a, b) => s"(- ${tr(a)} ${tr(b)})"
      case Uminus(x)   => s"(- ${tr(x)})"
      case Mult(a, b)  => s"(* ${tr(a)} ${tr(b)})"
      case Div(a, b)   => s"(/ ${tr(a)} ${tr(b)})"
      case Mod(a, b)   => s"(mod ${tr(a)} ${tr(b)})"
      case x           => throw new NotImplementedError(s"${x.getClass.getName} is not supported.")

    }

  // Constructs an SMT prime variable declaration from a TLA variable declaration
  def mkSMTDeclPrime(d: TlaVarDecl): String =
    d.typeTag match {
      case Typed(tt: TlaType1) =>
        val (_, to) = sortAsFn(TlaType1ToSortConverter.sortFromType(tt))

        def mkDecl(name: String) = s"($name $to) "

        s"${mkDecl(CHCprimeName(d.name))}"

      case _ => ""
    } // (val1.prime Bool) (val2.prime Int)

  // Constructs an SMT variable type declaration from a TLA variable declaration
  def mkSMTVarType(d: TlaVarDecl): String =
    d.typeTag match {
      case Typed(tt: TlaType1) =>
        val (_, to) = sortAsFn(TlaType1ToSortConverter.sortFromType(tt))

        def mkDecl(name: String) = s"$to "

        s"${mkDecl(d.name)}"

      case _ => ""
    } // Bool Int

  // Constructs an SMT variable declaration from a TLA variable declaration
  def mkSMTVar(d: TlaVarDecl): String =
    d.typeTag match {
      case Typed(tt: TlaType1) =>
        val (_, _) = sortAsFn(TlaType1ToSortConverter.sortFromType(tt))

        def mkDecl(name: String) = s"$name "

        s"${mkDecl(d.name)}"

      case _ => ""
    } // val1 val2

  // Constructs an SMT variable prime declaration from a TLA variable declaration
  def mkSMTVarPrime(d: TlaVarDecl): String =
    d.typeTag match {
      case Typed(tt: TlaType1) =>
        val (_, _) = sortAsFn(TlaType1ToSortConverter.sortFromType(tt))

        def mkDecl(name: String) = s"$name "

        s"${mkDecl(CHCprimeName(d.name))}"

      case _ => ""
    } // val1.prime val2,prime

  // Adds the VMT-specific tags, as defined by the VMTExpr wrapper
  override def mkVMTString(chcEx: VMTExpr): String =
    chcEx match {
      case Next(name, current, next) =>
        val (froms, to) = sortAsFn(current.sort)
        val dummyNamesAndSorts = froms.zipWithIndex.map { case (sortString, i) =>
          (s"_p$i@", sortString)
        }
        val fromParis = dummyNamesAndSorts.map { case (dummyName, sortString) =>
          s"($dummyName $sortString)"
        }
        val currentStr = tr(current)
        val currentApp =
          if (dummyNamesAndSorts.isEmpty) currentStr
          else s"($currentStr ${dummyNamesAndSorts.map(_._1).mkString(" ")})"

        s"(define-fun $name (${fromParis.mkString(" ")}) ${to} (! $currentApp :next ${tr(next)}))"
      case Init(_, init)    => s"${tr(init)}"
      case Invar(_, _, inv) => s"${tr(inv)}"
      case Trans(_, trEx)   => s"${tr(trEx)}"
    }
}
