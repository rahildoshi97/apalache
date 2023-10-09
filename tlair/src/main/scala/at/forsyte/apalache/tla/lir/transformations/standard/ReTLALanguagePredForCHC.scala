package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.transformations.{PredResult, PredResultFail, PredResultOk}
import at.forsyte.apalache.tla.lir.values._

import scala.collection.immutable.HashSet

/**
 * <p>Test whether the expressions fit into the reTLA fragment: all calls to user operators are inlined, except the
 * calls to nullary let-in definitions.</p>
 *
 */
class ReTLALanguagePredForCHC extends ContextualLanguagePred {
  override protected def isOkInContext(letDefs: Set[String], expr: TlaEx): PredResult = {
    expr match {
      case ValEx(TlaBool(_)) | ValEx(TlaInt(_)) | ValEx(TlaStr(_)) =>
        PredResultOk()

      case ValEx(TlaIntSet) | ValEx(TlaNatSet) | ValEx(TlaBoolSet) =>
        PredResultOk()

      case NameEx(_) =>
        PredResultOk()

      // Primes are only allowed, when attached to Names
      case OperEx(TlaActionOper.prime, _: NameEx) =>
        PredResultOk()

      case OperEx(oper, args @ _*) if ReTLALanguagePredForCHC.operators.contains(oper) =>
        allArgsOk(letDefs, args)

      // Function application and except are the only place we allow tuples, because that's how multivariable functions
      // get expanded
      case OperEx(TlaFunOper.app, fn, arg) =>
        isOkInContext(letDefs, fn).and(
            arg match {
              case OperEx(TlaFunOper.tuple, args @ _*) => allArgsOk(letDefs, args)
              case _                                   => isOkInContext(letDefs, arg)
            }
        )

      // SANY quirk #19123:
      // [f EXCEPT ![1] = ...] expands to
      // OperEx( except, << 1 >>, ... ) and
      // [f EXCEPT ![1,2] = ...] expands to
      // OperEx(except, << << 1, 2 >> >> , ...)
      // reTLA supports ONLY one-at-a-time, single-level EXCEPT, i.e.
      // [f EXCEPT ![a,b,c,...] = r] (not [f EXCEPT ![a][b] = r] or [f EXCEPT ![a] = r, ![b] = s] )
      case OperEx(TlaFunOper.except, fn, key, value) =>
        isOkInContext(letDefs, fn)
          .and(
              isOkInContext(letDefs, value)
          )
          .and(
              key match {
                // ![a,b,...] case
                case OperEx(TlaFunOper.tuple, OperEx(TlaFunOper.tuple, args @ _*)) =>
                  allArgsOk(letDefs, args)
                // ![a] case
                case OperEx(TlaFunOper.tuple, arg) =>
                  isOkInContext(letDefs, arg)
                // Impossible, but we need case-completeness
                case _ => PredResultFail(List())
              }
          )

      case LetInEx(body, defs @ _*) =>
        // check the let-definitions first, in a sequence, as they may refer to each other
        val defsResult = eachDefRec(letDefs, defs.toList)
        val newLetDefs = defs.map(_.name).toSet
        // check the terminal expression in the LET-IN chain, by assuming the context generated by the definitions
        defsResult
          .and(isOkInContext(letDefs ++ newLetDefs, body))

      case e @ OperEx(TlaOper.apply, NameEx(opName), args @ _*) =>
        // the only allowed case is calling a nullary operator that was declared with let-in
        if (!letDefs.contains(opName)) {
          PredResultFail(List((e.ID, s"undeclared operator $opName")))
        } else if (args.nonEmpty) {
          PredResultFail(List((e.ID, s"non-nullary operator $opName")))
        } else {
          PredResultOk()
        }

      case e =>
        PredResultFail(List((e.ID, e.toString)))
    }
  }
}

object ReTLALanguagePredForCHC {
  private val singleton = new ReTLALanguagePredForCHC

  protected val operators: HashSet[TlaOper] =
    HashSet(
        ApalacheOper.assign,
        ApalacheOper.skolem,
        TlaBoolOper.and,
        TlaBoolOper.equiv,
        TlaBoolOper.exists,
        TlaBoolOper.forall,
        TlaBoolOper.implies,
        TlaBoolOper.not,
        TlaBoolOper.or,
        TlaControlOper.ifThenElse,
        TlaFunOper.funDef,
        TlaOper.eq,
        TlaOper.ne,
        // IntArith
        TlaArithOper.div,
        TlaArithOper.exp,
        TlaArithOper.ge,
        TlaArithOper.gt,
        TlaArithOper.le,
        TlaArithOper.lt,
        TlaArithOper.minus,
        TlaArithOper.mod,
        TlaArithOper.mult,
        TlaArithOper.plus,
        TlaArithOper.uminus,
    )

  def apply(): ReTLALanguagePredForCHC = singleton
}
