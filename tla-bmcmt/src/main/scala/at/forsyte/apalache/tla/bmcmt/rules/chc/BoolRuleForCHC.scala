package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.tla.bmcmt.RewriterException
import at.forsyte.apalache.tla.lir.formulas.Integers._
import at.forsyte.apalache.tla.lir.oper.{TlaArithOper, TlaBoolOper}
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}

/**
 * BoolRule defines translations for reTLA patterns which use operators from propositional logic.
 *
 * @author
 *   Rahil Doshi
 */
class BoolRuleForCHC(rewriter: ToTermRewriter) extends BoolRule(rewriter) {
  override def isApplicable(ex: TlaEx): Boolean =
    ex match {
      case OperEx(TlaBoolOper.and | TlaBoolOper.or | TlaBoolOper.not | TlaBoolOper.implies | TlaBoolOper.equiv |
              TlaArithOper.lt | TlaArithOper.le | TlaArithOper.gt | TlaArithOper.ge, _*) =>
        true
      case _ => false
    }

  // Assume isApplicable
  override def applyBoolRule(ex: TlaEx): TermBuilderT =
    ex match {
      case OperEx(TlaArithOper.lt, lhs, rhs) =>
        for {
          lhsTerm <- rewrite(lhs)
          rhsTerm <- rewrite(rhs)
        } yield Lt(lhsTerm, rhsTerm)
      case OperEx(TlaArithOper.le, lhs, rhs) =>
        for {
          lhsTerm <- rewrite(lhs)
          rhsTerm <- rewrite(rhs)
        } yield Le(lhsTerm, rhsTerm)
      case OperEx(TlaArithOper.gt, lhs, rhs) =>
        for {
          lhsTerm <- rewrite(lhs)
          rhsTerm <- rewrite(rhs)
        } yield Gt(lhsTerm, rhsTerm)
      case OperEx(TlaArithOper.ge, lhs, rhs) =>
        for {
          lhsTerm <- rewrite(lhs)
          rhsTerm <- rewrite(rhs)
        } yield Ge(lhsTerm, rhsTerm)
      case _ => throw new RewriterException(s"BoolRuleForCHC not applicable to $ex", ex)
    }
}
