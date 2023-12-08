package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.tla.bmcmt.RewriterException
import at.forsyte.apalache.tla.lir.formulas.Integers._
import at.forsyte.apalache.tla.lir.oper.TlaArithOper
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}

/**
 * IntRule defines translations for reTLA patterns which use operators from propositional logic.
 *
 * @author
 *   Rahil Doshi
 */
class IntRuleForCHC(rewriter: ToTermRewriter) extends FormulaRule {
  override def isApplicable(ex: TlaEx): Boolean = {
    ex match {
      case OperEx(TlaArithOper.plus | TlaArithOper.minus | TlaArithOper.uminus | TlaArithOper.mult | TlaArithOper.div |
              TlaArithOper.mod, _*) =>
        true
      case _ => false
    }
  }

  // convenience shorthand
  private def rewrite: TlaEx => TermBuilderT = rewriter.rewrite

  // Assume isApplicable
  override def apply(ex: TlaEx): TermBuilderT =
    ex match {
      case OperEx(TlaArithOper.plus, lhs, rhs) =>
        for {
          lhsTerm <- rewrite(lhs)
          rhsTerm <- rewrite(rhs)
        } yield Plus(lhsTerm, rhsTerm)
      case OperEx(TlaArithOper.minus, lhs, rhs) =>
        for {
          lhsTerm <- rewrite(lhs)
          rhsTerm <- rewrite(rhs)
        } yield Minus(lhsTerm, rhsTerm)
      case OperEx(TlaArithOper.uminus, arg) => rewrite(arg).map(Uminus)
      case OperEx(TlaArithOper.mult, lhs, rhs) =>
        for {
          lhsTerm <- rewrite(lhs)
          rhsTerm <- rewrite(rhs)
        } yield Mult(lhsTerm, rhsTerm)
      case OperEx(TlaArithOper.div, lhs, rhs) =>
        for {
          lhsTerm <- rewrite(lhs)
          rhsTerm <- rewrite(rhs)
        } yield Div(lhsTerm, rhsTerm)
      case OperEx(TlaArithOper.mod, lhs, rhs) =>
        for {
          lhsTerm <- rewrite(lhs)
          rhsTerm <- rewrite(rhs)
        } yield Mod(lhsTerm, rhsTerm)
      case _ => throw new RewriterException(s"IntRule not applicable to $ex", ex)
    }
}
