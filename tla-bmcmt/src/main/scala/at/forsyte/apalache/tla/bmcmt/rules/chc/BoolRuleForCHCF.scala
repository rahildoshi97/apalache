package at.forsyte.apalache.tla.bmcmt.rules.chc

import at.forsyte.apalache.tla.bmcmt.RewriterException
import at.forsyte.apalache.tla.lir.formulas.Booleans._
import at.forsyte.apalache.tla.lir.formulas.Integers._
import at.forsyte.apalache.tla.lir.oper.{TlaArithOper, TlaBoolOper}
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}

/**
 * BoolRule defines translations for reTLA patterns which use operators from propositional logic.
 *
 * @author
 *   Jure Kukovec
 */
class BoolRuleForCHCF(rewriter: ToTermRewriterForCHC) extends FormulaRuleForCHC {
  override def isApplicable(ex: TlaEx): Boolean =
    ex match {
      case OperEx(TlaBoolOper.and | TlaBoolOper.or | TlaBoolOper.not | TlaBoolOper.implies | TlaBoolOper.equiv | TlaArithOper.lt | TlaArithOper.le | TlaArithOper.gt | TlaArithOper.ge, _*) =>
        true
      case _ => false
    }

  // convenience shorthand
  private def rewrite: TlaEx => TermBuilderTForCHC = rewriter.rewrite

  // Assume isApplicable
  override def apply(ex: TlaEx): TermBuilderTForCHC =
    ex match {
      case OperEx(TlaBoolOper.and, args @ _*) => cmpSeq(args.map(rewrite)).map { seq => And(seq: _*) }
      case OperEx(TlaBoolOper.or, args @ _*)  => cmpSeq(args.map(rewrite)).map { seq => Or(seq: _*) }
      case OperEx(TlaBoolOper.not, arg)       => rewrite(arg).map(Neg)
      case OperEx(TlaBoolOper.implies, lhs, rhs) =>
        for {
          lhsTerm <- rewrite(lhs)
          rhsTerm <- rewrite(rhs)
        } yield Impl(lhsTerm, rhsTerm)
      case OperEx(TlaBoolOper.equiv, lhs, rhs) =>
        for {
          lhsTerm <- rewrite(lhs)
          rhsTerm <- rewrite(rhs)
        } yield Equiv(lhsTerm, rhsTerm)
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
      case _ => throw new RewriterException(s"BoolRule not applicable to $ex", ex)
    }
}
