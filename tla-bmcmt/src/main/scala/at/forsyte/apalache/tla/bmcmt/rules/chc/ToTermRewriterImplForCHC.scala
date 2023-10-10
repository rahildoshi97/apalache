package at.forsyte.apalache.tla.bmcmt.rules.chc

import at.forsyte.apalache.tla.bmcmt.RewriterException
import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.pp.UniqueNameGenerator

/**
 * The ToTermRewriterForCHC implementation from reTLA to SMT Terms.
 */
class ToTermRewriterImplForCHC(constSets: ConstSetMapTForCHC, gen: UniqueNameGenerator) extends ToTermRewriterForCHC {
  // Less optimized rule lookup than SymbStateRewriter, since we have fewer rules, just search the list
  private val setJudgementForCHC = new RestrictedSetJudgementForCHC(constSets)
  private val rulesForCHC: List[FormulaRuleForCHC] = List(
    new BoolRuleForCHC(this),
    new QuantifierRuleForCHC(this, setJudgementForCHC),
    new EUFRuleForCHC(this, setJudgementForCHC, gen),
    new ValueRuleForCHC,
    new IntRuleForCHC(this),
  )

  override def rewrite(ex: TlaEx): TermBuilderTForCHC =
    rulesForCHC.find(r => r.isApplicable(ex)) match {
      case Some(r) =>
        r(ex)

      case None =>
        throw new RewriterException(s"No rule applies to $ex", ex)
    }
}

object ToTermRewriterImplForCHC {
  def apply(
      constSets: ConstSetMapTForCHC = Map.empty,
      generator: UniqueNameGenerator = new UniqueNameGenerator): ToTermRewriterForCHC =
    new ToTermRewriterImplForCHC(constSets, generator)
}
