package at.forsyte.apalache.tla.bmcmt.rules.chc

import at.forsyte.apalache.tla.bmcmt.RewriterException
import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.pp.UniqueNameGenerator

/**
 * The ToTermRewriter implementation from reTLA to SMT Terms.
 *
 * @author
 *   Jure Kukovec
 */
class ToTermRewriterImplForCHC(constSets: ConstSetMapTForCHC, gen: UniqueNameGenerator) extends ToTermRewriterForCHC {
  // Less optimized rule lookup than SymbStateRewriter, since we have fewer rules, just search the list
  private val setJudgement = new RestrictedSetJudgementForCHC(constSets)
  private val rules: List[FormulaRuleForCHC] = List(
    new BoolRuleForCHCForCHC(this),
    new QuantifierRuleForCHC(this, setJudgement),
    new EUFRuleForCHCForCHC(this, setJudgement, gen),
    new ValueRuleForCHC,
    new IntRuleForCHCForCHC(this),
  )

  override def rewrite(ex: TlaEx): TermBuilderTForCHC =
    rules.find(r => r.isApplicable(ex)) match {
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
