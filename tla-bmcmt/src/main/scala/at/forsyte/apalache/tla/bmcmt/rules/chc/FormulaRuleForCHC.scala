package at.forsyte.apalache.tla.bmcmt.rules.chc

import at.forsyte.apalache.tla.lir.TlaEx

/**
 * FormulaRule is analogous to RewritingRule, except that it produces a Term translation directly, while possibly
 * discharging declarations. It is side-effect free, instead of mutating the arena and solver context.
 */
trait FormulaRuleForCHC {
  def isApplicable(ex: TlaEx): Boolean

  def apply(ex: TlaEx): TermBuilderTForCHC
}
