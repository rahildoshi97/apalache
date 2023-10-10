package at.forsyte.apalache.tla.bmcmt.rules.chc

import at.forsyte.apalache.tla.lir.TlaEx

/**
 * `ToTermRewriterForCHC defines a translation from TLA+ to SMT Terms.`
 */
abstract class ToTermRewriterForCHC {
  def rewrite(ex: TlaEx): TermBuilderTForCHC
}
