package at.forsyte.apalache.tla.bmcmt.rules.chc

import at.forsyte.apalache.tla.lir.TlaEx

/**
 * ToTermRewriter defines a translation from TLA+ to SMT Terms.
 *
 * @author
 *   Jure Kukovec
 */
abstract class ToTermRewriterForCHC {
  def rewrite(ex: TlaEx): TermBuilderTForCHC
}
