package at.forsyte.apalache.tla.bmcmt.rules.chc

import at.forsyte.apalache.tla.lir.formulas.{BoolSort, Term, Variable}

/**
 * CHCExpr objects are wrappers around SMT Terms. They exist to let the writer to the output file know which labels to
 * add to which CHC expression.
 */
abstract class CHCExpr

sealed case class Next(name: String, current: Variable, next: Variable) extends CHCExpr {
  require(current.sort == next.sort, s"Variable binding $name must bind two variables of the same sort.")
}
sealed case class Init(name: String, initExpr: Term) extends CHCExpr {
  require(initExpr.sort == BoolSort, s"Initial state predicate $name must have Boolean sort.")
}
sealed case class Trans(name: String, transExpr: Term) extends CHCExpr {
  require(transExpr.sort == BoolSort, s"Transition predicate $name must have Boolean sort.")
}
sealed case class Invar(name: String, idx: Int, invExpr: Term) extends CHCExpr {
  require(invExpr.sort == BoolSort, s"Invariant $name must have Boolean sort.")
}
