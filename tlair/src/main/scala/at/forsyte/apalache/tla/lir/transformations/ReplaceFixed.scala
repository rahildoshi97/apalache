package at.forsyte.apalache.tla.lir.transformations

import at.forsyte.apalache.tla.lir.TlaEx

/**
  * A Transformation where every instance of `replacedEx` is replaced by an instance of `newEx`
  */
sealed case class ReplaceFixed(
                                replacedEx : TlaEx,
                                newEx : TlaEx,
                                listeners : TransformationListener*
                              )
  extends Transformation(
    ex => if ( ex == replacedEx ) newEx.deepCopy() else ex,
    listeners : _*
  )