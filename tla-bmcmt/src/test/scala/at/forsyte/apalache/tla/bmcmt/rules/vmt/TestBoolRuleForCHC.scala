package at.forsyte.apalache.tla.bmcmt.rules.chc

import at.forsyte.apalache.tla.bmcmt.rules.chc.{BoolRuleForCHC, ToTermRewriterImplForCHC}
import at.forsyte.apalache.tla.lir.formulas.Booleans._
import at.forsyte.apalache.tla.lir.formulas.Term
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.types.tla
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestBoolRuleForCHC extends AnyFunSuite {
  val rewriter: ToTermRewriterForCHC = ToTermRewriterImplForCHC()

  val rule: FormulaRule = new BoolRuleForCHC(rewriter)

  val b: TlaType1 = BoolT1

  val p: TBuilderInstruction = tla.name("p", b)
  val pVar: Term = BoolVar("p")
  val q: TBuilderInstruction = tla.name("q", b)
  val qVar: Term = BoolVar("q")

  val expected: Map[TlaEx, BoolExpr] = Map(
      tla.and(p, q).build -> And(pVar, qVar),
      tla.not(p).build -> Neg(pVar),
      tla.or(tla.impl(p, q), p).build -> Or(Impl(pVar, qVar), pVar),
  )

  test("BoolRule applicability") {
    expected.keys.foreach { ex =>
      assert(rule.isApplicable(ex))
    }

    val notApp = List(
        tla.tuple(tla.int(1), tla.int(2)),
        tla.funSet(tla.name("S", SetT1(IntT1)), tla.dotdot(tla.int(1), tla.int(42))),
        tla.unchanged(tla.name("x", IntT1)),
        tla.forall(tla.name("x", IntT1), tla.name("S", SetT1(IntT1)), tla.name("p", BoolT1)),
        tla.int(2),
        tla.bool(true),
    )

    notApp.foreach { ex =>
      assert(!rule.isApplicable(ex))
    }
  }

  test("BoolRule correctness") {
    expected.foreach { case (k, expected) =>
      val actual = rule(k).run(SmtDeclarationsForCHC.init)._2
      assert(actual == expected)
    }
  }

}
