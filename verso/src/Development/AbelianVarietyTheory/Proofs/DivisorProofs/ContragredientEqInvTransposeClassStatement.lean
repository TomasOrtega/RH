import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContragredientEqInvTransposeClass
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsDataDualGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelCharacterAtConjugateSplitPlace
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DualClassTranspose.dualCl_iff` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FContragredientEqInvTransposeClass.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.contragredient_eq_inv_transpose_class : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ x y : IrrGL k, DualCl x y ↔ ∃ (h1 : IsSmooth (x.rep.comp (GlobalTheory.TypeTame.invTranspose x.1))) (h2 : Representation.IsIrreducible (x.rep.comp (GlobalTheory.TypeTame.invTranspose x.1))), y = IrrGL.of (x.rep.comp (GlobalTheory.TypeTame.invTranspose x.1)) h1 h2 := by
  first | exact @GlobalTheory.DualClassTranspose.dualCl_iff | exact GlobalTheory.DualClassTranspose.dualCl_iff | (intros; apply GlobalTheory.DualClassTranspose.dualCl_iff <;> assumption)
