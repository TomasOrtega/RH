import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZalgEqAdjoinFiniteCapelli
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetPolyMapMonic
open NumberField GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CuspRep.zalg_eq_adjoin_finite_caps` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FZalgEqAdjoinFiniteCapelli.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.zalg_eq_adjoin_finite_capelli : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (b : ℕ), ∃ T : Finset (Module.End ℂ (Sm E b)), (∀ t ∈ T, ∃ (τ : E →+* ℂ) (u : ℂ), t = cap τ u) ∧ Zalg E b = Algebra.adjoin ℂ (T : Set (Module.End ℂ (Sm E b))) := by
  first | exact @GlobalTheory.CuspRep.zalg_eq_adjoin_finite_caps | exact GlobalTheory.CuspRep.zalg_eq_adjoin_finite_caps | (intros; apply GlobalTheory.CuspRep.zalg_eq_adjoin_finite_caps <;> assumption)
