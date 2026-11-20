import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothConeFaceOfInteriorCommonPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSmoothConeFaceOfInteriorCommonPoint.lean&line=45#L45)
-/
theorem _root_.GlobalTheory.T.smoothCone_face_of_interior_common_point : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X], IsPolFanOn bar φ X → ∀ (r r' : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X) (γ' : Fin r' → LinearMap.BilinForm ℤ X), IsCone bar φ γ → IsCone bar φ γ' → ∀ (c : Fin r → ℕ) (c' : Fin r' → ℕ), (∀ j, 0 < c j) → ∑ j, c j • γ j = ∑ j, c' j • γ' j → ∀ j, ∃ j', γ j = γ' j' := by
  first | exact @GlobalTheory.Poinc.intCone_face | exact GlobalTheory.Poinc.intCone_face | (intros; apply GlobalTheory.Poinc.intCone_face <;> assumption)
