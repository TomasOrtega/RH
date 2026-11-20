import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatQuotientSmulTopOfSurjectiveFlat
import Mathlib
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFlatQuotientSmulTopOfSurjectiveFlat.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.flat_quotient_smul_top_of_surjective_flat : ∀ (P R₁ B B₁ : Type) [CommRing P] [CommRing R₁] [CommRing B] [CommRing B₁] [Algebra P B] (f₁ : P →+* R₁) (a₁ : R₁ →+* B₁) (c₁ : B →+* B₁), Function.Surjective f₁ → Function.Surjective c₁ → c₁.comp (algebraMap P B) = a₁.comp f₁ → RingHom.ker c₁ = (RingHom.ker f₁).map (algebraMap P B) → a₁.Flat → Module.Flat (P ⧸ RingHom.ker f₁) (B ⧸ (RingHom.ker f₁ • ⊤ : Submodule P B)) := by
  first | exact @GlobalTheory.flat_quot_smul_top_of_surj_flat | exact GlobalTheory.flat_quot_smul_top_of_surj_flat | (intros; apply GlobalTheory.flat_quot_smul_top_of_surj_flat <;> assumption)
