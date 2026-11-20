import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelMulPowOfInvariantModPow
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsLevelMulPowOfInvariantModPow.lean&line=117#L117)
-/
theorem _root_.GlobalTheory.T.exists_level_mul_pow_of_invariant_mod_pow : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (l n M e : ℕ), l.Prime → 0 < M → ∀ f : X.Kˣ, Lev X (M ^ e) f → (∀ γ ∈ CongruenceSubgroup.Gamma M, ∃ g : X.Kˣ, X.sl (ofSL γ) (f : X.K) = f * (g : X.K) ^ (l ^ n)) → ∃ (k : ℕ) (h : X.Kˣ), Lev X (M * l ^ k) ((f : X.K) * (h : X.K) ^ (l ^ n)) := by
  first | exact @GlobalTheory.KZ.ES.exists_lev_mul_pow_of_invariant_mod_pow | exact GlobalTheory.KZ.ES.exists_lev_mul_pow_of_invariant_mod_pow | (intros; apply GlobalTheory.KZ.ES.exists_lev_mul_pow_of_invariant_mod_pow <;> assumption)
