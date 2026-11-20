import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviTorusHyperbolicPair
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPlanePairOfPair

open scoped Matrix
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HyperbolicDecomp.exists_decomp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLeviTorusHyperbolicPair.lean&line=72#L72)
-/
theorem _root_.GlobalTheory.T.levi_torus_hyperbolic_pair : ∀ (R : Type) [CommRing R] (c : R →+* R) (d d₁ : ℕ) (j : Matrix (Fin d) (Fin d) R) (j₁ : Matrix (Fin d₁) (Fin d₁) R) (x y : Fin d → R) (ι : Matrix (Fin d) (Fin d₁) R), (∀ z, c (c z) = z) → (∀ i k, c (j k i) = -j i k) → d = d₁ + 2 → GlobalTheory.LeviTorusExists.sesq c j x x = 0 → GlobalTheory.LeviTorusExists.sesq c j y y = 0 → GlobalTheory.LeviTorusExists.sesq c j x y = 1 → (∀ z, GlobalTheory.LeviTorusExists.sesq c j (ι *ᵥ z) x = 0 ∧ GlobalTheory.LeviTorusExists.sesq c j (ι *ᵥ z) y = 0) → ιᵀ * j * ι.map c = j₁ → IsUnit j₁.det → ∀ v : Fin d → R, ∃ z, v = GlobalTheory.LeviTorusExists.sesq c j v y • x - GlobalTheory.LeviTorusExists.sesq c j v x • y + ι *ᵥ z := by
  first | exact @GlobalTheory.HyperbolicDecomp.exists_decomp | exact GlobalTheory.HyperbolicDecomp.exists_decomp | (intros; apply GlobalTheory.HyperbolicDecomp.exists_decomp <;> assumption)
