import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfFiniteGeneratingAutomorphisms
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGaloisOfFiniteGeneratingAutomorphisms.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.isGalois_of_finite_fixed_automorphisms : ∀ (K K' : Type) [Field K] [Field K'] (i : K →+* K'), i.Finite → ∀ (Γ : Type) [Finite Γ] (s : Γ → (K' ≃+* K')), (∀ g x, s g (i x) = i x) → (∀ y : K', (∀ g, s g y = y) → y ∈ i.range) → (letI := i.toAlgebra; IsGalois K K') ∧ ∀ σ : K' ≃+* K', (∀ x, σ (i x) = i x) → σ ∈ Submonoid.closure (Set.range s) := by
  first | exact @GlobalTheory.galois_of_finite_generating_automorphisms | exact GlobalTheory.galois_of_finite_generating_automorphisms | (intros; apply GlobalTheory.galois_of_finite_generating_automorphisms <;> assumption)
