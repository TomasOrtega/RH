import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrdegLeGenerators
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.trdeg_le_of_map_mem_closure_algebraic_union` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FTrdegLeGenerators.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.trdeg_le_generators : ∀ {k K K' A : Type} [Field k] [Field K] [Field K'] [CommRing A] (ρ : k →+* K) (σ : K →+* K') (φ : A →+* K),
    Subfield.closure (Set.range φ) = ⊤ → ∀ (L₀ : Subfield K'),
    (∀ z ∈ L₀, @IsAlgebraic k K' _ _ (σ.comp ρ).toAlgebra z) → ∀ {d : ℕ} (cf : Fin d → K'),
    (∀ r, σ (φ r) ∈ Subfield.closure ((L₀ : Set K') ∪ Set.range cf)) →
    @Algebra.trdeg k K _ _ ρ.toAlgebra ≤ (d : Cardinal) := by
  first | exact @GlobalTheory.trdeg_le_of_map_mem_closure_algebraic_union | exact GlobalTheory.trdeg_le_of_map_mem_closure_algebraic_union | (intros; apply GlobalTheory.trdeg_le_of_map_mem_closure_algebraic_union <;> assumption)
