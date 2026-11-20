import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormWt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTerm

open NumberField MeasureTheory

namespace GlobalTheory.CMTypeNorm

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Separate the alternatives or extract the components of the hypothesis. Prove the first alternative. Prove the second alternative. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis.

Prove the first alternative. Prove the second alternative. A detailed English derivation is pending.
-/
theorem place_bijective {K : Type} [Field K] [NumberField K] {I : Type} {φ : I → K →+* ℂ} (h : GlobalTheory.CMVal.IsCMType φ) :
    Function.Bijective fun i => InfinitePlace.mk (φ i) := by
  constructor
  · intro i j hij
    obtain ⟨k, -, hk⟩ := h (φ j)
    have hj : j = k := hk j (Or.inl rfl)
    have hi : i = k := by
      apply hk i
      rcases InfinitePlace.mk_eq_iff.mp hij with h1 | h1
      · exact Or.inl h1.symm
      · exact Or.inr h1.symm
    rw [hi, hj]
  · intro w
    obtain ⟨k, hk, -⟩ := h w.embedding
    refine ⟨k, ?_⟩
    show InfinitePlace.mk (φ k) = w
    rw [← InfinitePlace.mk_embedding w, InfinitePlace.mk_eq_iff]
    rcases hk with h1 | h1
    · exact Or.inl h1.symm
    · exact Or.inr h1.symm

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Move the embeddings inside the algebraic operations. Both sides reduce to the same expression.
-/
theorem prod_norm_sq_eq_absNorm :
    ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ),
      GlobalTheory.CMVal.IsCMType φ → ∀ α : 𝓞 K,
        ∏ i, ‖φ i (α : K)‖ ^ 2 = ((Ideal.absNorm (Ideal.span {α}) : ℕ) : ℝ) := by
  intro K _ _ _ I _ φ h α
  have h1 : ∏ i, ‖φ i (α : K)‖ ^ 2 = ∏ w : InfinitePlace K, w (α : K) ^ w.mult := by
    refine Fintype.prod_bijective _ (place_bijective h) _ _ fun i => ?_
    rw [InfinitePlace.apply, IsTotallyComplex.mult_eq]
  rw [h1, InfinitePlace.prod_eq_abs_norm, Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int, Nat.cast_natAbs]
  push_cast
  rfl

end GlobalTheory.CMTypeNorm
