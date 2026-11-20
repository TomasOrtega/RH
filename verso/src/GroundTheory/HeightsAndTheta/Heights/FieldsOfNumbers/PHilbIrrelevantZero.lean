import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegreeBound
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]

omit [Fintype K] in

/- English proof (translation)
Rewrite using `[f.as_sum]`. Use `Ideal.sum_mem _ fun d hd => ?_` and prove the remaining obligations. Establish `hw` using `hf (mem_support_iff.mp hd)`. Rewrite `hw` using `[GroundTheory.Heights₂.Heights.Bridge.weight_blockWeight]`. Establish `hsum : ∑ i, d ⟨k, i⟩ ≠ 0`.

Use `congrFun hw k` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨i, -, hi⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hsum`. Establish `hle : Finsupp.single (⟨k, i⟩ : Σ k, ι k) 1 ≤ d`. Rewrite using `[Finsupp.single_le_iff]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[← tsub_add_cancel_of_le hle, monomial_add_single, pow_one]`. Conclude with `Ideal.mul_mem_left _ _ (hk i)`.
-/
theorem mem_of_isMultiHomog_of_block_le {I : Ideal (MRing ι F)} {k : K}
    (hk : ∀ i : ι k, (X ⟨k, i⟩ : MRing ι F) ∈ I) {b : K → ℕ} (hb : 1 ≤ b k)
    {f : MRing ι F} (hf : IsWeightedHomogeneous (blockWeight ι) f b) : f ∈ I := by
  rw [f.as_sum]
  refine Ideal.sum_mem _ fun d hd => ?_
  have hw := hf (mem_support_iff.mp hd)
  rw [GroundTheory.Heights₂.Heights.Bridge.weight_blockWeight] at hw
  have hsum : ∑ i, d ⟨k, i⟩ ≠ 0 := by
    have := congrFun hw k
    omega
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hle : Finsupp.single (⟨k, i⟩ : Σ k, ι k) 1 ≤ d := by
    rw [Finsupp.single_le_iff]
    omega
  rw [← tsub_add_cancel_of_le hle, monomial_add_single, pow_one]
  exact Ideal.mul_mem_left _ _ (hk i)

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, ∀ i : ι k, (X ⟨k, i⟩ : MRing ι F) ∈ I := by`. Assume the negation of the conclusion as `h`. Conclude with `hI fun k => by`. Assume the negation of the conclusion as `h'`. Conclude with `h ⟨k, fun i => by`.

Assume the negation of the conclusion as `h''`. Conclude with `h' ⟨i, h''⟩⟩`. Rewrite using `[eq_bot_iff]`. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Rewrite using `[Submodule.mem_bot]`.

Establish `: f ∈ I` using `mem_of_isMultiHomog_of_block_le hk (hm k) ((mem_weightedHomogeneousSubmodule _ _ _ _).mp hf)`. Simplify using `using (Ideal.Quotient.eq_zero_iff_mem).mpr this`.
-/
theorem gradedPiece_eq_bot_of_not_isRelevant {I : Ideal (MRing ι F)} (hI : ¬ IsRelevant I)
    {m : K → ℕ} (hm : ∀ k, 1 ≤ m k) : gradedPiece I m = ⊥ := by
  obtain ⟨k, hk⟩ : ∃ k, ∀ i : ι k, (X ⟨k, i⟩ : MRing ι F) ∈ I := by
    by_contra h
    exact hI fun k => by
      by_contra h'
      exact h ⟨k, fun i => by
        by_contra h''
        exact h' ⟨i, h''⟩⟩
  rw [eq_bot_iff]
  rintro _ ⟨f, hf, rfl⟩
  rw [Submodule.mem_bot]
  have : f ∈ I := mem_of_isMultiHomog_of_block_le hk (hm k)
    ((mem_weightedHomogeneousSubmodule _ _ _ _).mp hf)
  simpa using (Ideal.Quotient.eq_zero_iff_mem).mpr this

end

/- English proof (translation)
Introduce `F _ K _ _ ι _ I hI`. Use `filter_upwards [Filter.eventually_ge_atTop (1 : K → ℤ)] with m hm`. Establish `hpos : ∀ k, 0 ≤ m k` using `fun k => le_trans zero_le_one (hm k)`. Unfold `hilbFn`. Rewrite using `[if_pos hpos, gradedPiece_eq_bot_of_not_isRelevant hI (m := fun k => (m k).toNat)]`.

Simplify using the standard rewrite rules. Introduce `k`. Use `hm k` as an intermediate fact. Simplify using `only [Pi.one_apply] at this`. Use linear arithmetic over natural numbers and integers.
-/
theorem HilbIrrelevantZero.proof : HilbIrrelevantZero.Statement.{u} := by
  intro F _ K _ _ ι _ I hI
  filter_upwards [Filter.eventually_ge_atTop (1 : K → ℤ)] with m hm
  have hpos : ∀ k, 0 ≤ m k := fun k => le_trans zero_le_one (hm k)
  unfold hilbFn
  rw [if_pos hpos, gradedPiece_eq_bot_of_not_isRelevant hI (m := fun k => (m k).toNat)]
  · simp
  · intro k
    have := hm k
    simp only [Pi.one_apply] at this
    omega

end

end GroundTheory.Heights₂.Heights.FieldNumbers
