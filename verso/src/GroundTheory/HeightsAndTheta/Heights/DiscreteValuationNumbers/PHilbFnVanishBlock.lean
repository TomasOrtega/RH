import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Establish `h0 : Finsupp.weight (blockWeight ι) d k = 0`. Rewrite using `[Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]`. Use `Finset.sum_eq_zero fun v hv => ?_` and prove the remaining obligations.

Establish `hv1 : v.1 ≠ k` using `fun e => (Finsupp.mem_support_iff.mp hv) (hne v e)`. Simplify using `[blockWeight, hv1]`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_block_var_of_weight_pos {K : Type} [DecidableEq K] {ι : K → Type}
    (d : (Σ k, ι k) →₀ ℕ) (k : K) (h : 1 ≤ Finsupp.weight (blockWeight ι) d k) :
    ∃ v : Σ k, ι k, v.1 = k ∧ d v ≠ 0 := by
  by_contra hne
  push Not at hne
  have h0 : Finsupp.weight (blockWeight ι) d k = 0 := by
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun v hv => ?_
    have hv1 : v.1 ≠ k := fun e => (Finsupp.mem_support_iff.mp hv) (hne v e)
    simp [blockWeight, hv1]
  omega

/- English proof (translation)
Establish `hspan : Ideal.span ((X : (Σ k, ι k) → MRing ι F) '' {v | v.1 = k}) ≤ Q`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨⟨k', i⟩, hv, rfl⟩`. Simplify using `only [Set.mem_ofPred_eq] at hv`. Substitute `hv` using the available equality.

Conclude with `hX i`. Apply `hspan` to reduce the goal to its premises. Rewrite using `[mem_ideal_span_X_image]`. Introduce `d hd`. Rewrite `hf` using `[mem_weightedHomogeneousSubmodule]`.

Establish `hw : Finsupp.weight (blockWeight ι) d = m` using `hf (Finsupp.mem_support_iff.mp hd)`. Take `⟨v, hv, hdv⟩` from `exists_block_var_of_weight_pos d k (by rw [hw]; exact hm)`. Conclude with `⟨v, hv, hdv⟩`.
-/
theorem mem_of_block_vars_mem {F : Type u} [Field F] {K : Type} [DecidableEq K] {ι : K → Type}
    (Q : Ideal (MRing ι F)) (k : K) (hX : ∀ i, (X ⟨k, i⟩ : MRing ι F) ∈ Q) (m : K → ℕ)
    (hm : 1 ≤ m k) (f : MRing ι F) (hf : f ∈ weightedHomogeneousSubmodule F (blockWeight ι) m) :
    f ∈ Q := by
  have hspan : Ideal.span ((X : (Σ k, ι k) → MRing ι F) '' {v | v.1 = k}) ≤ Q := by
    rw [Ideal.span_le]
    rintro _ ⟨⟨k', i⟩, hv, rfl⟩
    simp only [Set.mem_ofPred_eq] at hv
    subst hv
    exact hX i
  apply hspan
  rw [mem_ideal_span_X_image]
  intro d hd
  rw [mem_weightedHomogeneousSubmodule] at hf
  have hw : Finsupp.weight (blockWeight ι) d = m := hf (Finsupp.mem_support_iff.mp hd)
  obtain ⟨v, hv, hdv⟩ := exists_block_var_of_weight_pos d k (by rw [hw]; exact hm)
  exact ⟨v, hv, hdv⟩

/- English proof (translation)
Introduce `F _ K _ _ ι _ Q k hX m hm`. Unfold `hilbFn`. Use `split_ifs with h`. Establish `hbot : gradedPiece Q (fun k => (m k).toNat) = ⊥`. Rewrite using `[Submodule.eq_bot_iff]`.

Introduce `x hx`. Take `⟨f, hf, rfl⟩` from `Submodule.mem_map.mp hx`. Establish `hfQ : f ∈ Q` using `mem_of_block_vars_mem Q k hX _ (by omega) f hf`. Simplify using `using (Ideal.Quotient.eq_zero_iff_mem).mpr hfQ`. Rewrite using `[hbot, finrank_bot]`.

Both sides reduce to the same expression. Both sides reduce to the same expression.
-/
theorem HilbFnVanishBlock.proof : HilbFnVanishBlock.Statement.{u} := by
  intro F _ K _ _ ι _ Q k hX m hm
  unfold hilbFn
  split_ifs with h
  · have hbot : gradedPiece Q (fun k => (m k).toNat) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hx
      have hfQ : f ∈ Q := mem_of_block_vars_mem Q k hX _ (by omega) f hf
      simpa using (Ideal.Quotient.eq_zero_iff_mem).mpr hfQ
    rw [hbot, finrank_bot]
    rfl
  · rfl

end GroundTheory.Heights₂.Heights.NumbersDVR
