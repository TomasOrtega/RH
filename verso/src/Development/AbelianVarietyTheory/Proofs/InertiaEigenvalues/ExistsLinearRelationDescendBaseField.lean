import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `K Ω _ _ _ ι _ V c hc hV`. Choose the witnesses or unpack the hypotheses as in `⟨s0, hs0⟩ : ∃ s, c s ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hc (funext h)`.

Set `b` to `Module.Basis.ofVectorSpace K Ω`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, b.repr (c s0) j ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Apply `hs0` to reduce the goal to its premises.

Establish `h0 : b.repr (c s0) = 0` using `Finsupp.ext h`. Conclude with `b.repr.map_eq_zero_iff.mp h0`. Use `⟨fun s => b.repr (c s) j, fun h => hj (congrFun h s0), fun v hv => ?_⟩` and prove the remaining obligations. Establish `h2 : ∑ s, v s • c s = 0`. Rewrite using `[← hV v hv]`.

Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, mul_comm]`. Establish `h3` using `congrArg (fun x => b.repr x j) h2`. Simplify using `only [map_sum, map_smul, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h3`. Rewrite using `[← h3]`.

Conclude with `Finset.sum_congr rfl fun s _ => mul_comm _ _`.
-/
theorem linRelation_descend : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (ι : Type) [Fintype ι]
    (V : Set (ι → K)) (c : ι → Ω), c ≠ 0 → (∀ v ∈ V, ∑ s, c s * algebraMap K Ω (v s) = 0) →
    ∃ d : ι → K, d ≠ 0 ∧ ∀ v ∈ V, ∑ s, d s * v s = 0 := by
  intro K Ω _ _ _ ι _ V c hc hV
  obtain ⟨s0, hs0⟩ : ∃ s, c s ≠ 0 := by
    by_contra h
    push_neg at h
    exact hc (funext h)
  let b := Module.Basis.ofVectorSpace K Ω
  obtain ⟨j, hj⟩ : ∃ j, b.repr (c s0) j ≠ 0 := by
    by_contra h
    push_neg at h
    apply hs0
    have h0 : b.repr (c s0) = 0 := Finsupp.ext h
    exact b.repr.map_eq_zero_iff.mp h0
  refine ⟨fun s => b.repr (c s) j, fun h => hj (congrFun h s0), fun v hv => ?_⟩
  have h2 : ∑ s, v s • c s = 0 := by
    rw [← hV v hv]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Algebra.smul_def, mul_comm]
  have h3 := congrArg (fun x => b.repr x j) h2
  simp only [map_sum, map_smul, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul,
    map_zero, Finsupp.coe_zero, Pi.zero_apply] at h3
  rw [← h3]
  exact Finset.sum_congr rfl fun s _ => mul_comm _ _

end GlobalTheory
