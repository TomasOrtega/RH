import Mathlib
open Matrix

namespace GlobalTheory

/- English proof (translation)
Use `set B := Metric.ball (0 : ℂ) r with hB`. Establish `hBo : IsOpen B` using `Metric.isOpen_ball`. Establish `h0B : (0 : ℂ) ∈ B` using `Metric.mem_ball_self hr`. Set `I : ι → ℂ → Fin p → Fin q → ℂ` to `fun i t a b => (∑ k, M i t a (Sum.inl k) * (z₀ k b + t * w k b)) + ∑ k, M i t a (Sum.inr k) * (1 : Matrix (Fin q) (Fin q) ℂ) k b`. Establish `hI : ∀ i t a b, (M i t * Matrix.fromRows (z₀ + t • w) (1 : Matrix (Fin q) (Fin q) ℂ)) a b = I i t a b`.

Introduce `i t a b`. Simplify using `[I, Matrix.mul_apply, Fintype.sum_sum_type]`. Establish `hId : ∀ i a b, DifferentiableOn ℂ (fun t => I i t a b) B`. Introduce `i a b`. Use `DifferentiableOn.add (DifferentiableOn.fun_sum fun k _ => ?_) (DifferentiableOn.fun_sum fun k _ => ?_)` and prove the remaining obligations.

Conclude with `(hd i a _).mul (by fun_prop)`. Conclude with `(hd i a _).mul (by fun_prop)`. Set `C : ι → Set ℂ` to `fun i => {t | t ∈ B → ∀ a b, I i t a b = 0}`. Establish `hC : ∀ i, IsClosed (C i)`. Introduce `i`.

Establish `hcompl : (C i)ᶜ = ⋃ a, ⋃ b, B ∩ (fun t => I i t a b) ⁻¹' {0}ᶜ`. Use extensionality with `t`. Simplify using `only [C, Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]`. Use `push_neg`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, a, b, h2⟩`. Conclude with `⟨a, b, h1, h2⟩`. Introduce and unpack `⟨a, b, h1, h2⟩`. Conclude with `⟨h1, a, b, h2⟩`. Rewrite using `[← isOpen_compl_iff, hcompl]`.

Conclude with `isOpen_iUnion fun a => isOpen_iUnion fun b => (hId i a b).continuousOn.isOpen_inter_preimage hBo isOpen_compl_singleton`. Establish `hU : ⋃ i, C i = Set.univ`. Use `Set.eq_univ_of_forall fun t => ?_` and prove the remaining obligations. Distinguish the cases in `ht : t ∈ B`. Take `⟨i, hi⟩` from `hk t ht`.

Use `Set.mem_iUnion.2 ⟨i, fun _ a b => ?_⟩` and prove the remaining obligations. Rewrite using `[← hI, hi]`. Both sides reduce to the same expression. Establish `hne : Nonempty ι`. Take `⟨i, _⟩` from `hk 0 h0B`.

Conclude with `⟨i⟩`. Take `⟨i⟩` from `hne`. Conclude with `Set.mem_iUnion.2 ⟨i, fun h => absurd h ht⟩`. Establish `hdense` using `dense_iUnion_interior_of_closed hC hU`. Take `⟨t₀, ht₀B, ht₀⟩` from `hdense.inter_open_nonempty B hBo ⟨0, h0B⟩`.

Take `⟨i, hi⟩` from `Set.mem_iUnion.1 ht₀`. Establish `hzero : ∀ a b, Set.EqOn (fun t => I i t a b) 0 B`. Introduce `a b`. Establish `han : AnalyticOnNhd ℂ (fun t => I i t a b) B` using `(hId i a b).analyticOnNhd hBo`. Use `han.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball _ _).isPreconnected ht₀B ?_` and prove the remaining obligations.

Use `filter_upwards [isOpen_interior.mem_nhds hi, hBo.mem_nhds ht₀B] with t h1 h2`. Conclude with `interior_subset h1 h2 a b`. Establish `hM : ∀ a c, HasDerivAt (fun t => M i t a c) 0 0`. Introduce `a c`. Use `((hd i a c).differentiableAt (hBo.mem_nhds h0B)).hasDerivAt` as an intermediate fact.

Rewrite `this` using `[h0 i a c]`. Then use the resulting hypothesis. Establish `hder : ∀ a b, HasDerivAt (fun t => I i t a b) (∑ k, M i 0 a (Sum.inl k) * w k b) 0`. Introduce `a b`. Establish `h1 : HasDerivAt (fun t => ∑ k, M i t a (Sum.inl k) * (z₀ k b + t * w k b)) (∑ k, (0 * (z₀ k b + 0 * w k b) + M i 0 a (Sum.inl k) * (1 * w k b))) 0` using `HasDerivAt.fun_sum fun k _ => (hM a (Sum.inl k)).mul (((hasDerivAt_id (0 : ℂ)).mul_const (w k b)).const_add (z₀ k b))`. Establish `h2 : HasDerivAt (fun t => ∑ k, M i t a (Sum.inr k) * (1 : Matrix (Fin q) (Fin q) ℂ) k b) (∑ k, 0 * (1 : Matrix (Fin q) (Fin q) ℂ) k b) 0` using `HasDerivAt.fun_sum fun k _ => (hM a (Sum.inr k)).mul_const _`.

Establish `h3` using `h1.add h2`. Simplify using `only [zero_mul, zero_add, one_mul, Finset.sum_const_zero, add_zero] at h3`. Conclude with `h3`. Establish `hw : ∀ a b, ∑ k, M i 0 a (Sum.inl k) * w k b = 0`. Introduce `a b`.

Establish `hev : (fun t => I i t a b) =ᶠ[nhds 0] fun _ => 0` using `by filter_upwards [hBo.mem_nhds h0B] with t ht`. Conclude with `hzero a b ht`. Conclude with `(hder a b).unique ((hasDerivAt_const (0 : ℂ) (0 : ℂ)).congr_of_eventuallyEq hev)`. Establish `hz : ∀ a b, (∑ k, M i 0 a (Sum.inl k) * z₀ k b) + M i 0 a (Sum.inr b) = 0`. Introduce `a b`.

Use `hzero a b h0B` as an intermediate fact. Simplify `this` using `[I, Matrix.one_apply]`. Take `⟨R, hRi⟩` from `hR i`. Set `A : Matrix (Fin p) (Fin p) ℂ` to `Matrix.of fun a k => M i 0 a (Sum.inl k)`. Set `S : Matrix (Fin p) (Fin p) ℂ` to `Matrix.of fun k c => R (Sum.inl k) c - ∑ b, z₀ k b * R (Sum.inr b) c`.

Establish `hAw : A * w = 0`. Use extensionality with `a b`. Rewrite using `[Matrix.mul_apply]`. Conclude with `hw a b`. Establish `hAS : A * S = 1`.

Rewrite using `[← hRi]`. Use extensionality with `a c`. Establish `hb : ∀ b, M i 0 a (Sum.inr b) = -∑ k, M i 0 a (Sum.inl k) * z₀ k b` using `fun b => eq_neg_of_add_eq_zero_right (hz a b)`. Establish `key : ∑ b, (∑ k, M i 0 a (Sum.inl k) * z₀ k b) * R (Sum.inr b) c = ∑ k, M i 0 a (Sum.inl k) * ∑ b, z₀ k b * R (Sum.inr b) c`. Repeatedly rewrite using `[Finset.sum_mul, Finset.mul_sum, mul_assoc]`.

Conclude with `Finset.sum_comm`. Rewrite using `[Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_sum_type]`. Simplify using `only [A, S, Matrix.of_apply, hb, neg_mul, Finset.sum_neg_distrib, key, mul_sub, Finset.sum_sub_distrib]`. Expand and normalize the polynomial expressions, which then agree. Establish `hSA : S * A = 1` using `mul_eq_one_comm.1 hAS`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem eq_zero_of_family_killing_graph (p q : ℕ) (ι : Type) [Countable ι] (r : ℝ) (hr : 0 < r)
    (z₀ w : Matrix (Fin p) (Fin q) ℂ) (M : ι → ℂ → Matrix (Fin p) (Fin p ⊕ Fin q) ℂ)
    (hd : ∀ i a b, DifferentiableOn ℂ (fun t => M i t a b) (Metric.ball 0 r))
    (h0 : ∀ i a b, deriv (fun t => M i t a b) 0 = 0)
    (hk : ∀ t ∈ Metric.ball (0 : ℂ) r, ∃ i,
      M i t * Matrix.fromRows (z₀ + t • w) (1 : Matrix (Fin q) (Fin q) ℂ) = 0)
    (hR : ∀ i, ∃ R : Matrix (Fin p ⊕ Fin q) (Fin p) ℂ, M i 0 * R = 1) : w = 0 := by
  set B := Metric.ball (0 : ℂ) r with hB
  have hBo : IsOpen B := Metric.isOpen_ball
  have h0B : (0 : ℂ) ∈ B := Metric.mem_ball_self hr
  let I : ι → ℂ → Fin p → Fin q → ℂ := fun i t a b =>
    (∑ k, M i t a (Sum.inl k) * (z₀ k b + t * w k b)) +
      ∑ k, M i t a (Sum.inr k) * (1 : Matrix (Fin q) (Fin q) ℂ) k b
  have hI : ∀ i t a b, (M i t * Matrix.fromRows (z₀ + t • w)
      (1 : Matrix (Fin q) (Fin q) ℂ)) a b = I i t a b := by
    intro i t a b
    simp [I, Matrix.mul_apply, Fintype.sum_sum_type]
  have hId : ∀ i a b, DifferentiableOn ℂ (fun t => I i t a b) B := by
    intro i a b
    refine DifferentiableOn.add (DifferentiableOn.fun_sum fun k _ => ?_)
      (DifferentiableOn.fun_sum fun k _ => ?_)
    · exact (hd i a _).mul (by fun_prop)
    · exact (hd i a _).mul (by fun_prop)
  let C : ι → Set ℂ := fun i => {t | t ∈ B → ∀ a b, I i t a b = 0}
  have hC : ∀ i, IsClosed (C i) := by
    intro i
    have hcompl : (C i)ᶜ = ⋃ a, ⋃ b, B ∩ (fun t => I i t a b) ⁻¹' {0}ᶜ := by
      ext t
      simp only [C, Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff,
        Set.mem_preimage, Set.mem_singleton_iff]
      push_neg
      constructor
      · rintro ⟨h1, a, b, h2⟩
        exact ⟨a, b, h1, h2⟩
      · rintro ⟨a, b, h1, h2⟩
        exact ⟨h1, a, b, h2⟩
    rw [← isOpen_compl_iff, hcompl]
    exact isOpen_iUnion fun a => isOpen_iUnion fun b =>
      (hId i a b).continuousOn.isOpen_inter_preimage hBo isOpen_compl_singleton
  have hU : ⋃ i, C i = Set.univ := by
    refine Set.eq_univ_of_forall fun t => ?_
    by_cases ht : t ∈ B
    · obtain ⟨i, hi⟩ := hk t ht
      refine Set.mem_iUnion.2 ⟨i, fun _ a b => ?_⟩
      rw [← hI, hi]
      rfl
    · have hne : Nonempty ι := by
        obtain ⟨i, _⟩ := hk 0 h0B
        exact ⟨i⟩
      obtain ⟨i⟩ := hne
      exact Set.mem_iUnion.2 ⟨i, fun h => absurd h ht⟩
  have hdense := dense_iUnion_interior_of_closed hC hU
  obtain ⟨t₀, ht₀B, ht₀⟩ := hdense.inter_open_nonempty B hBo ⟨0, h0B⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 ht₀
  have hzero : ∀ a b, Set.EqOn (fun t => I i t a b) 0 B := by
    intro a b
    have han : AnalyticOnNhd ℂ (fun t => I i t a b) B := (hId i a b).analyticOnNhd hBo
    refine han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball _ _).isPreconnected ht₀B ?_
    filter_upwards [isOpen_interior.mem_nhds hi, hBo.mem_nhds ht₀B] with t h1 h2
    exact interior_subset h1 h2 a b
  have hM : ∀ a c, HasDerivAt (fun t => M i t a c) 0 0 := by
    intro a c
    have := ((hd i a c).differentiableAt (hBo.mem_nhds h0B)).hasDerivAt
    rwa [h0 i a c] at this
  have hder : ∀ a b, HasDerivAt (fun t => I i t a b) (∑ k, M i 0 a (Sum.inl k) * w k b) 0 := by
    intro a b
    have h1 : HasDerivAt (fun t => ∑ k, M i t a (Sum.inl k) * (z₀ k b + t * w k b))
        (∑ k, (0 * (z₀ k b + 0 * w k b) + M i 0 a (Sum.inl k) * (1 * w k b))) 0 :=
      HasDerivAt.fun_sum fun k _ =>
        (hM a (Sum.inl k)).mul (((hasDerivAt_id (0 : ℂ)).mul_const (w k b)).const_add (z₀ k b))
    have h2 : HasDerivAt (fun t => ∑ k, M i t a (Sum.inr k) * (1 : Matrix (Fin q) (Fin q) ℂ) k b)
        (∑ k, 0 * (1 : Matrix (Fin q) (Fin q) ℂ) k b) 0 :=
      HasDerivAt.fun_sum fun k _ => (hM a (Sum.inr k)).mul_const _
    have h3 := h1.add h2
    simp only [zero_mul, zero_add, one_mul, Finset.sum_const_zero, add_zero] at h3
    exact h3
  have hw : ∀ a b, ∑ k, M i 0 a (Sum.inl k) * w k b = 0 := by
    intro a b
    have hev : (fun t => I i t a b) =ᶠ[nhds 0] fun _ => 0 := by
      filter_upwards [hBo.mem_nhds h0B] with t ht
      exact hzero a b ht
    exact (hder a b).unique ((hasDerivAt_const (0 : ℂ) (0 : ℂ)).congr_of_eventuallyEq hev)
  have hz : ∀ a b, (∑ k, M i 0 a (Sum.inl k) * z₀ k b) + M i 0 a (Sum.inr b) = 0 := by
    intro a b
    have := hzero a b h0B
    simpa [I, Matrix.one_apply] using this
  obtain ⟨R, hRi⟩ := hR i
  let A : Matrix (Fin p) (Fin p) ℂ := Matrix.of fun a k => M i 0 a (Sum.inl k)
  let S : Matrix (Fin p) (Fin p) ℂ := Matrix.of fun k c =>
    R (Sum.inl k) c - ∑ b, z₀ k b * R (Sum.inr b) c
  have hAw : A * w = 0 := by
    ext a b
    rw [Matrix.mul_apply]
    exact hw a b
  have hAS : A * S = 1 := by
    rw [← hRi]
    ext a c
    have hb : ∀ b, M i 0 a (Sum.inr b) = -∑ k, M i 0 a (Sum.inl k) * z₀ k b := fun b =>
      eq_neg_of_add_eq_zero_right (hz a b)
    have key : ∑ b, (∑ k, M i 0 a (Sum.inl k) * z₀ k b) * R (Sum.inr b) c =
        ∑ k, M i 0 a (Sum.inl k) * ∑ b, z₀ k b * R (Sum.inr b) c := by
      simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
      exact Finset.sum_comm
    rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_sum_type]
    simp only [A, S, Matrix.of_apply, hb, neg_mul, Finset.sum_neg_distrib, key, mul_sub,
      Finset.sum_sub_distrib]
    ring
  have hSA : S * A = 1 := mul_eq_one_comm.1 hAS
  calc w = (S * A) * w := by rw [hSA, Matrix.one_mul]
    _ = 0 := by rw [Matrix.mul_assoc, hAw, Matrix.mul_zero]

end GlobalTheory
