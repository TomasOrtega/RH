import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.RestCountOf

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Finset

/- English proof (translation)
Establish `h1 : (Finset.piAntidiag (Finset.univ : Finset (Fin k)) n).card = ((Finset.univ : Finset (Fin k)).finsuppAntidiag n).card`. Apply the tactic sequence `refine Finset.card_bij' (fun f _ => Finsupp.equivFunOnFinite.symm f) (fun f _ => ⇑f) ?_ ?_ ?_ ?_ <;>`. Simplify using `[Finset.mem_finsuppAntidiag]`. Rewrite using `[h1, Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, Fintype.card_fin]`. Establish `h2 : k + n - 1 = n + (k - 1)` using `by omega`.

Establish `h3 : n + k - 1 = n + (k - 1)` using `by omega`. Rewrite using `[h2, h3]`. Conclude with `Nat.choose_symm_add`.
-/
theorem sum_card_tuples (k n : ℕ) (hk : 0 < k) :
    (Finset.piAntidiag (Finset.univ : Finset (Fin k)) n).card = (n + k - 1).choose (k - 1) := by
  have h1 : (Finset.piAntidiag (Finset.univ : Finset (Fin k)) n).card =
      ((Finset.univ : Finset (Fin k)).finsuppAntidiag n).card := by
    refine Finset.card_bij' (fun f _ => Finsupp.equivFunOnFinite.symm f) (fun f _ => ⇑f) ?_ ?_ ?_ ?_ <;>
      simp [Finset.mem_finsuppAntidiag]
  rw [h1, Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, Fintype.card_fin]
  have h2 : k + n - 1 = n + (k - 1) := by omega
  have h3 : n + k - 1 = n + (k - 1) := by omega
  rw [h2, h3]
  exact Nat.choose_symm_add

/- English proof (translation)
Rewrite using `[← sum_card_tuples k n hk]`. Establish `hdec : ∀ w : Fin k → ℕ, ∑ c, w c = P * ∑ c, w c / P + ∑ c, w c % P`. Introduce `w`. Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun c _ => (Nat.div_add_mod (w c) P).symm`.

Establish `hmaps : ∀ w ∈ Finset.piAntidiag (Finset.univ : Finset (Fin k)) n, (fun c => w c % P) ∈ S`. Introduce `w hw`. Establish `hw' : ∑ c, w c = n` using `by simpa using hw`. Establish `hd` using `hdec w`. Use `hS _ (fun c => Nat.mod_lt _ hP) ?_ ?_` and prove the remaining obligations.

Rewrite using `[← hw', hd]`. Conclude with `Nat.le_add_left _ _`. Rewrite using `[← hw', hd, Nat.mul_add_mod]`. Rewrite using `[Finset.card_eq_sum_card_fiberwise hmaps]`. Use `Finset.sum_le_sum fun v _ => ?_` and prove the remaining obligations.

Rewrite using `[← sum_card_tuples k _ hk]`. Use `Finset.card_le_card_of_injOn (fun w c => w c / P) ?_ ?_` and prove the remaining obligations. Introduce `w hw`. Establish `hw1` using `Finset.mem_filter.mp (Finset.mem_coe.mp hw)`. Establish `hw' : ∑ c, w c = n` using `by simpa using hw1.1`.

Establish `hv : (fun c => w c % P) = v` using `hw1.2`. Establish `hd` using `hdec w`. Establish `hv' : ∑ c, w c % P = ∑ c, v c` using `by rw [← hv]`. Simplify using `only [Finset.mem_coe, Finset.mem_piAntidiag, Finset.mem_univ, implies_true, and_true]`. Rewrite using `[← hw', hd, hv', Nat.add_sub_cancel, Nat.mul_div_cancel_left _ hP]`.

Introduce `w hw w' hw' hww`. Establish `hw1` using `(Finset.mem_filter.mp (Finset.mem_coe.mp hw)).2`. Establish `hw2` using `(Finset.mem_filter.mp (Finset.mem_coe.mp hw')).2`. Use function extensionality and compare the values at `c`. Establish `e1` using `congrFun hww c`.

Establish `e2` using `congrFun (hw1.trans hw2.symm) c`. Simplify using `only at e1 e2`. Rewrite using `[← Nat.div_add_mod (w c) P, ← Nat.div_add_mod (w' c) P, e1, e2]`.
-/
theorem sum_digit_count (k n P : ℕ) (hk : 0 < k) (hP : 0 < P) (S : Finset (Fin k → ℕ))
    (hS : ∀ v : Fin k → ℕ, (∀ c, v c < P) → ∑ c, v c ≤ n → (∑ c, v c) % P = n % P → v ∈ S) :
    (n + k - 1).choose (k - 1) ≤ ∑ v ∈ S, ((n - ∑ c, v c) / P + k - 1).choose (k - 1) := by
  classical
  rw [← sum_card_tuples k n hk]
  have hdec : ∀ w : Fin k → ℕ, ∑ c, w c = P * ∑ c, w c / P + ∑ c, w c % P := by
    intro w
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => (Nat.div_add_mod (w c) P).symm
  have hmaps : ∀ w ∈ Finset.piAntidiag (Finset.univ : Finset (Fin k)) n, (fun c => w c % P) ∈ S := by
    intro w hw
    have hw' : ∑ c, w c = n := by simpa using hw
    have hd := hdec w
    refine hS _ (fun c => Nat.mod_lt _ hP) ?_ ?_
    · rw [← hw', hd]; exact Nat.le_add_left _ _
    · rw [← hw', hd, Nat.mul_add_mod]
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_le_sum fun v _ => ?_
  rw [← sum_card_tuples k _ hk]
  refine Finset.card_le_card_of_injOn (fun w c => w c / P) ?_ ?_
  · intro w hw
    have hw1 := Finset.mem_filter.mp (Finset.mem_coe.mp hw)
    have hw' : ∑ c, w c = n := by simpa using hw1.1
    have hv : (fun c => w c % P) = v := hw1.2
    have hd := hdec w
    have hv' : ∑ c, w c % P = ∑ c, v c := by rw [← hv]
    simp only [Finset.mem_coe, Finset.mem_piAntidiag, Finset.mem_univ, implies_true, and_true]
    rw [← hw', hd, hv', Nat.add_sub_cancel, Nat.mul_div_cancel_left _ hP]
  · intro w hw w' hw' hww
    have hw1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hw)).2
    have hw2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hw')).2
    funext c
    have e1 := congrFun hww c
    have e2 := congrFun (hw1.trans hw2.symm) c
    simp only at e1 e2
    rw [← Nat.div_add_mod (w c) P, ← Nat.div_add_mod (w' c) P, e1, e2]

/- English proof (translation)
Take `⟨m, rfl⟩` from `Nat.exists_eq_succ_of_ne_zero hk.ne'`. Establish `hc : (Finset.univ : Finset (Fin m → Fin P)).card = P ^ (m + 1 - 1)`. Simplify using the standard rewrite rules. Rewrite using `[← hc]`. Set `g : (Fin m → Fin P) → (Fin (m + 1) → ℕ)` to `fun u => Fin.cons ((n + (P - 1) * ∑ i, (u i : ℕ)) % P) (fun i => (u i : ℕ))`.

Use `Finset.card_le_card_of_injOn g ?_ ?_` and prove the remaining obligations. Introduce `u _`. Establish `hlt : ∀ c, g u c < P`. Introduce `c`. Use `Fin.cases ?_ (fun i => ?_) c` and prove the remaining obligations.

Simplify using `only [g, Fin.cons_zero]`. Conclude with `Nat.mod_lt _ hP`. Simplify using `only [g, Fin.cons_succ]`. Conclude with `(u i).isLt`. Use `Finset.mem_coe.mpr (hS _ hlt ?_ ?_)` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Fin.sum_univ_succ]`. Simplify using `only [g, Fin.cons_zero, Fin.cons_succ]`. Use `set s := ∑ i, (u i : ℕ)`. Rewrite using `[Nat.mod_add_mod]`.

Establish `: n + (P - 1) * s + s = n + P * s`. Take `⟨P', rfl⟩` from `Nat.exists_eq_succ_of_ne_zero hP.ne'`. Simplify using `only [Nat.succ_eq_add_one, Nat.add_sub_cancel]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, Nat.add_mul_mod_self_left]`.

Introduce `u _ u' _ huu`. Use function extensionality and compare the values at `i`. Use `congrFun huu i.succ` as an intermediate fact. Simplify using `only [g, Fin.cons_succ] at this`. Conclude with `Fin.ext this`.
-/
theorem sum_label_count (k n P : ℕ) (hk : 0 < k) (hP : 0 < P) (hn : k * P ≤ n) (S : Finset (Fin k → ℕ))
    (hS : ∀ v : Fin k → ℕ, (∀ c, v c < P) → ∑ c, v c ≤ n → (∑ c, v c) % P = n % P → v ∈ S) :
    P ^ (k - 1) ≤ S.card := by
  classical
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  have hc : (Finset.univ : Finset (Fin m → Fin P)).card = P ^ (m + 1 - 1) := by
    simp
  rw [← hc]
  let g : (Fin m → Fin P) → (Fin (m + 1) → ℕ) := fun u =>
    Fin.cons ((n + (P - 1) * ∑ i, (u i : ℕ)) % P) (fun i => (u i : ℕ))
  refine Finset.card_le_card_of_injOn g ?_ ?_
  · intro u _
    have hlt : ∀ c, g u c < P := by
      intro c
      refine Fin.cases ?_ (fun i => ?_) c
      · simp only [g, Fin.cons_zero]; exact Nat.mod_lt _ hP
      · simp only [g, Fin.cons_succ]; exact (u i).isLt
    refine Finset.mem_coe.mpr (hS _ hlt ?_ ?_)
    · calc ∑ c, g u c ≤ ∑ _c : Fin (m + 1), P := Finset.sum_le_sum fun c _ => (hlt c).le
        _ = (m + 1) * P := by simp
        _ ≤ n := hn
    · rw [Fin.sum_univ_succ]
      simp only [g, Fin.cons_zero, Fin.cons_succ]
      set s := ∑ i, (u i : ℕ)
      rw [Nat.mod_add_mod]
      have : n + (P - 1) * s + s = n + P * s := by
        obtain ⟨P', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hP.ne'
        simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
        ring
      rw [this, Nat.add_mul_mod_self_left]
  · intro u _ u' _ huu
    funext i
    have := congrFun huu i.succ
    simp only [g, Fin.cons_succ] at this
    exact Fin.ext this

/- English proof (translation)
Establish `h` using `Nat.ascFactorial_eq_factorial_mul_choose x M`. Rewrite `h` using `[Nat.ascFactorial_eq_prod_range]`. Establish `h' : ((∏ i ∈ Finset.range M, (x + 1 + i) : ℕ) : ℝ) = ((M.factorial * (x + M).choose M : ℕ) : ℝ)`. Rewrite using `[h]`. Move the coercions through the operations in `at h'`.

Rewrite using `[← h']`.
-/
theorem factorial_mul_choose_eq_prod_range (x M : ℕ) :
    ((M.factorial : ℕ) : ℝ) * (((x + M).choose M : ℕ) : ℝ) = ∏ l ∈ Finset.range M, ((x : ℝ) + 1 + l) := by
  have h := Nat.ascFactorial_eq_factorial_mul_choose x M
  rw [Nat.ascFactorial_eq_prod_range] at h
  have h' : ((∏ i ∈ Finset.range M, (x + 1 + i) : ℕ) : ℝ) = ((M.factorial * (x + M).choose M : ℕ) : ℝ) := by
    rw [h]
  push_cast at h'
  rw [← h']

/- English proof (translation)
Establish `hf : (0 : ℝ) < (M.factorial : ℝ)` using `by exact_mod_cast M.factorial_pos`. Establish `hb : 1 - (M : ℝ) * θ ≤ (1 - θ) ^ M`. Use `one_add_mul_le_pow (a := -θ) (by linarith) M` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Establish `hy : (0 : ℝ) ≤ (((y + M).choose M : ℕ) : ℝ)` using `Nat.cast_nonneg _`.

Use `le_trans (mul_le_mul_of_nonneg_left hb hy) ?_` and prove the remaining obligations. Use `le_of_mul_le_mul_left ?_ hf` and prove the remaining obligations. Establish `e1 : (M.factorial : ℝ) * ((((y + M).choose M : ℕ) : ℝ) * (1 - θ) ^ M) = ∏ l ∈ Finset.range M, (((y : ℝ) + 1 + l) * (1 - θ))`. Rewrite using `[← mul_assoc, factorial_mul_choose_eq_prod_range, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]`. Establish `e2 : (M.factorial : ℝ) * (s ^ M * (((x + M).choose M : ℕ) : ℝ)) = ∏ l ∈ Finset.range M, (s * ((x : ℝ) + 1 + l))`.

Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← factorial_mul_choose_eq_prod_range]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, e2]`. Use `Finset.prod_le_prod (fun l _ => ?_) fun l hl => h l (Finset.mem_range.mp hl)` and prove the remaining obligations. Establish `: (0 : ℝ) ≤ (y : ℝ) + 1 + l` using `by positivity`.

Conclude with `mul_nonneg this (by linarith)`.
-/
theorem choose_add_mul_one_sub_le_pow_mul_choose_add (x y M : ℕ) (s θ : ℝ) (h1 : θ ≤ 1)
    (h : ∀ l < M, ((y : ℝ) + 1 + l) * (1 - θ) ≤ s * ((x : ℝ) + 1 + l)) :
    (((y + M).choose M : ℕ) : ℝ) * (1 - M * θ) ≤ s ^ M * (((x + M).choose M : ℕ) : ℝ) := by
  have hf : (0 : ℝ) < (M.factorial : ℝ) := by exact_mod_cast M.factorial_pos
  have hb : 1 - (M : ℝ) * θ ≤ (1 - θ) ^ M := by
    have := one_add_mul_le_pow (a := -θ) (by linarith) M
    calc 1 - (M : ℝ) * θ = 1 + (M : ℝ) * (-θ) := by ring
      _ ≤ (1 + -θ) ^ M := this
      _ = (1 - θ) ^ M := by ring_nf
  have hy : (0 : ℝ) ≤ (((y + M).choose M : ℕ) : ℝ) := Nat.cast_nonneg _
  refine le_trans (mul_le_mul_of_nonneg_left hb hy) ?_
  refine le_of_mul_le_mul_left ?_ hf
  have e1 : (M.factorial : ℝ) * ((((y + M).choose M : ℕ) : ℝ) * (1 - θ) ^ M) =
      ∏ l ∈ Finset.range M, (((y : ℝ) + 1 + l) * (1 - θ)) := by
    rw [← mul_assoc, factorial_mul_choose_eq_prod_range, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have e2 : (M.factorial : ℝ) * (s ^ M * (((x + M).choose M : ℕ) : ℝ)) =
      ∏ l ∈ Finset.range M, (s * ((x : ℝ) + 1 + l)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← factorial_mul_choose_eq_prod_range]
    ring
  rw [e1, e2]
  refine Finset.prod_le_prod (fun l _ => ?_) fun l hl => h l (Finset.mem_range.mp hl)
  have : (0 : ℝ) ≤ (y : ℝ) + 1 + l := by positivity
  exact mul_nonneg this (by linarith)

/- English proof (translation)
Take `⟨J', rfl⟩` from `Nat.exists_eq_succ_of_ne_zero (by omega : J ≠ 0)`. Rewrite using `[Finset.prod_range_succ, Finset.prod_range_succ' (fun j : ℕ => φ (j : ℤ))]`. Establish `h` using `hφ 0`. Move the coercions through the operations in `at h ⊢`. Rewrite `h` using `[zero_add]`.

Rewrite using `[h]`.
-/
theorem prod_range_shift_of_periodic (φ : ℤ → ℝ) (J : ℕ) (hJ : 1 ≤ J) (hφ : ∀ j, φ (j + J) = φ j) :
    ∏ j ∈ Finset.range J, φ ((j : ℤ) + 1) = ∏ j ∈ Finset.range J, φ (j : ℤ) := by
  obtain ⟨J', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : J ≠ 0)
  rw [Finset.prod_range_succ, Finset.prod_range_succ' (fun j : ℕ => φ (j : ℤ))]
  have h := hφ 0
  push_cast at h ⊢
  rw [zero_add] at h
  rw [h]

end Formalism.MainNotions.SelectionLemmas.Pf
