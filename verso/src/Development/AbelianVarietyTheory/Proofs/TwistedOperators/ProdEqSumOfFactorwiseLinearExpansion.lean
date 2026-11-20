import Mathlib

namespace GlobalTheory

open Finset in

/- English proof (translation)
Introduce `K _ X I S x a b A B h1 h2 h3 hne`. Establish `key : ∀ T : Finset K, ∀ q : ∀ n, X n, ∑ i ∈ S, x i * ∏ n, (if n ∈ T then b n i else a n i (q n)) = ∏ n, (if n ∈ T then B n else A n (q n))`. Introduce `T`. Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => intro q`.

Simplify using `using (h3 q).symm`. Consider the case `insert m T hm ih`. Introduce `q`. Take `⟨c, hc⟩ : ∃ c, c = ∏ n ∈ univ.erase m, (if n ∈ T then B n else A n (q n))` from `⟨_, rfl⟩`. Take `⟨y, hy⟩ : ∃ y : I → ℂ, y = fun i => x i * ∏ n ∈ univ.erase m, (if n ∈ T then b n i else a n i (q n))` from `⟨_, rfl⟩`.

Establish `hL : ∀ t, ∑ i ∈ S, y i * a m i t = A m t * c`. Introduce `t`. Establish `h` using `ih (Function.update q m t)`. Establish `e1 : ∀ i, ∏ n, (if n ∈ T then b n i else a n i (Function.update q m t n)) = a m i t * ∏ n ∈ univ.erase m, (if n ∈ T then b n i else a n i (q n))`. Introduce `i`.

Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ m)]`. Use `congr 1`. Simplify using `[hm]`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `n hn`.

Establish `hnm : n ≠ m` using `Finset.ne_of_mem_erase hn`. Rewrite using `[Function.update_of_ne hnm]`. Establish `e2 : ∏ n, (if n ∈ T then B n else A n (Function.update q m t n)) = A m t * c`. Rewrite using `[hc, ← Finset.mul_prod_erase _ _ (Finset.mem_univ m)]`. Use `congr 1`.

Simplify using `[hm]`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `n hn`. Establish `hnm : n ≠ m` using `Finset.ne_of_mem_erase hn`. Rewrite using `[Function.update_of_ne hnm]`.

Rewrite `h` using `[e2]`. Simplify using `only [e1] at h`. Rewrite using `[← h, hy]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`.

Expand and normalize the polynomial expressions, which then agree. Establish `e3 : ∀ i, ∏ n, (if n ∈ insert m T then b n i else a n i (q n)) = b m i * ∏ n ∈ univ.erase m, (if n ∈ T then b n i else a n i (q n))`. Introduce `i`. Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ m)]`. Use `congr 1`.

Simplify using the standard rewrite rules. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `n hn`. Establish `hnm : n ≠ m` using `Finset.ne_of_mem_erase hn`. Simplify using `[Finset.mem_insert, hnm]`.

Establish `e4 : ∏ n, (if n ∈ insert m T then B n else A n (q n)) = B m * c`. Rewrite using `[hc, ← Finset.mul_prod_erase _ _ (Finset.mem_univ m)]`. Use `congr 1`. Simplify using the standard rewrite rules. Apply `Finset.prod_congr rfl` to reduce the goal to its premises.

Introduce `n hn`. Establish `hnm : n ≠ m` using `Finset.ne_of_mem_erase hn`. Simplify using `[Finset.mem_insert, hnm]`. Rewrite using `[e4]`. Simplify using `only [e3]`.

Establish `hs : ∑ i ∈ S, x i * (b m i * ∏ n ∈ univ.erase m, (if n ∈ T then b n i else a n i (q n))) = ∑ i ∈ S, y i * b m i`. Rewrite using `[hy]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hs]`. Distinguish the cases in `hc0 : c = 0`. Rewrite using `[hc0, mul_zero]`. Apply `h1 m y` to reduce the goal to its premises. Introduce `t`.

Rewrite using `[hL t, hc0, mul_zero]`. Establish `hB` using `h2 m (fun i => y i / c) (by`. Introduce `t`. Establish `: ∑ i ∈ S, y i / c * a m i t = (∑ i ∈ S, y i * a m i t) / c`. Rewrite using `[Finset.sum_div]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, hL t, mul_div_cancel_right₀ _ hc0])`. Rewrite using `[hB, Finset.sum_mul]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`. Clear the denominators using the available nonvanishing facts. Take `⟨q⟩ : Nonempty (∀ n, X n)` from `⟨fun n => Classical.choice (hne n)⟩`. Simplify using `using (key Finset.univ q).symm`.
-/
theorem prod_eq_sum_of_factorwise_expansion : ∀ (K : Type) [Fintype K] (X : K → Type) (I : Type) (S : Finset I) (x : I → ℂ) (a : ∀ n, I → X n → ℂ) (b : K → I → ℂ) (A : ∀ n, X n → ℂ) (B : K → ℂ), (∀ n (y : I → ℂ), (∀ q, ∑ i ∈ S, y i * a n i q = 0) → ∑ i ∈ S, y i * b n i = 0) → (∀ n (y : I → ℂ), (∀ q, A n q = ∑ i ∈ S, y i * a n i q) → B n = ∑ i ∈ S, y i * b n i) → (∀ q : ∀ n, X n, ∏ n, A n (q n) = ∑ i ∈ S, x i * ∏ n, a n i (q n)) → (∀ n, Nonempty (X n)) → ∏ n, B n = ∑ i ∈ S, x i * ∏ n, b n i := by
  intro K _ X I S x a b A B h1 h2 h3 hne
  classical
  have key : ∀ T : Finset K, ∀ q : ∀ n, X n,
      ∑ i ∈ S, x i * ∏ n, (if n ∈ T then b n i else a n i (q n)) =
        ∏ n, (if n ∈ T then B n else A n (q n)) := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro q; simpa using (h3 q).symm
    | insert m T hm ih =>
      intro q
      obtain ⟨c, hc⟩ : ∃ c, c = ∏ n ∈ univ.erase m, (if n ∈ T then B n else A n (q n)) := ⟨_, rfl⟩
      obtain ⟨y, hy⟩ : ∃ y : I → ℂ, y = fun i => x i * ∏ n ∈ univ.erase m,
          (if n ∈ T then b n i else a n i (q n)) := ⟨_, rfl⟩
      have hL : ∀ t, ∑ i ∈ S, y i * a m i t = A m t * c := by
        intro t
        have h := ih (Function.update q m t)
        have e1 : ∀ i, ∏ n, (if n ∈ T then b n i else a n i (Function.update q m t n)) =
            a m i t * ∏ n ∈ univ.erase m, (if n ∈ T then b n i else a n i (q n)) := by
          intro i
          rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ m)]
          congr 1
          · simp [hm]
          · apply Finset.prod_congr rfl
            intro n hn
            have hnm : n ≠ m := Finset.ne_of_mem_erase hn
            rw [Function.update_of_ne hnm]
        have e2 : ∏ n, (if n ∈ T then B n else A n (Function.update q m t n)) = A m t * c := by
          rw [hc, ← Finset.mul_prod_erase _ _ (Finset.mem_univ m)]
          congr 1
          · simp [hm]
          · apply Finset.prod_congr rfl
            intro n hn
            have hnm : n ≠ m := Finset.ne_of_mem_erase hn
            rw [Function.update_of_ne hnm]
        rw [e2] at h
        simp only [e1] at h
        rw [← h, hy]
        apply Finset.sum_congr rfl
        intro i _
        ring
      have e3 : ∀ i, ∏ n, (if n ∈ insert m T then b n i else a n i (q n)) =
          b m i * ∏ n ∈ univ.erase m, (if n ∈ T then b n i else a n i (q n)) := by
        intro i
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ m)]
        congr 1
        · simp
        · apply Finset.prod_congr rfl
          intro n hn
          have hnm : n ≠ m := Finset.ne_of_mem_erase hn
          simp [Finset.mem_insert, hnm]
      have e4 : ∏ n, (if n ∈ insert m T then B n else A n (q n)) = B m * c := by
        rw [hc, ← Finset.mul_prod_erase _ _ (Finset.mem_univ m)]
        congr 1
        · simp
        · apply Finset.prod_congr rfl
          intro n hn
          have hnm : n ≠ m := Finset.ne_of_mem_erase hn
          simp [Finset.mem_insert, hnm]
      rw [e4]
      simp only [e3]
      have hs : ∑ i ∈ S, x i * (b m i * ∏ n ∈ univ.erase m, (if n ∈ T then b n i else a n i (q n))) =
          ∑ i ∈ S, y i * b m i := by
        rw [hy]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hs]
      by_cases hc0 : c = 0
      · rw [hc0, mul_zero]
        apply h1 m y
        intro t
        rw [hL t, hc0, mul_zero]
      · have hB := h2 m (fun i => y i / c) (by
          intro t
          have : ∑ i ∈ S, y i / c * a m i t = (∑ i ∈ S, y i * a m i t) / c := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro i _
            ring
          rw [this, hL t, mul_div_cancel_right₀ _ hc0])
        rw [hB, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        field_simp
  obtain ⟨q⟩ : Nonempty (∀ n, X n) := ⟨fun n => Classical.choice (hne n)⟩
  simpa using (key Finset.univ q).symm

end GlobalTheory
