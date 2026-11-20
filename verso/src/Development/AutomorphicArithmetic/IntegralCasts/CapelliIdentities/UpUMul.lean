import Mathlib

noncomputable def UpperTheory.Reformulated.B.Qh21.UpU.{u_1} :
    {K : Type u_1} → [Field K] → {N : ℕ} → Matrix (Fin N) (Fin N) K → Prop :=
    fun {K : Type u_1} [Field K] {N : ℕ} (U : Matrix (Fin N) (Fin N) K) ↦
      ∀ (i j : Fin N), (j < i → U i j = (0 : K)) ∧ (i = j → U i j = (1 : K))

/- English proof (translation)
Introduce `K _ N A B hA hB i j`. Establish `hz : j ≤ i → ∀ k : Fin N, k ≠ i → A i k * B k j = 0`. Introduce `hji k hk`. Break down `lt_or_gt_of_ne hk with h | h` into its components or cases. Rewrite using `[(hA i k).1 h, zero_mul]`.

Rewrite using `[(hB k j).1 (lt_of_le_of_lt hji h), mul_zero]`. Establish `hs : j ≤ i → (A * B) i j = B i j`. Introduce `hji`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hk => hz hji k hk) (fun h => absurd (Finset.mem_univ i) h), (hA i i).2 rfl, one_mul]`. Conclude with `⟨fun h => (hs h.le).trans ((hB i j).1 h), fun h => (hs h.ge).trans ((hB i j).2 h)⟩`.
-/
theorem UpperTheory.Reformulated.B.Qh21.upU_mul.{u_1} :
    ∀ {K : Type u_1} [inst : Field K] {N : ℕ} {A B : Matrix (Fin N) (Fin N) K},
      UpperTheory.Reformulated.B.Qh21.UpU A → UpperTheory.Reformulated.B.Qh21.UpU B → UpperTheory.Reformulated.B.Qh21.UpU (A * B) := by
  intro K _ N A B hA hB i j
  have hz : j ≤ i → ∀ k : Fin N, k ≠ i → A i k * B k j = 0 := by
    intro hji k hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [(hA i k).1 h, zero_mul]
    · rw [(hB k j).1 (lt_of_le_of_lt hji h), mul_zero]
  have hs : j ≤ i → (A * B) i j = B i j := by
    intro hji
    rw [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hk => hz hji k hk)
      (fun h => absurd (Finset.mem_univ i) h), (hA i i).2 rfl, one_mul]
  exact ⟨fun h => (hs h.le).trans ((hB i j).1 h), fun h => (hs h.ge).trans ((hB i j).2 h)⟩
