import Mathlib

/- English proof (translation)
Introduce `Γ W _ _ U f h`. Establish `h1 : f 1 = 0`. Establish `h11` using `h 1 U.one_mem 1 U.one_mem`. Rewrite `h11` using `[one_mul]`. Conclude with `left_eq_add.mp h11`.

Use `⟨h1, fun u hu k => ?_⟩` and prove the remaining obligations. Proceed by induction on `k with`. Consider the case `zero => rw [pow_zero, zero_nsmul, h1]`. Consider the case `succ k ih => rw [pow_succ, h _ (U.pow_mem hu k) u hu, ih, succ_nsmul]`.
-/
theorem UpperTheory.Reformulated.B.Qf49.add_pow_nsmul :
    ∀ {Γ W : Type} [inst : Group Γ] [inst_1 : AddCommGroup W]
    (U : Subgroup Γ) (f : Γ → W),
    (∀ u ∈ U, ∀ v ∈ U, f (u * v) = f u + f v) → f (1 : Γ) = (0 : W) ∧ ∀ u ∈ U, ∀ (k : ℕ), f (u ^ k) = k • f u := by
  intro Γ W _ _ U f h
  have h1 : f 1 = 0 := by
    have h11 := h 1 U.one_mem 1 U.one_mem
    rw [one_mul] at h11
    exact left_eq_add.mp h11
  refine ⟨h1, fun u hu k => ?_⟩
  induction k with
  | zero => rw [pow_zero, zero_nsmul, h1]
  | succ k ih => rw [pow_succ, h _ (U.pow_mem hu k) u hu, ih, succ_nsmul]
