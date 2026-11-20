import Mathlib

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qh58.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

/- English proof (translation)
Introduce `l _ ι n M R hR h`. Establish `hR0 : (0 : ℝ) ≤ R` using `zero_le_one.trans hR`. Rewrite using `[Matrix.det_apply', map_sum]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hR0 n) ?_` and prove the remaining obligations. Introduce `σ _`.

Rewrite using `[map_mul, map_prod, norm_mul, norm_prod, map_intCast]`. Establish `h1 : ‖(((Equiv.Perm.sign σ : ℤˣ) : ℤ) : PadicAlgCl l)‖ = 1`. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]`. Rewrite using `[h1, one_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.Reformulated.B.Qh58.norm_det_le :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (ι : UpperTheory.Reformulated.B.Qh58.Qbar l ≃+* ℂ) {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
      (R : ℝ),
      (1 : ℝ) ≤ R →
        (∀ (i j : Fin n), ‖(ι.symm : ℂ → UpperTheory.Reformulated.B.Qh58.Qbar l) (M i j)‖ ≤ R) →
          ‖(ι.symm : ℂ → UpperTheory.Reformulated.B.Qh58.Qbar l) M.det‖ ≤ R ^ n := by
  intro l _ ι n M R hR h
  have hR0 : (0 : ℝ) ≤ R := zero_le_one.trans hR
  rw [Matrix.det_apply', map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hR0 n) ?_
  intro σ _
  rw [map_mul, map_prod, norm_mul, norm_prod, map_intCast]
  have h1 : ‖(((Equiv.Perm.sign σ : ℤˣ) : ℤ) : PadicAlgCl l)‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]
  rw [h1, one_mul]
  calc ∏ i, ‖ι.symm (M (σ i) i)‖ ≤ ∏ _i : Fin n, R :=
        Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => h _ _)
    _ = R ^ n := by simp
