import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.PartSplitOfOne

noncomputable section

namespace PIW.AdelClassFin

open NumberField

/- English proof (translation)
Introduce `E _ _ k X`. Establish `h : ∀ p : Fin k × Fin k, ∃ D : ℕ, 1 ≤ D ∧ (D : E) * X p.1 p.2 ∈ (algebraMap (𝓞 E) E).range`. Introduce `p`. Take `⟨y, hy, hint⟩` from `IsAlgebraic.exists_integral_multiple (IsFractionRing.isAlgebraic_iff ℤ ℚ E |>.mpr (.of_finite ℚ (X p.1 p.2)))`. Use `⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩` and prove the remaining obligations.

Establish `hmem : (y : E) * X p.1 p.2 ∈ (algebraMap (𝓞 E) E).range` using `⟨⟨(y : E) * X p.1 p.2, by rw [mem_integralClosure_iff]; simpa [zsmul_eq_mul] using hint⟩, rfl⟩`. Establish `h2 : (y.natAbs : ℤ) = y ∨ (y.natAbs : ℤ) = -y`. Break down `Int.natAbs_eq y with h | h` into its components or cases. Conclude with `Or.inl h.symm`. Use `right`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[← Int.cast_natCast]`. Apply the tactic sequence `rcases h2 with h2 | h2 <;> rw [h2]`. Conclude with `hmem`. Rewrite using `[Int.cast_neg, neg_mul]`.

Conclude with `neg_mem hmem`. Use `choose Dp hDp1 hDp using h`. Use `⟨∏ p, Dp p, Finset.one_le_prod' fun p _ => hDp1 p, fun i j => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `Finset.dvd_prod_of_mem Dp (Finset.mem_univ (i, j))`. Rewrite using `[hc, Nat.cast_mul, mul_comm (Dp (i, j) : E), mul_assoc]`.

Conclude with `Subring.mul_mem _ ⟨c, by simp⟩ (hDp (i, j))`.
-/
theorem spDen : SpDen := by
  intro E _ _ k X
  have h : ∀ p : Fin k × Fin k, ∃ D : ℕ, 1 ≤ D ∧ (D : E) * X p.1 p.2 ∈ (algebraMap (𝓞 E) E).range := by
    intro p
    obtain ⟨y, hy, hint⟩ := IsAlgebraic.exists_integral_multiple (IsFractionRing.isAlgebraic_iff ℤ ℚ E |>.mpr (.of_finite ℚ (X p.1 p.2)))
    refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
    have hmem : (y : E) * X p.1 p.2 ∈ (algebraMap (𝓞 E) E).range :=
      ⟨⟨(y : E) * X p.1 p.2, by rw [mem_integralClosure_iff]; simpa [zsmul_eq_mul] using hint⟩, rfl⟩
    have h2 : (y.natAbs : ℤ) = y ∨ (y.natAbs : ℤ) = -y := by
      rcases Int.natAbs_eq y with h | h
      · exact Or.inl h.symm
      · right; linarith
    rw [← Int.cast_natCast]
    rcases h2 with h2 | h2 <;> rw [h2]
    · exact hmem
    · rw [Int.cast_neg, neg_mul]; exact neg_mem hmem
  choose Dp hDp1 hDp using h
  refine ⟨∏ p, Dp p, Finset.one_le_prod' fun p _ => hDp1 p, fun i j => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem Dp (Finset.mem_univ (i, j))
  rw [hc, Nat.cast_mul, mul_comm (Dp (i, j) : E), mul_assoc]
  exact Subring.mul_mem _ ⟨c, by simp⟩ (hDp (i, j))

end PIW.AdelClassFin
