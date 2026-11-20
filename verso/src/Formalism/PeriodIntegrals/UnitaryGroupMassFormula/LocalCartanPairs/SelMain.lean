import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.SelCore

noncomputable section
open Matrix

namespace PI.SqPair.LCP

variable {R : Type} [CommRing R] [IsDomain R]

/- English proof (translation)
Establish `hc : ∀ n : ℕ, ϖ ^ n ≠ 0` using `fun n => pow_ne_zero n hϖ0`. Establish `hh : h ≠ 0`. Introduce and unpack `rfl`. Establish `h0 : ϖ ^ (2 * k) • A' = 0` using `by rw [← hrel]; simp`. Break down `smul_eq_zero.1 h0 with h2 | h2` into its components or cases.

Conclude with `hc _ h2`. Rewrite `hA'` using `[h2, Matrix.det_zero]`. Conclude with `not_isUnit_zero hA'`. Take `⟨m, h₁, i, j, rfl, hu⟩` from `sel_factor ϖ hϖ0 hval h hh`. Take `⟨hmk, hrel₁⟩` from `sel_le σ ϖ hϖ0 hϖ hσϖ A A' h₁ hA' m k hrel`.

Use `⟨m, h₁, rfl, hmk, hrel₁, ?_⟩` and prove the remaining obligations. Break down `Nat.lt_or_ge m k with hlt | hge` into its components or cases. Use `right`. Use `⟨hlt, ?_⟩` and prove the remaining obligations. Take `⟨hg1, hg2⟩` from `sel_inv σ A A' h₁ hA' (hc _) hrel₁`.

Establish `hxi : IsUnit ((h₁ *ᵥ Pi.single j 1) i)` using `by simpa [Matrix.mulVec_single] using hu`. Take `⟨y, hy⟩` from `sel_dual σ A hA (h₁ *ᵥ Pi.single j 1) i hxi`. Use `⟨A'⁻¹ * (h₁.map σ)ᵀ * A, j, y, hg1, hg2, ⟨i, hxi⟩, hy, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[sel_form σ A h₁ (Pi.single j 1) (Pi.single j 1), hrel₁]`. Establish `hs : (fun l : ι => σ ((Pi.single j (1 : R) : ι → R) l)) = (Pi.single j 1 : ι → R)`.

Use function extensionality and compare the values at `l`. Distinguish the cases in `hl : l = j`. Substitute `hl` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hl]`.

Rewrite using `[hs]`. Simplify using `[Matrix.mulVec_single, dotProduct, Pi.single_apply]`. Rewrite using `[Matrix.mulVec_mulVec, hg2, Matrix.smul_mulVec, Matrix.one_mulVec]`. Use `left`. Establish `hm : m = k` using `le_antisymm hmk hge`.

Substitute `hm` using the available equality. Use `⟨rfl, ?_⟩` and prove the remaining obligations. Rewrite `hrel₁` using `[Nat.sub_self, mul_zero, pow_zero, one_smul]`. Conclude with `sel_unit_of_rel σ A A' h₁ hA' hrel₁`.
-/
theorem sel_main (σ : R ≃+* R) (ϖ : R) (hϖ0 : ϖ ≠ 0) (hϖ : ¬ IsUnit ϖ) (hσϖ : σ ϖ = ϖ)
    (hval : ∀ x : R, x ≠ 0 → ∃ n : ℕ, ∃ u : R, IsUnit u ∧ x = ϖ ^ n * u)
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A A' h : Matrix ι ι R) (hA : IsUnit A.det) (hA' : IsUnit A'.det) (k : ℕ)
    (hrel : (h.map σ)ᵀ * A * h = ϖ ^ (2 * k) • A') :
    ∃ (m : ℕ) (h₁ : Matrix ι ι R), h = ϖ ^ m • h₁ ∧ m ≤ k ∧
      (h₁.map σ)ᵀ * A * h₁ = ϖ ^ (2 * (k - m)) • A' ∧
      ((m = k ∧ IsUnit h₁.det) ∨
       (m < k ∧ ∃ (g₁ : Matrix ι ι R) (j : ι) (y : ι → R),
          g₁ * h₁ = ϖ ^ (2 * (k - m)) • 1 ∧ h₁ * g₁ = ϖ ^ (2 * (k - m)) • 1 ∧
          (∃ i, IsUnit ((h₁ *ᵥ Pi.single j 1) i)) ∧
          (fun l => σ ((h₁ *ᵥ Pi.single j 1) l)) ⬝ᵥ (A *ᵥ y) = 1 ∧
          (fun l => σ ((h₁ *ᵥ Pi.single j 1) l)) ⬝ᵥ (A *ᵥ (h₁ *ᵥ Pi.single j 1)) =
            ϖ ^ (2 * (k - m)) * A' j j ∧
          ϖ ^ (2 * (k - m)) • y = h₁ *ᵥ (g₁ *ᵥ y))) := by
  have hc : ∀ n : ℕ, ϖ ^ n ≠ 0 := fun n => pow_ne_zero n hϖ0
  have hh : h ≠ 0 := by
    rintro rfl
    have h0 : ϖ ^ (2 * k) • A' = 0 := by rw [← hrel]; simp
    rcases smul_eq_zero.1 h0 with h2 | h2
    · exact hc _ h2
    · rw [h2, Matrix.det_zero] at hA'
      exact not_isUnit_zero hA'
  obtain ⟨m, h₁, i, j, rfl, hu⟩ := sel_factor ϖ hϖ0 hval h hh
  obtain ⟨hmk, hrel₁⟩ := sel_le σ ϖ hϖ0 hϖ hσϖ A A' h₁ hA' m k hrel
  refine ⟨m, h₁, rfl, hmk, hrel₁, ?_⟩
  rcases Nat.lt_or_ge m k with hlt | hge
  · right
    refine ⟨hlt, ?_⟩
    obtain ⟨hg1, hg2⟩ := sel_inv σ A A' h₁ hA' (hc _) hrel₁
    have hxi : IsUnit ((h₁ *ᵥ Pi.single j 1) i) := by simpa [Matrix.mulVec_single] using hu
    obtain ⟨y, hy⟩ := sel_dual σ A hA (h₁ *ᵥ Pi.single j 1) i hxi
    refine ⟨A'⁻¹ * (h₁.map σ)ᵀ * A, j, y, hg1, hg2, ⟨i, hxi⟩, hy, ?_, ?_⟩
    · rw [sel_form σ A h₁ (Pi.single j 1) (Pi.single j 1), hrel₁]
      have hs : (fun l : ι => σ ((Pi.single j (1 : R) : ι → R) l)) = (Pi.single j 1 : ι → R) := by
        funext l
        by_cases hl : l = j
        · subst hl
          simp
        · simp [Pi.single_apply, hl]
      rw [hs]
      simp [Matrix.mulVec_single, dotProduct, Pi.single_apply]
    · rw [Matrix.mulVec_mulVec, hg2, Matrix.smul_mulVec, Matrix.one_mulVec]
  · left
    have hm : m = k := le_antisymm hmk hge
    subst hm
    refine ⟨rfl, ?_⟩
    rw [Nat.sub_self, mul_zero, pow_zero, one_smul] at hrel₁
    exact sel_unit_of_rel σ A A' h₁ hA' hrel₁

end PI.SqPair.LCP
