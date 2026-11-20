import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsCongIdealTwoTorsion

open CompanionTheory.Rg.FlB

namespace GlobalTheory.CompanionTheory.Iwahori.TorusConj

/- English proof (translation)
Establish `e1 : S * a * S' - 1 = ∑ i, ∑ j, P i * (S * (a - 1) * S') * P j`. Repeatedly rewrite using `[← Finset.mul_sum, ← Finset.sum_mul]`. Rewrite using `[hP.sum]`. Simplify using `[mul_sub, sub_mul, hSS]`. Rewrite using `[e1]`.

Use `sum_mem fun i _ => sum_mem fun j _ => ?_` and prove the remaining obligations. Establish `e2 : P i * (S * (a - 1) * S') * P j = (σ i * ρ j) • (P i * (a - 1) * P j)`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`. Use `_ = (σ i * ρ j) • (P i * (a - 1) * P j) := by`.

Rewrite using `[hS, hS']`. Simplify using `only [smul_mul_assoc, mul_smul_comm, smul_smul]`. Rewrite using `[mul_comm]`. Rewrite using `[e2]`. Break down `h i j with hn | ⟨hij, hz⟩` into its components or cases.

Conclude with `hc _ hn _ (hJ.right_mem j _ (hJ.left_mem i _ ha))`. Establish `: P i * (a - 1) * P j = 0`. Rewrite using `[mul_sub, sub_mul, hz, mul_one, hP.orth i j hij, sub_zero]`. Rewrite using `[this, smul_zero]`. Conclude with `J.zero_mem`.
-/
theorem conj_sub_one_mem {L E ι : Type} [NormedField L] [Ring E] [Algebra L E] [Fintype ι]
    {P : ι → E} (hP : GlobalTheory.CompanionTheory.Iwahori.IsPieces P) {J : AddSubgroup E}
    (hJ : GlobalTheory.CompanionTheory.Iwahori.IsCongIdeal J P)
    (hc : ∀ c : L, ‖c‖ ≤ 1 → ∀ x ∈ J, c • x ∈ J)
    {S S' : E} {σ ρ : ι → L} (hS : ∀ i, P i * S = σ i • P i)
    (hS' : ∀ j, S' * P j = ρ j • P j) (hSS : S * S' = 1) {a : E} (ha : a - 1 ∈ J)
    (h : ∀ i j, ‖σ i * ρ j‖ ≤ 1 ∨ (i ≠ j ∧ P i * a * P j = 0)) :
    S * a * S' - 1 ∈ J := by
  have e1 : S * a * S' - 1 = ∑ i, ∑ j, P i * (S * (a - 1) * S') * P j := by
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    rw [hP.sum]
    simp [mul_sub, sub_mul, hSS]
  rw [e1]
  refine sum_mem fun i _ => sum_mem fun j _ => ?_
  have e2 : P i * (S * (a - 1) * S') * P j = (σ i * ρ j) • (P i * (a - 1) * P j) := by
    calc P i * (S * (a - 1) * S') * P j = (P i * S) * (a - 1) * (S' * P j) := by
          simp only [mul_assoc]
      _ = (σ i * ρ j) • (P i * (a - 1) * P j) := by
          rw [hS, hS']
          simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
          rw [mul_comm]
  rw [e2]
  rcases h i j with hn | ⟨hij, hz⟩
  · exact hc _ hn _ (hJ.right_mem j _ (hJ.left_mem i _ ha))
  · have : P i * (a - 1) * P j = 0 := by
      rw [mul_sub, sub_mul, hz, mul_one, hP.orth i j hij, sub_zero]
    rw [this, smul_zero]
    exact J.zero_mem

/- English proof (translation)
Establish `hl' : ∀ j, T' * P j = (τ j)⁻¹ • P j`. Introduce `j`. Establish `e : T' * (T * P j) = T' * (τ j • P j)` using `by rw [hl]`. Rewrite `e` using `[← mul_assoc, hTT', one_mul, mul_smul_comm]`. Rewrite using `[eq_inv_smul_iff₀ (hτ j)]`.

Conclude with `e.symm`. Establish `hr' : ∀ j, P j * T' = (τ j)⁻¹ • P j`. Introduce `j`. Establish `e : (P j * T) * T' = (τ j • P j) * T'` using `by rw [hr]`. Rewrite `e` using `[mul_assoc, hTT, mul_one, smul_mul_assoc]`.

Rewrite using `[eq_inv_smul_iff₀ (hτ j)]`. Conclude with `e.symm`. Prove the components needed by the constructor for the conclusion. Use `conj_sub_one_mem hP hJ hc hr hl' hTT ha fun i j => ?_` and prove the remaining obligations. Distinguish the cases in `hij : wt j < wt i`.

Conclude with `Or.inr ⟨fun e => by subst e; exact lt_irrefl _ hij, hU i j hij⟩`. Use `left`. Establish `hn` using `hw i j (not_lt.mp hij)`. Establish `hpos : 0 < ‖τ j‖` using `norm_pos_iff.mpr (hτ j)`. Rewrite using `[norm_mul, norm_inv, ← div_eq_mul_inv]`.

Conclude with `(div_le_one hpos).mpr hn`. Use `conj_sub_one_mem hP hJ hc hr' hl hTT' hb fun i j => ?_` and prove the remaining obligations. Distinguish the cases in `hij : wt i < wt j`. Conclude with `Or.inr ⟨fun e => by subst e; exact lt_irrefl _ hij, hL i j hij⟩`. Use `left`.

Establish `hn` using `hw j i (not_lt.mp hij)`. Establish `hpos : 0 < ‖τ i‖` using `norm_pos_iff.mpr (hτ i)`. Rewrite using `[norm_mul, norm_inv, inv_mul_eq_div]`. Conclude with `(div_le_one hpos).mpr hn`.
-/
theorem conj_congruence {L E ι : Type} [NormedField L] [Ring E] [Algebra L E] [Fintype ι]
    (wt : ι → ℕ) (P : ι → E) (hP : GlobalTheory.CompanionTheory.Iwahori.IsPieces P) (J : AddSubgroup E)
    (hJ : GlobalTheory.CompanionTheory.Iwahori.IsCongIdeal J P)
    (hc : ∀ c : L, ‖c‖ ≤ 1 → ∀ x ∈ J, c • x ∈ J) (T T' : E) (τ : ι → L)
    (hτ : ∀ i, τ i ≠ 0) (hTT : T * T' = 1) (hTT' : T' * T = 1)
    (hl : ∀ i, T * P i = τ i • P i) (hr : ∀ i, P i * T = τ i • P i)
    (hw : ∀ i j, wt i ≤ wt j → ‖τ i‖ ≤ ‖τ j‖) (a b : E) (ha : a - 1 ∈ J) (hb : b - 1 ∈ J)
    (hU : GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a) (hL : GlobalTheory.CompanionTheory.Iwahori.IsLower wt P b) :
    T * a * T' - 1 ∈ J ∧ T' * b * T - 1 ∈ J := by
  have hl' : ∀ j, T' * P j = (τ j)⁻¹ • P j := by
    intro j
    have e : T' * (T * P j) = T' * (τ j • P j) := by rw [hl]
    rw [← mul_assoc, hTT', one_mul, mul_smul_comm] at e
    rw [eq_inv_smul_iff₀ (hτ j)]
    exact e.symm
  have hr' : ∀ j, P j * T' = (τ j)⁻¹ • P j := by
    intro j
    have e : (P j * T) * T' = (τ j • P j) * T' := by rw [hr]
    rw [mul_assoc, hTT, mul_one, smul_mul_assoc] at e
    rw [eq_inv_smul_iff₀ (hτ j)]
    exact e.symm
  constructor
  · refine conj_sub_one_mem hP hJ hc hr hl' hTT ha fun i j => ?_
    by_cases hij : wt j < wt i
    · exact Or.inr ⟨fun e => by subst e; exact lt_irrefl _ hij, hU i j hij⟩
    · left
      have hn := hw i j (not_lt.mp hij)
      have hpos : 0 < ‖τ j‖ := norm_pos_iff.mpr (hτ j)
      rw [norm_mul, norm_inv, ← div_eq_mul_inv]
      exact (div_le_one hpos).mpr hn
  · refine conj_sub_one_mem hP hJ hc hr' hl hTT' hb fun i j => ?_
    by_cases hij : wt i < wt j
    · exact Or.inr ⟨fun e => by subst e; exact lt_irrefl _ hij, hL i j hij⟩
    · left
      have hn := hw j i (not_lt.mp hij)
      have hpos : 0 < ‖τ i‖ := norm_pos_iff.mpr (hτ i)
      rw [norm_mul, norm_inv, inv_mul_eq_div]
      exact (div_le_one hpos).mpr hn

end GlobalTheory.CompanionTheory.Iwahori.TorusConj
