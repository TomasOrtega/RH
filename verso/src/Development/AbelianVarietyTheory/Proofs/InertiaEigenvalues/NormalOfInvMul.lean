import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowTEqRowS
open GlobalTheory.PMonE

namespace GlobalTheory.PMonE

open Finset

/- English proof (translation)
Rewrite using `[Matrix.det_apply']`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_prod]`. Establish `hs : ‖((Equiv.Perm.sign σ : ℤ) : F)‖ = 1`. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]`.

Rewrite using `[hs, one_mul]`. Conclude with `Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => hA _ _)`.
-/
theorem norm_det_le_one_of_entries {F : Type} [NormedField F] [IsUltrametricDist F] {m : Type} [Fintype m]
    [DecidableEq m] (A : Matrix m m F) (hA : ∀ i j, ‖A i j‖ ≤ 1) : ‖A.det‖ ≤ 1 := by
  rw [Matrix.det_apply']
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  rw [norm_mul, norm_prod]
  have hs : ‖((Equiv.Perm.sign σ : ℤ) : F)‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [hs, one_mul]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => hA _ _)

/- English proof (translation)
Rewrite using `[Matrix.adjugate_apply]`. Use `norm_det_le_one_of_entries _ fun a b => ?_` and prove the remaining obligations. Distinguish the cases in `h : a = j`. Substitute `h` using the available equality. Rewrite using `[Matrix.updateRow_self]`.

Distinguish the cases in `hb : b = i`. Substitute `hb` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hb]`. Rewrite using `[Matrix.updateRow_ne h]`.

Conclude with `hA a b`.
-/
theorem norm_adjugate_le_one {F : Type} [NormedField F] [IsUltrametricDist F] {m : Type} [Fintype m]
    [DecidableEq m] (A : Matrix m m F) (hA : ∀ i j, ‖A i j‖ ≤ 1) (i j : m) : ‖A.adjugate i j‖ ≤ 1 := by
  rw [Matrix.adjugate_apply]
  refine norm_det_le_one_of_entries _ fun a b => ?_
  by_cases h : a = j
  · subst h
    rw [Matrix.updateRow_self]
    by_cases hb : b = i
    · subst hb; simp
    · simp [Pi.single_apply, hb]
  · rw [Matrix.updateRow_ne h]; exact hA a b

/- English proof (translation)
Rewrite using `[Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv, hd, inv_one, one_mul]`. Conclude with `norm_adjugate_le_one A hA i j`.
-/
theorem norm_inv_le_one_of_det {F : Type} [NormedField F] [IsUltrametricDist F] {m : Type} [Fintype m]
    [DecidableEq m] (A : Matrix m m F) (hA : ∀ i j, ‖A i j‖ ≤ 1) (hd : ‖A.det‖ = 1) (i j : m) :
    ‖A⁻¹ i j‖ ≤ 1 := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv, hd, inv_one, one_mul]
  exact norm_adjugate_le_one A hA i j

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ (hA i k) (norm_nonneg _) (hB k j)`.
-/
theorem norm_mul_apply_le_one {F : Type} [NormedField F] [IsUltrametricDist F] {m : Type} [Fintype m]
    (A B : Matrix m m F) (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ i j, ‖B i j‖ ≤ 1) (i j : m) :
    ‖(A * B) i j‖ ≤ 1 := by
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hA i k) (norm_nonneg _) (hB k j)

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Break down `isEmpty_or_nonempty m with hm | hm` into its components or cases. Simplify using the standard rewrite rules. Take `⟨k₀, -, hk₀⟩` from `Finset.exists_max_image (univ : Finset m) (fun k => ‖A i k * B k j‖) univ_nonempty`. Establish `hlt : ‖A i k₀ * B k₀ j‖ < 1`.

Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `lt_of_le_of_lt (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun k hk => hk₀ k hk) hlt`.
-/
theorem norm_mul_apply_lt_one {F : Type} [NormedField F] [IsUltrametricDist F] {m : Type} [Fintype m]
    (A B : Matrix m m F) (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ i j, ‖B i j‖ < 1) (i j : m) :
    ‖(A * B) i j‖ < 1 := by
  rw [Matrix.mul_apply]
  rcases isEmpty_or_nonempty m with hm | hm
  · simp
  obtain ⟨k₀, -, hk₀⟩ := Finset.exists_max_image (univ : Finset m) (fun k => ‖A i k * B k j‖) univ_nonempty
  have hlt : ‖A i k₀ * B k₀ j‖ < 1 := by
    rw [norm_mul]
    calc ‖A i k₀‖ * ‖B k₀ j‖ ≤ 1 * ‖B k₀ j‖ := mul_le_mul_of_nonneg_right (hA i k₀) (norm_nonneg _)
      _ = ‖B k₀ j‖ := one_mul _
      _ < 1 := hB k₀ j
  exact lt_of_le_of_lt
    (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun k hk => hk₀ k hk) hlt

/- English proof (translation)
Introduce `F _ _ m _ _ N B hint hsmall hd`. Establish `hinv : ∀ i j, ‖(B N)⁻¹ i j‖ ≤ 1` using `norm_inv_le_one_of_det (B N) (hint N) hd`. Establish `hunit : IsUnit (B N).det`. Rewrite using `[isUnit_iff_ne_zero]`. Introduce `h0`.

Rewrite `hd` using `[h0, norm_zero]`. Conclude with `zero_ne_one hd`. Use `⟨⟨fun n i j => norm_mul_apply_le_one _ _ hinv (hint n) i j, ?_, fun n hn i j => norm_mul_apply_lt_one _ _ hinv (hsmall n hn) i j⟩, hinv⟩` and prove the remaining obligations. Conclude with `Matrix.nonsing_inv_mul _ hunit`.
-/
theorem normal_of_inv_mul : ∀ (F : Type) [NormedField F] [IsUltrametricDist F] (m : Type) [Fintype m]
    [DecidableEq m] (N : ℕ) (B : ℕ → Matrix m m F), (∀ n i j, ‖B n i j‖ ≤ 1) →
    (∀ n, N < n → ∀ i j, ‖B n i j‖ < 1) → ‖(B N).det‖ = 1 →
    Normal N (fun n => (B N)⁻¹ * B n) ∧ ∀ i j, ‖(B N)⁻¹ i j‖ ≤ 1 := by
  intro F _ _ m _ _ N B hint hsmall hd
  have hinv : ∀ i j, ‖(B N)⁻¹ i j‖ ≤ 1 := norm_inv_le_one_of_det (B N) (hint N) hd
  have hunit : IsUnit (B N).det := by
    rw [isUnit_iff_ne_zero]; intro h0; rw [h0, norm_zero] at hd; exact zero_ne_one hd
  refine ⟨⟨fun n i j => norm_mul_apply_le_one _ _ hinv (hint n) i j, ?_,
    fun n hn i j => norm_mul_apply_lt_one _ _ hinv (hsmall n hn) i j⟩, hinv⟩
  exact Matrix.nonsing_inv_mul _ hunit

end GlobalTheory.PMonE
