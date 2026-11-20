import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedOfFrobeniusIterateFixedFilZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPeriodRingFieldTPowFiltrationUnitsStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

/- English proof (translation)
Use `set M := Matrix.of fun i j : Fin (n + 1) => P.φB^[i] (a j) with hM`. Establish `h1 : P.φB M.det = (M.map P.φB).det`. Rewrite using `[AlgHom.map_det]`. Both sides reduce to the same expression. Establish `h2 : M.map P.φB = Matrix.diagonal (fun i : Fin (n + 1) => if i = Fin.last n then (l : P.R.B) else 1) * M.submatrix (finRotate (n + 1)) id`.

Use extensionality with `i j`. Rewrite using `[Matrix.diagonal_mul, Matrix.map_apply, Matrix.submatrix_apply, finRotate_succ_apply, id]`. Simplify using `only [hM, Matrix.of_apply]`. Rewrite using `[← Function.iterate_succ_apply' (f := P.φB)]`. Distinguish the cases in `hi : i = Fin.last n`.

Substitute `hi` using the available equality. Simplify using `[ha]`. Rewrite using `[if_neg hi, one_mul, Fin.val_add_one, if_neg hi]`. Rewrite using `[h1, h2, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_permute, sign_finRotate]`. Simplify using `[Finset.prod_ite_eq']`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem phiB_moore_det {l : ℕ} [Fact l.Prime] (P : LocPrime l) (n : ℕ) (a : Fin (n + 1) → P.R.B)
    (ha : ∀ j, P.φB^[n + 1] (a j) = (l : P.R.B) * a j) :
    P.φB (Matrix.of fun i j : Fin (n + 1) => P.φB^[i] (a j)).det =
      (-1) ^ n * (l : P.R.B) * (Matrix.of fun i j : Fin (n + 1) => P.φB^[i] (a j)).det := by
  set M := Matrix.of fun i j : Fin (n + 1) => P.φB^[i] (a j) with hM
  have h1 : P.φB M.det = (M.map P.φB).det := by
    rw [AlgHom.map_det]; rfl
  have h2 : M.map P.φB = Matrix.diagonal (fun i : Fin (n + 1) => if i = Fin.last n then (l : P.R.B) else 1) *
      M.submatrix (finRotate (n + 1)) id := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.map_apply, Matrix.submatrix_apply, finRotate_succ_apply, id]
    simp only [hM, Matrix.of_apply]
    rw [← Function.iterate_succ_apply' (f := P.φB)]
    by_cases hi : i = Fin.last n
    · subst hi
      simp [ha]
    · rw [if_neg hi, one_mul, Fin.val_add_one, if_neg hi]
  rw [h1, h2, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_permute, sign_finRotate]
  simp [Finset.prod_ite_eq']
  ring

/- English proof (translation)
Introduce `l _ P AI T h hh a ha _ hd hF`. Take `⟨n, rfl⟩ : ∃ n, h = n + 1` from `⟨h - 1, by omega⟩`. Use `set d := (Matrix.of fun i j : Fin (n + 1) => P.φB^[i] (a j)).det with hdd`. Establish `hφd : P.φB d = (-1) ^ n * (l : P.R.B) * d` using `phiB_moore_det P n a ha`. Establish `ht : IsUnit P.tB` using `isUnit_tB P`.

Establish `hl : IsUnit (l : P.R.B)`. Establish `h0 : (l : ℚ_[l]) ≠ 0` using `Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero`. Use `(IsUnit.mk0 _ h0).map (algebraMap ℚ_[l] P.R.B)` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Establish `hφt : P.φB P.tB = (l : P.R.B) * P.tB`.

Rewrite using `[localPrime_frobenius_periodT, Algebra.smul_def, map_natCast]`. Use `set c := d * ((ht.unit⁻¹ : P.R.Bˣ) : P.R.B) with hc`. Establish `hct : c * P.tB = d`. Rewrite using `[hc, mul_assoc, Units.inv_mul_of_eq ht.unit_spec, mul_one]`. Establish `hφc : P.φB c = (-1) ^ n * c`.

Apply `(hl.mul ht).mul_right_cancel` to reduce the goal to its premises. Establish `e` using `congrArg P.φB hct`. Rewrite `e` using `[map_mul, hφt, hφd, ← hct]`. Rewrite using `[show P.φB c * ((l : P.R.B) * P.tB) = P.φB c * ((l : P.R.B) * P.tB) from rfl]`. Take the linear combination `e`.

Establish `hφ2 : P.φB^[2] c = c`. Rewrite using `[Function.iterate_succ_apply', Function.iterate_one, hφc, map_mul, hφc, map_pow, map_neg, map_one, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]`. Establish `hFc : P.ιB c ∈ Fil P 0`. Establish `e : tz P 1 * P.ιB c = P.ιB d`. Rewrite using `[show tz P 1 = P.ιB P.tB by simp [tz], ← map_mul, mul_comm, hct]`.

Establish `key` using `(GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T).2.2.1 0 1 (P.ιB c)`. Rewrite `key` using `[zero_add, e]`. Conclude with `key.2 hF`. Establish `hev : ∀ j < 2, ev P j c ∈ Fil P 0`. Introduce `j hj`.

Use `interval_cases j`. Simplify `hFc` using `[ev]`. Simplify using `only [ev, Function.iterate_one, hφc, map_mul, map_pow, map_neg, map_one]`. Break down `neg_one_pow_eq_or P.R.BdR n with h1 | h1` into its components or cases. Rewrite using `[h1, one_mul]`.

Conclude with `hFc`. Rewrite using `[h1, neg_one_mul]`. Simplify using `only [Fil, SetLike.mem_coe] at hFc ⊢`. Conclude with `neg_mem hFc`. Take `⟨κ, -, hκ⟩` from `GlobalTheory.T.unramified_of_frobeniusIterate_fixed_filZero l P AI T 2 two_pos c hφ2 hev`.

Use `⟨κ, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Apply `hd` to reduce the goal to its premises. Rewrite using `[← hct, hκ, map_zero, zero_mul]`. Rewrite using `[← hκ, hct]`.
-/
theorem mooreDeterminant_eq_unramified_mul_period_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (h : ℕ), 0 < h → ∀ a : Fin h → P.R.B, (∀ j, P.φB^[h] (a j) = (l : P.R.B) * a j) → (∀ (i : ℕ) j, ev P i (a j) ∈ Fil P 0) → (Matrix.of fun i j : Fin h => P.φB^[i] (a j)).det ≠ 0 → P.ιB (Matrix.of fun i j : Fin h => P.φB^[i] (a j)).det ∈ Fil P 1 → ∃ κ : ↥(MaximalUnramifiedExtension l), κ ≠ 0 ∧ (Matrix.of fun i j : Fin h => P.φB^[i] (a j)).det = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B κ * P.tB := by
  intro l _ P AI T h hh a ha _ hd hF
  obtain ⟨n, rfl⟩ : ∃ n, h = n + 1 := ⟨h - 1, by omega⟩
  set d := (Matrix.of fun i j : Fin (n + 1) => P.φB^[i] (a j)).det with hdd
  have hφd : P.φB d = (-1) ^ n * (l : P.R.B) * d := phiB_moore_det P n a ha
  have ht : IsUnit P.tB := isUnit_tB P
  have hl : IsUnit (l : P.R.B) := by
    have h0 : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
    have := (IsUnit.mk0 _ h0).map (algebraMap ℚ_[l] P.R.B)
    rwa [map_natCast] at this
  have hφt : P.φB P.tB = (l : P.R.B) * P.tB := by
    rw [localPrime_frobenius_periodT, Algebra.smul_def, map_natCast]
  set c := d * ((ht.unit⁻¹ : P.R.Bˣ) : P.R.B) with hc
  have hct : c * P.tB = d := by
    rw [hc, mul_assoc, Units.inv_mul_of_eq ht.unit_spec, mul_one]
  have hφc : P.φB c = (-1) ^ n * c := by
    apply (hl.mul ht).mul_right_cancel
    have e := congrArg P.φB hct
    rw [map_mul, hφt, hφd, ← hct] at e
    rw [show P.φB c * ((l : P.R.B) * P.tB) = P.φB c * ((l : P.R.B) * P.tB) from rfl]
    linear_combination e
  have hφ2 : P.φB^[2] c = c := by
    rw [Function.iterate_succ_apply', Function.iterate_one, hφc, map_mul, hφc, map_pow, map_neg, map_one, ← mul_assoc,
      ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
  have hFc : P.ιB c ∈ Fil P 0 := by
    have e : tz P 1 * P.ιB c = P.ιB d := by
      rw [show tz P 1 = P.ιB P.tB by simp [tz], ← map_mul, mul_comm, hct]
    have key := (GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T).2.2.1 0 1 (P.ιB c)
    rw [zero_add, e] at key
    exact key.2 hF
  have hev : ∀ j < 2, ev P j c ∈ Fil P 0 := by
    intro j hj
    interval_cases j
    · simpa [ev] using hFc
    · simp only [ev, Function.iterate_one, hφc, map_mul, map_pow, map_neg, map_one]
      rcases neg_one_pow_eq_or P.R.BdR n with h1 | h1
      · rw [h1, one_mul]; exact hFc
      · rw [h1, neg_one_mul]
        simp only [Fil, SetLike.mem_coe] at hFc ⊢
        exact neg_mem hFc
  obtain ⟨κ, -, hκ⟩ := GlobalTheory.T.unramified_of_frobeniusIterate_fixed_filZero l P AI T 2 two_pos c hφ2 hev
  refine ⟨κ, ?_, ?_⟩
  · rintro rfl
    apply hd
    rw [← hct, hκ, map_zero, zero_mul]
  · rw [← hκ, hct]

end GlobalTheory.PMon
