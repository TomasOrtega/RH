import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CellLintegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.NAInterSupSSubset
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumRankinSelbergSchurTermFinsuppEulerProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.ZEulLocal

/- English proof (translation)
Establish `h1 : ∀ i : Fin n, (∑ j : Fin n, if i < j then a i - a j else 0) = (∑ j : Fin n, if i < j then a i else 0) - ∑ j : Fin n, if i < j then a j else 0`. Introduce `i`. Rewrite using `[← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.

Rewrite using `[GlobalTheory.CellDec.wtS, Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_sub_distrib, Finset.sum_comm (f := fun i j => if i < j then a j else 0)]`. Simplify using `only [← Finset.sum_filter, Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio, Finset.sum_const, Fin.card_Ioi, Fin.card_Iio, nsmul_eq_mul, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `hi` using `i.isLt`. Rewrite using `[Nat.cast_sub (by omega), Nat.cast_sub (by omega)]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wtS_eq_sum (n : ℕ) (a : Fin n → ℤ) :
    GlobalTheory.CellDec.wtS n a = ∑ i : Fin n, ((n : ℤ) - 1 - 2 * (i : ℕ)) * a i := by
  have h1 : ∀ i : Fin n, (∑ j : Fin n, if i < j then a i - a j else 0) =
      (∑ j : Fin n, if i < j then a i else 0) - ∑ j : Fin n, if i < j then a j else 0 := by
    intro i
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  rw [GlobalTheory.CellDec.wtS, Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_sub_distrib,
    Finset.sum_comm (f := fun i j => if i < j then a j else 0)]
  simp only [← Finset.sum_filter, Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio, Finset.sum_const,
    Fin.card_Ioi, Fin.card_Iio, nsmul_eq_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := i.isLt
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

open GlobalTheory.JSW in

/- English proof (translation)
Introduce `q hq n α β x v h0 hv`. Establish `hqR : (0 : ℝ) < q` using `by exact_mod_cast hq`. Establish `hl : Antitone (fun i => (v i).toNat)` using `fun i j hij => Int.toNat_le_toNat (hv hij)`. Establish `hcast : ∀ i, (((v i).toNat : ℕ) : ℂ) = ((v i : ℝ) : ℂ)`. Introduce `i`.

Rewrite using `[← Int.cast_natCast, Int.toNat_of_nonneg (h0 i)]`. Simplify using the standard rewrite rules. Use `set cR : ℝ := ∑ i : Fin n, ((n : ℝ) - 1 - 2 * (i : ℕ)) * (v i : ℝ) with hcR`. Establish `hc : (∑ i : Fin n, (((n : ℂ) - 1 - 2 * (i : ℕ)) * (((v i).toNat : ℕ) : ℂ))) = (cR : ℂ)`. Rewrite using `[hcR]`.

Use `push_cast`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hcast i, Complex.ofReal_intCast]`. Use `set A : ℝ := (q : ℝ) ^ (-cR / 2) with hA'`. Establish `hA : (q : ℂ) ^ (-(cR : ℂ) / 2) = (A : ℂ)`.

Rewrite using `[hA', Complex.ofReal_cpow hqR.le]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hW : (GlobalTheory.CellDec.wtS n v : ℝ) = cR`. Rewrite using `[GlobalTheory.ZEulLocal.wtS_eq_sum, hcR]`.

Use `push_cast`. Both sides reduce to the same expression. Establish `key : (q : ℝ) ^ GlobalTheory.CellDec.wtS n v * (A * A) = 1`. Rewrite using `[hA', ← Real.rpow_add hqR, ← Real.rpow_intCast, ← Real.rpow_add hqR, hW]`. Rewrite using `[show cR + (-cR / 2 + -cR / 2) = 0 by ring, Real.rpow_zero]`.

Establish `key2 : (((q : ℝ) ^ (-x * ∑ i, (v i : ℝ)) : ℝ) : ℂ) = ((q : ℂ) ^ (-(x : ℂ))) ^ (∑ i, (v i).toNat)`. Establish `e : (q : ℂ) ^ (-(x : ℂ)) = (((q : ℝ) ^ (-x) : ℝ) : ℂ)`. Rewrite using `[Complex.ofReal_cpow hqR.le]`. Use `push_cast`. Both sides reduce to the same expression.

Rewrite using `[e, ← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul hqR.le]`. Use `congr 3`. Use `push_cast`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Conclude with `(Int.toNat_of_nonneg (h0 i)).symm` after adjusting the coercions.

Rewrite using `[sphW, sphW, if_pos hl, if_pos hl, hc, hA, GlobalTheory.ZEul.rsTerm, if_pos ⟨h0, hv⟩, key2, map_mul, Complex.conj_ofReal]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem localTerm_eq : ∀ (q : ℕ), 0 < q → ∀ (n : ℕ) (α β : Fin n → ℂ) (x : ℝ) (v : Fin n → ℤ), (∀ i, 0 ≤ v i) → Antitone v →
    (((q : ℝ) ^ GlobalTheory.CellDec.wtS n v : ℝ) : ℂ) *
      (GlobalTheory.JSW.sphW q α (fun i => (v i).toNat) * conj (GlobalTheory.JSW.sphW q β (fun i => (v i).toNat))) *
      (((q : ℝ) ^ (-x * ∑ i, (v i : ℝ)) : ℝ) : ℂ) = GlobalTheory.ZEul.rsTerm q α β x v := by
  intro q hq n α β x v h0 hv
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hl : Antitone (fun i => (v i).toNat) := fun i j hij => Int.toNat_le_toNat (hv hij)
  have hcast : ∀ i, (((v i).toNat : ℕ) : ℂ) = ((v i : ℝ) : ℂ) := by
    intro i
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (h0 i)]
    simp
  set cR : ℝ := ∑ i : Fin n, ((n : ℝ) - 1 - 2 * (i : ℕ)) * (v i : ℝ) with hcR
  have hc : (∑ i : Fin n, (((n : ℂ) - 1 - 2 * (i : ℕ)) * (((v i).toNat : ℕ) : ℂ))) = (cR : ℂ) := by
    rw [hcR]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcast i, Complex.ofReal_intCast]
  set A : ℝ := (q : ℝ) ^ (-cR / 2) with hA'
  have hA : (q : ℂ) ^ (-(cR : ℂ) / 2) = (A : ℂ) := by
    rw [hA', Complex.ofReal_cpow hqR.le]
    push_cast
    rfl
  have hW : (GlobalTheory.CellDec.wtS n v : ℝ) = cR := by
    rw [GlobalTheory.ZEulLocal.wtS_eq_sum, hcR]
    push_cast
    rfl
  have key : (q : ℝ) ^ GlobalTheory.CellDec.wtS n v * (A * A) = 1 := by
    rw [hA', ← Real.rpow_add hqR, ← Real.rpow_intCast, ← Real.rpow_add hqR, hW]
    rw [show cR + (-cR / 2 + -cR / 2) = 0 by ring, Real.rpow_zero]
  have key2 : (((q : ℝ) ^ (-x * ∑ i, (v i : ℝ)) : ℝ) : ℂ) = ((q : ℂ) ^ (-(x : ℂ))) ^ (∑ i, (v i).toNat) := by
    have e : (q : ℂ) ^ (-(x : ℂ)) = (((q : ℝ) ^ (-x) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hqR.le]
      push_cast
      rfl
    rw [e, ← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul hqR.le]
    congr 3
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    exact_mod_cast (Int.toNat_of_nonneg (h0 i)).symm
  rw [sphW, sphW, if_pos hl, if_pos hl, hc, hA, GlobalTheory.ZEul.rsTerm, if_pos ⟨h0, hv⟩, key2, map_mul,
    Complex.conj_ofReal]
  calc _ = (((q : ℝ) ^ GlobalTheory.CellDec.wtS n v * (A * A) : ℝ) : ℂ) *
        (schurAt (fun i => (v i).toNat) α * conj (schurAt (fun i => (v i).toNat) β) *
          ((q : ℂ) ^ (-(x : ℂ))) ^ (∑ i, (v i).toNat)) := by push_cast; ring
    _ = _ := by rw [key]; simp

end GlobalTheory.ZEulLocal
