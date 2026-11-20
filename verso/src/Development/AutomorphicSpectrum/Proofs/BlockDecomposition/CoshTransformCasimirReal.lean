import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondGelfandInvariantValueEq

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

/- English proof (translation)
Establish `h : ∀ a, Formalism.REAL.Amat l a j = (if a = j then l j else 0) + (if a < j then -1 else 0)`. Introduce `a`. Simplify using `only [Formalism.REAL.Amat, Matrix.of_apply]`. Distinguish the cases in `h1 : a = j`. Substitute `h1` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[h1]`. Simplify using `only [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Rewrite using `[Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.filter_gt_eq_Iio, Fin.card_Iio]`. Simplify using `[sub_eq_add_neg]`.
-/
private theorem sum_amat_first_index_eq {n : ℕ} (l : Fin n → ℂ) (j : Fin n) :
    ∑ a, Formalism.REAL.Amat l a j = l j - ((j : ℕ) : ℂ) := by
  have h : ∀ a, Formalism.REAL.Amat l a j = (if a = j then l j else 0) + (if a < j then -1 else 0) := by
    intro a
    simp only [Formalism.REAL.Amat, Matrix.of_apply]
    by_cases h1 : a = j
    · subst h1
      simp
    · simp [h1]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.filter_gt_eq_Iio,
    Fin.card_Iio]
  simp [sub_eq_add_neg]

/- English proof (translation)
Establish `h : ∀ b, Formalism.REAL.Amat l j b = (if j = b then l j else 0) + (if j < b then -1 else 0)`. Introduce `b`. Simplify using `only [Formalism.REAL.Amat, Matrix.of_apply]`. Distinguish the cases in `h1 : j = b`. Substitute `h1` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[h1]`. Simplify using `only [h, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Rewrite using `[Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.filter_lt_eq_Ioi, Fin.card_Ioi]`. Simplify using `[sub_eq_add_neg]`.
-/
private theorem sum_amat_second_index_eq {n : ℕ} (l : Fin n → ℂ) (j : Fin n) :
    ∑ b, Formalism.REAL.Amat l j b = l j - ((n - 1 - j : ℕ) : ℂ) := by
  have h : ∀ b, Formalism.REAL.Amat l j b = (if j = b then l j else 0) + (if j < b then -1 else 0) := by
    intro b
    simp only [Formalism.REAL.Amat, Matrix.of_apply]
    by_cases h1 : j = b
    · subst h1
      simp
    · simp [h1]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.filter_lt_eq_Ioi,
    Fin.card_Ioi]
  simp [sub_eq_add_neg]

/- English proof (translation)
Establish `key : ∀ j : Fin n, (∑ a, Formalism.REAL.Amat (fun i => c i + ((n : ℂ) - 1) / 2) a j) * (∑ b, Formalism.REAL.Amat (fun i => c i + ((n : ℂ) - 1) / 2) j b) = c j ^ 2 - (((n : ℂ) - 1) / 2 - ((j : ℕ) : ℂ)) ^ 2`. Introduce `j`. Establish `hj : (j : ℕ) + 1 ≤ n` using `j.isLt`. Rewrite using `[sum_amat_first_index_eq, sum_amat_second_index_eq, Nat.sub_sub, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]`. Expand and normalize the polynomial expressions, which then agree.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [GlobalTheory.Dec.gelfVal, sq, Matrix.mul_apply, Finset.sum_mul_sum]`. Use `conv_rhs => rw [Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Conclude with `Finset.sum_comm`.

Use `_ = _ := Finset.sum_congr rfl fun j _ => key j`.
-/
private theorem gelfVal_two_eq_sum_sq_sub_sq {n : ℕ} (c : Fin n → ℂ) :
    GlobalTheory.Dec.gelfVal c 2 = ∑ j, (c j ^ 2 - (((n : ℂ) - 1) / 2 - ((j : ℕ) : ℂ)) ^ 2) := by
  have key : ∀ j : Fin n,
      (∑ a, Formalism.REAL.Amat (fun i => c i + ((n : ℂ) - 1) / 2) a j) *
        (∑ b, Formalism.REAL.Amat (fun i => c i + ((n : ℂ) - 1) / 2) j b) =
        c j ^ 2 - (((n : ℂ) - 1) / 2 - ((j : ℕ) : ℂ)) ^ 2 := by
    intro j
    have hj : (j : ℕ) + 1 ≤ n := j.isLt
    rw [sum_amat_first_index_eq, sum_amat_second_index_eq, Nat.sub_sub, Nat.cast_sub (by omega), Nat.cast_add,
      Nat.cast_one]
    ring
  calc GlobalTheory.Dec.gelfVal c 2
      = ∑ j, (∑ a, Formalism.REAL.Amat (fun i => c i + ((n : ℂ) - 1) / 2) a j) *
          (∑ b, Formalism.REAL.Amat (fun i => c i + ((n : ℂ) - 1) / 2) j b) := by
        simp only [GlobalTheory.Dec.gelfVal, sq, Matrix.mul_apply, Finset.sum_mul_sum]
        conv_rhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        exact Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun j _ => key j

/- English proof (translation)
Take `⟨σ, hσ⟩` from `h`. Establish `hT : ∑ a, conj (χ true a) ^ 2 = ∑ a, χ false a ^ 2`. Rewrite using `[← Equiv.sum_comp σ (fun a => χ false a ^ 2)]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[hσ a, neg_sq]`.

Establish `hF : ∑ a, conj (χ false a) ^ 2 = ∑ a, χ true a ^ 2`. Establish `h2` using `congrArg conj hT`. Simplify `h2.symm` using `[map_sum, map_pow]`. Establish `hK : ∀ j : Fin n, conj (((n : ℂ) - 1) / 2 - ((j : ℕ) : ℂ)) = ((n : ℂ) - 1) / 2 - ((j : ℕ) : ℂ)`. Introduce `j`.

Simplify using `only [map_sub, map_div₀, map_natCast, map_one, map_ofNat]`. Establish `hconj : ∀ x : Fin n → ℂ, conj (GlobalTheory.Dec.gelfVal x 2) = ∑ j, (conj (x j) ^ 2 - (((n : ℂ) - 1) / 2 - ((j : ℕ) : ℂ)) ^ 2)`. Introduce `x`. Rewrite using `[gelfVal_two_eq_sum_sq_sub_sq, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[map_sub, map_pow, map_pow, hK]`. Simplify using `only [cas]`. Rewrite using `[map_mul, map_add, hconj, hconj, map_ofNat, gelfVal_two_eq_sum_sq_sub_sq, gelfVal_two_eq_sum_sq_sub_sq]`. Simplify using `only [Finset.sum_sub_distrib]`. Rewrite using `[hT, hF]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem conj_cas_of_isHerm {n : ℕ} {χ : Inf n} (h : IsHerm χ) : conj (cas χ) = cas χ := by
  obtain ⟨σ, hσ⟩ := h
  have hT : ∑ a, conj (χ true a) ^ 2 = ∑ a, χ false a ^ 2 := by
    rw [← Equiv.sum_comp σ (fun a => χ false a ^ 2)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hσ a, neg_sq]
  have hF : ∑ a, conj (χ false a) ^ 2 = ∑ a, χ true a ^ 2 := by
    have h2 := congrArg conj hT
    simpa [map_sum, map_pow] using h2.symm
  have hK : ∀ j : Fin n, conj (((n : ℂ) - 1) / 2 - ((j : ℕ) : ℂ)) = ((n : ℂ) - 1) / 2 - ((j : ℕ) : ℂ) := by
    intro j
    simp only [map_sub, map_div₀, map_natCast, map_one, map_ofNat]
  have hconj : ∀ x : Fin n → ℂ, conj (GlobalTheory.Dec.gelfVal x 2) =
      ∑ j, (conj (x j) ^ 2 - (((n : ℂ) - 1) / 2 - ((j : ℕ) : ℂ)) ^ 2) := by
    intro x
    rw [gelfVal_two_eq_sum_sq_sub_sq, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_sub, map_pow, map_pow, hK]
  simp only [cas]
  rw [map_mul, map_add, hconj, hconj, map_ofNat, gelfVal_two_eq_sum_sq_sub_sq, gelfVal_two_eq_sum_sq_sub_sq]
  simp only [Finset.sum_sub_distrib]
  rw [hT, hF]
  ring

/- English proof (translation)
Establish `hw2 : (c ^ (1 / 2 : ℂ)) ^ 2 = c`. Establish `h` using `Complex.cpow_nat_inv_pow c (n := 2) two_ne_zero`. Simplify `h` using `[one_div]`. Establish `hsq : conj (c ^ (1 / 2 : ℂ)) ^ 2 = (c ^ (1 / 2 : ℂ)) ^ 2`. Rewrite using `[← map_pow, hw2, hc]`.

Rewrite using `[← Complex.cosh_conj, map_mul, Complex.conj_ofReal]`. Break down `sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h` into its components or cases. Rewrite using `[h]`. Rewrite using `[h, mul_neg, Complex.cosh_neg]`.
-/
theorem conj_cosh_mul_sqrt {c : ℂ} (hc : conj c = c) (t : ℝ) :
    conj (Complex.cosh (t * c ^ (1 / 2 : ℂ))) = Complex.cosh (t * c ^ (1 / 2 : ℂ)) := by
  have hw2 : (c ^ (1 / 2 : ℂ)) ^ 2 = c := by
    have h := Complex.cpow_nat_inv_pow c (n := 2) two_ne_zero
    simpa [one_div] using h
  have hsq : conj (c ^ (1 / 2 : ℂ)) ^ 2 = (c ^ (1 / 2 : ℂ)) ^ 2 := by
    rw [← map_pow, hw2, hc]
  rw [← Complex.cosh_conj, map_mul, Complex.conj_ofReal]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · rw [h]
  · rw [h, mul_neg, Complex.cosh_neg]

/- English proof (translation)
Introduce `n χ g T hχ _`. Establish `hc` using `conj_cas_of_isHerm hχ`. Simplify using `only [coshT]`. Rewrite using `[← integral_conj]`. Use `congr 1`.

Use function extensionality and compare the values at `t`. Rewrite using `[map_mul, Complex.conj_ofReal, conj_cosh_mul_sqrt hc t]`.
-/
theorem conj_coshT_cas : ∀ (n : ℕ) (χ : Inf n) (g : ℝ → ℝ) (T : ℝ), IsHerm χ → IsBump g T →
    conj (coshT g (cas χ)) = coshT g (cas χ) := by
  intro n χ g T hχ _
  have hc := conj_cas_of_isHerm hχ
  simp only [coshT]
  rw [← integral_conj]
  congr 1
  funext t
  rw [map_mul, Complex.conj_ofReal, conj_cosh_mul_sqrt hc t]

end GlobalTheory.CompanionTheory.WaveMult
