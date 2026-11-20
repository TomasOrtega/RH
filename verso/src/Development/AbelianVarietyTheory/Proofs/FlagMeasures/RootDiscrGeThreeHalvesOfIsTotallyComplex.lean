import Mathlib
import Formalism.HermitianLattices.StatementMass

open MeasureTheory NumberField Finset

namespace GlobalTheory

open MeasureTheory NumberField Finset in

/- English proof (translation)
Introduce `K _ _ hK`. Establish `hf : _root_.Formalism.HermitianLatticesTheory.fDeg K = InfinitePlace.nrComplexPlaces K`. Unfold `_root_.Formalism.HermitianLatticesTheory.fDeg`. Rewrite using `[InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]`. Establish `hn : Module.finrank ℚ K = 2 * _root_.Formalism.HermitianLatticesTheory.fDeg K`.

Rewrite using `[hf]`. Conclude with `IsTotallyComplex.finrank K`. Establish `hpos : 0 < Module.finrank ℚ K` using `Module.finrank_pos`. Establish `h1 : 1 ≤ _root_.Formalism.HermitianLatticesTheory.fDeg K` using `by omega`. Establish `hv : 2 * _root_.Formalism.HermitianLatticesTheory.vInv K = |(discr K : ℝ)| ^ (1 / (2 * (_root_.Formalism.HermitianLatticesTheory.fDeg K : ℝ)))`.

Unfold `_root_.Formalism.HermitianLatticesTheory.vInv`. Expand and normalize the polynomial expressions, which then agree. Establish `hD0 : 0 ≤ |(discr K : ℝ)|` using `abs_nonneg _`. Establish `hbound : (3 / 2 : ℝ) ^ (2 * _root_.Formalism.HermitianLatticesTheory.fDeg K) ≤ |(discr K : ℝ)|`. Establish `hd` using `abs_discr_ge (K := K) (by omega)`.

Rewrite `hd` using `[hn, Int.cast_abs]`. Use `le_trans ?_ hd` and prove the remaining obligations. Take `⟨m, hm⟩ : ∃ m, _root_.Formalism.HermitianLatticesTheory.fDeg K = m + 1` from `⟨_root_.Formalism.HermitianLatticesTheory.fDeg K - 1, by omega⟩`. Rewrite using `[hm, pow_mul, pow_mul, pow_succ ((3 / 2 : ℝ) ^ 2), pow_succ ((3 * Real.pi / 4) ^ 2)]`. Establish `hpi` using `Real.pi_gt_d2`.

Establish `hc : (11 / 2 : ℝ) ≤ (3 * Real.pi / 4) ^ 2` using `by nlinarith`. Establish `hm' : ((3 / 2 : ℝ) ^ 2) ^ m ≤ ((3 * Real.pi / 4) ^ 2) ^ m` using `pow_le_pow_left₀ (by positivity) (by nlinarith) m`. Establish `hc' : (3 / 2 : ℝ) ^ 2 ≤ 4 / 9 * (3 * Real.pi / 4) ^ 2` using `by nlinarith`. Use `mul_le_mul hm' hc' (by positivity) (by positivity)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hne : (2 * _root_.Formalism.HermitianLatticesTheory.fDeg K) ≠ 0` using `by omega`. Establish `hexp : (1 / (2 * (_root_.Formalism.HermitianLatticesTheory.fDeg K : ℝ))) = (((2 * _root_.Formalism.HermitianLatticesTheory.fDeg K : ℕ) : ℝ))⁻¹` using `by push_cast; rw [one_div]`. Use `⟨hn, h1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hv, hexp]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hv, ← Real.rpow_natCast, ← Real.rpow_mul hD0, Real.sqrt_eq_rpow]`. Use `congr 1`. Establish `: (_root_.Formalism.HermitianLatticesTheory.fDeg K : ℝ) ≠ 0` using `by exact_mod_cast (by omega : _root_.Formalism.HermitianLatticesTheory.fDeg K ≠ 0)`. Clear the denominators using the available nonvanishing facts.
-/
theorem _root_.GlobalTheory.rootDiscr_ge_three_halves_of_totallyComplex :
    ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K →
      Module.finrank ℚ K = 2 * _root_.Formalism.HermitianLatticesTheory.fDeg K ∧ 1 ≤ _root_.Formalism.HermitianLatticesTheory.fDeg K ∧
      (3 / 2 : ℝ) ≤ 2 * _root_.Formalism.HermitianLatticesTheory.vInv K ∧
      Real.sqrt |(discr K : ℝ)| = (2 * _root_.Formalism.HermitianLatticesTheory.vInv K) ^ _root_.Formalism.HermitianLatticesTheory.fDeg K := by
  intro K _ _ hK
  have hf : _root_.Formalism.HermitianLatticesTheory.fDeg K = InfinitePlace.nrComplexPlaces K := by
    unfold _root_.Formalism.HermitianLatticesTheory.fDeg
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  have hn : Module.finrank ℚ K = 2 * _root_.Formalism.HermitianLatticesTheory.fDeg K := by
    rw [hf]; exact IsTotallyComplex.finrank K
  have hpos : 0 < Module.finrank ℚ K := Module.finrank_pos
  have h1 : 1 ≤ _root_.Formalism.HermitianLatticesTheory.fDeg K := by omega
  have hv : 2 * _root_.Formalism.HermitianLatticesTheory.vInv K = |(discr K : ℝ)| ^ (1 / (2 * (_root_.Formalism.HermitianLatticesTheory.fDeg K : ℝ))) := by
    unfold _root_.Formalism.HermitianLatticesTheory.vInv; ring
  have hD0 : 0 ≤ |(discr K : ℝ)| := abs_nonneg _
  have hbound : (3 / 2 : ℝ) ^ (2 * _root_.Formalism.HermitianLatticesTheory.fDeg K) ≤ |(discr K : ℝ)| := by
    have hd := abs_discr_ge (K := K) (by omega)
    rw [hn, Int.cast_abs] at hd
    refine le_trans ?_ hd
    obtain ⟨m, hm⟩ : ∃ m, _root_.Formalism.HermitianLatticesTheory.fDeg K = m + 1 := ⟨_root_.Formalism.HermitianLatticesTheory.fDeg K - 1, by omega⟩
    rw [hm, pow_mul, pow_mul, pow_succ ((3 / 2 : ℝ) ^ 2), pow_succ ((3 * Real.pi / 4) ^ 2)]
    have hpi := Real.pi_gt_d2
    have hc : (11 / 2 : ℝ) ≤ (3 * Real.pi / 4) ^ 2 := by nlinarith
    have hm' : ((3 / 2 : ℝ) ^ 2) ^ m ≤ ((3 * Real.pi / 4) ^ 2) ^ m :=
      pow_le_pow_left₀ (by positivity) (by nlinarith) m
    have hc' : (3 / 2 : ℝ) ^ 2 ≤ 4 / 9 * (3 * Real.pi / 4) ^ 2 := by nlinarith
    have := mul_le_mul hm' hc' (by positivity) (by positivity)
    linarith
  have hne : (2 * _root_.Formalism.HermitianLatticesTheory.fDeg K) ≠ 0 := by omega
  have hexp : (1 / (2 * (_root_.Formalism.HermitianLatticesTheory.fDeg K : ℝ))) = (((2 * _root_.Formalism.HermitianLatticesTheory.fDeg K : ℕ) : ℝ))⁻¹ := by
    push_cast; rw [one_div]
  refine ⟨hn, h1, ?_, ?_⟩
  · rw [hv, hexp]
    calc (3 / 2 : ℝ) = ((3 / 2 : ℝ) ^ (2 * _root_.Formalism.HermitianLatticesTheory.fDeg K)) ^ (((2 * _root_.Formalism.HermitianLatticesTheory.fDeg K : ℕ) : ℝ))⁻¹ :=
          (Real.pow_rpow_inv_natCast (by norm_num) hne).symm
      _ ≤ |(discr K : ℝ)| ^ (((2 * _root_.Formalism.HermitianLatticesTheory.fDeg K : ℕ) : ℝ))⁻¹ :=
          Real.rpow_le_rpow (by positivity) hbound (by positivity)
  · rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul hD0, Real.sqrt_eq_rpow]
    congr 1
    have : (_root_.Formalism.HermitianLatticesTheory.fDeg K : ℝ) ≠ 0 := by exact_mod_cast (by omega : _root_.Formalism.HermitianLatticesTheory.fDeg K ≠ 0)
    field_simp

end GlobalTheory
