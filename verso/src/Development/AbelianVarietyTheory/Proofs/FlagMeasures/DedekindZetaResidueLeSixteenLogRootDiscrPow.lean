import Mathlib
import Formalism.HermitianLattices.StatementMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClassNumberMulRegulatorLeSqrtDiscrRpowStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RootDiscrGeThreeHalvesOfIsTotallyComplexStatement
open MeasureTheory NumberField Finset

namespace GlobalTheory

/- English proof (translation)
Establish `hx0 : 0 < x` using `by linarith`. Establish `hL : (2 / 5 : ℝ) ≤ Real.log x`. Establish `h1` using `Real.le_log_one_add_of_nonneg (x := (1 / 2 : ℝ)) (by norm_num)`. Establish `h2 : Real.log (1 + 1 / 2) ≤ Real.log x` using `Real.log_le_log (by norm_num) (by linarith)`. Evaluate the numerical expressions using `at h1 h2 ⊢`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `set L := Real.log x with hLdef`. Establish `hL0 : 0 < L` using `by linarith`. Use `⟨hL0, ?_⟩` and prove the remaining obligations. Establish `e1 : (1 + 1 / L) / ((1 + 1 / L) - 1) = 1 + L`.

Rewrite using `[add_sub_cancel_left]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : (x ^ f) ^ (1 + 1 / L) = x ^ f * Real.exp 1 ^ f`. Rewrite using `[Real.rpow_add (pow_pos hx0 f), Real.rpow_one, Real.rpow_def_of_pos (pow_pos hx0 f), Real.log_pow, ← hLdef, ← Real.exp_nat_mul]`.

Use `congr 2`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e1, e2, pow_mul, pow_mul]`. Establish `hb : 2 * Real.pi * Real.exp 1 * (1 + L) ^ 2 ≤ (16 * L) ^ 2`. Establish `hpi` using `Real.pi_lt_d2`.

Establish `he` using `Real.exp_one_lt_d9`. Establish `hp0` using `Real.pi_pos`. Establish `he0` using `Real.exp_pos 1`. Establish `h3 : 2 * Real.pi * Real.exp 1 ≤ 18` using `by nlinarith`. Establish `h4 : (1 + L) ^ 2 ≤ (7 / 2 * L) ^ 2` using `pow_le_pow_left₀ (by linarith) (by linarith) 2`.

Combine the equalities or inequalities in the displayed calculation. Establish `hc` using `pow_le_pow_left₀ (by positivity) hb f`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_pow (2 * Real.pi * Real.exp 1), mul_pow (2 * Real.pi)]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)`.
-/
theorem residue_rankin_numeric (x : ℝ) (hx : (3 / 2 : ℝ) ≤ x) (f : ℕ) :
    0 < Real.log x ∧
    (2 * Real.pi) ^ f * ((x ^ f) ^ (1 + 1 / Real.log x) *
      ((1 + 1 / Real.log x) / ((1 + 1 / Real.log x) - 1)) ^ (2 * f))
      ≤ (16 * Real.log x) ^ (2 * f) * x ^ f := by
  have hx0 : 0 < x := by linarith
  have hL : (2 / 5 : ℝ) ≤ Real.log x := by
    have h1 := Real.le_log_one_add_of_nonneg (x := (1 / 2 : ℝ)) (by norm_num)
    have h2 : Real.log (1 + 1 / 2) ≤ Real.log x := Real.log_le_log (by norm_num) (by linarith)
    norm_num at h1 h2 ⊢
    linarith
  set L := Real.log x with hLdef
  have hL0 : 0 < L := by linarith
  refine ⟨hL0, ?_⟩
  have e1 : (1 + 1 / L) / ((1 + 1 / L) - 1) = 1 + L := by
    rw [add_sub_cancel_left]; field_simp; ring
  have e2 : (x ^ f) ^ (1 + 1 / L) = x ^ f * Real.exp 1 ^ f := by
    rw [Real.rpow_add (pow_pos hx0 f), Real.rpow_one, Real.rpow_def_of_pos (pow_pos hx0 f),
      Real.log_pow, ← hLdef, ← Real.exp_nat_mul]
    congr 2
    field_simp
  rw [e1, e2, pow_mul, pow_mul]
  have hb : 2 * Real.pi * Real.exp 1 * (1 + L) ^ 2 ≤ (16 * L) ^ 2 := by
    have hpi := Real.pi_lt_d2
    have he := Real.exp_one_lt_d9
    have hp0 := Real.pi_pos
    have he0 := Real.exp_pos 1
    have h3 : 2 * Real.pi * Real.exp 1 ≤ 18 := by nlinarith
    have h4 : (1 + L) ^ 2 ≤ (7 / 2 * L) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    calc 2 * Real.pi * Real.exp 1 * (1 + L) ^ 2 ≤ 18 * (7 / 2 * L) ^ 2 :=
          mul_le_mul h3 h4 (by positivity) (by norm_num)
      _ ≤ (16 * L) ^ 2 := by nlinarith [sq_nonneg L]
  have hc := pow_le_pow_left₀ (by positivity) hb f
  calc (2 * Real.pi) ^ f * (x ^ f * Real.exp 1 ^ f * ((1 + L) ^ 2) ^ f)
      = (2 * Real.pi * Real.exp 1 * (1 + L) ^ 2) ^ f * x ^ f := by
        rw [mul_pow (2 * Real.pi * Real.exp 1), mul_pow (2 * Real.pi)]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)

/- English proof (translation)
Introduce `K _ _ hK`. Use `⟨dedekindZeta_residue_pos K, ?_⟩` and prove the remaining obligations. Take `⟨hn, -, hx, hd⟩` from `GlobalTheory.T.rootDiscr_ge_three_halves_of_isTotallyComplex K hK`. Take `⟨hL0, hnum⟩` from `residue_rankin_numeric _ hx (Formalism.HermitianLatticesTheory.fDeg K)`. Use `set x := 2 * Formalism.HermitianLatticesTheory.vInv K with hxdef`.

Establish `hx0 : 0 < x` using `by linarith`. Establish `hHR` using `GlobalTheory.T.classNumber_mul_regulator_le_sqrt_discr_rpow' K hK (1 + 1 / Real.log x) (by`. Establish `: 0 < 1 / Real.log x` using `by positivity`. Use the proof step `linarith)`. Establish `hr : InfinitePlace.nrRealPlaces K = 0` using `IsTotallyComplex.nrRealPlaces_eq_zero K`.

Establish `hc : InfinitePlace.nrComplexPlaces K = Formalism.HermitianLatticesTheory.fDeg K`. Use `InfinitePlace.card_add_two_mul_card_eq_rank K` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hw : (1 : ℝ) ≤ (Units.torsionOrder K : ℝ)`. Conclude with `Units.torsionOrder_pos K` after adjusting the coercions.

Rewrite `hHR` using `[hn, hd]`. Rewrite using `[dedekindZeta_residue_def, hr, hc, hd, div_le_iff₀ (by positivity)]`. Establish `hp : 0 < (2 * Real.pi) ^ Formalism.HermitianLatticesTheory.fDeg K` using `by positivity`. Establish `hq : 0 ≤ (16 * Real.log x) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K) * x ^ Formalism.HermitianLatticesTheory.fDeg K` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem dedekindZeta_residue_le_log_rootDiscr_pow :
    ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K →
      0 < dedekindZeta_residue K ∧ dedekindZeta_residue K ≤
        (16 * Real.log (2 * Formalism.HermitianLatticesTheory.vInv K)) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K) := by
  intro K _ _ hK
  refine ⟨dedekindZeta_residue_pos K, ?_⟩
  obtain ⟨hn, -, hx, hd⟩ := GlobalTheory.T.rootDiscr_ge_three_halves_of_isTotallyComplex K hK
  obtain ⟨hL0, hnum⟩ := residue_rankin_numeric _ hx (Formalism.HermitianLatticesTheory.fDeg K)
  set x := 2 * Formalism.HermitianLatticesTheory.vInv K with hxdef
  have hx0 : 0 < x := by linarith
  have hHR := GlobalTheory.T.classNumber_mul_regulator_le_sqrt_discr_rpow' K hK (1 + 1 / Real.log x) (by
    have : 0 < 1 / Real.log x := by positivity
    linarith)
  have hr : InfinitePlace.nrRealPlaces K = 0 := IsTotallyComplex.nrRealPlaces_eq_zero K
  have hc : InfinitePlace.nrComplexPlaces K = Formalism.HermitianLatticesTheory.fDeg K := by
    have := InfinitePlace.card_add_two_mul_card_eq_rank K
    omega
  have hw : (1 : ℝ) ≤ (Units.torsionOrder K : ℝ) := by
    exact_mod_cast Units.torsionOrder_pos K
  rw [hn, hd] at hHR
  rw [dedekindZeta_residue_def, hr, hc, hd, div_le_iff₀ (by positivity)]
  have hp : 0 < (2 * Real.pi) ^ Formalism.HermitianLatticesTheory.fDeg K := by positivity
  have hq : 0 ≤ (16 * Real.log x) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K) * x ^ Formalism.HermitianLatticesTheory.fDeg K := by positivity
  calc (2 : ℝ) ^ 0 * (2 * Real.pi) ^ Formalism.HermitianLatticesTheory.fDeg K * Units.regulator K * (classNumber K : ℝ)
      = (2 * Real.pi) ^ Formalism.HermitianLatticesTheory.fDeg K * ((classNumber K : ℝ) * Units.regulator K) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hHR hp.le
    _ ≤ _ := hnum
    _ ≤ _ := by nlinarith

end GlobalTheory
