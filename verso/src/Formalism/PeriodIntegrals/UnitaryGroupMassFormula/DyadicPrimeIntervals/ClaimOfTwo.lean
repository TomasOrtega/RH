import Mathlib
import Formalism.PeriodIntegrals.PrimesDyadicRS
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.ThetaDiff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.FloorHalf

namespace PI.PrimesDyadicRS.W

/- English proof (translation)
Introduce `y hy`. Establish `hab : ⌊y⌋₊ ≤ ⌊2 * y⌋₊` using `Nat.floor_mono (by linarith)`. Establish `hsub : Nat.primesLE ⌊y⌋₊ ⊆ Nat.primesLE ⌊2 * y⌋₊` using `Nat.primesLE_mono hab`. Rewrite using `[Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE, ← Finset.sum_sdiff hsub, add_sub_cancel_right]`. Establish `hcard : ((Nat.primesLE ⌊2 * y⌋₊ \ Nat.primesLE ⌊y⌋₊).card : ℝ) = (Nat.primeCounting ⌊2 * y⌋₊ : ℝ) - (Nat.primeCounting ⌊y⌋₊ : ℝ)`.

Rewrite using `[Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub), Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting]`. Rewrite using `[← hcard, ← nsmul_eq_mul]`. Apply `Finset.sum_le_card_nsmul` to reduce the goal to its premises. Introduce `p hp`. Establish `hp'` using `(Finset.mem_sdiff.1 hp).1`.

Establish `h2 : (2 : ℝ) ≤ p` using `by exact_mod_cast Nat.two_le_of_mem_primesLE hp'`. Establish `hle : (p : ℝ) ≤ 2 * y` using `(Nat.cast_le.2 (Nat.le_of_mem_primesLE hp')).trans (Nat.floor_le (by linarith))`. Conclude with `Real.log_le_log (by linarith) hle`.
-/
theorem thetaDiff : ThetaDiff := by
  intro y hy
  have hab : ⌊y⌋₊ ≤ ⌊2 * y⌋₊ := Nat.floor_mono (by linarith)
  have hsub : Nat.primesLE ⌊y⌋₊ ⊆ Nat.primesLE ⌊2 * y⌋₊ := Nat.primesLE_mono hab
  rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE,
    ← Finset.sum_sdiff hsub, add_sub_cancel_right]
  have hcard : ((Nat.primesLE ⌊2 * y⌋₊ \ Nat.primesLE ⌊y⌋₊).card : ℝ) =
      (Nat.primeCounting ⌊2 * y⌋₊ : ℝ) - (Nat.primeCounting ⌊y⌋₊ : ℝ) := by
    rw [Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub),
      Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting]
  rw [← hcard, ← nsmul_eq_mul]
  apply Finset.sum_le_card_nsmul
  intro p hp
  have hp' := (Finset.mem_sdiff.1 hp).1
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast Nat.two_le_of_mem_primesLE hp'
  have hle : (p : ℝ) ≤ 2 * y :=
    (Nat.cast_le.2 (Nat.le_of_mem_primesLE hp')).trans (Nat.floor_le (by linarith))
  exact Real.log_le_log (by linarith) hle

/- English proof (translation)
Introduce `x hx`. Establish `h` using `Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x`. Establish `e : Real.sqrt x = x ^ ((2 : ℝ)⁻¹)` using `by rw [Real.sqrt_eq_rpow]; norm_num`. Establish `m3 : Chebyshev.psi (x ^ ((3 : ℝ)⁻¹)) ≤ Chebyshev.psi (x ^ ((2 : ℝ)⁻¹))` using `Chebyshev.psi_mono (Real.rpow_le_rpow_of_exponent_le hx (by norm_num))`. Establish `m5 : Chebyshev.psi (x ^ ((5 : ℝ)⁻¹)) ≤ Chebyshev.psi (x ^ ((2 : ℝ)⁻¹))` using `Chebyshev.psi_mono (Real.rpow_le_rpow_of_exponent_le hx (by norm_num))`.

Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem psiTheta : PsiTheta := by
  intro x hx
  have h := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  have e : Real.sqrt x = x ^ ((2 : ℝ)⁻¹) := by rw [Real.sqrt_eq_rpow]; norm_num
  have m3 : Chebyshev.psi (x ^ ((3 : ℝ)⁻¹)) ≤ Chebyshev.psi (x ^ ((2 : ℝ)⁻¹)) :=
    Chebyshev.psi_mono (Real.rpow_le_rpow_of_exponent_le hx (by norm_num))
  have m5 : Chebyshev.psi (x ^ ((5 : ℝ)⁻¹)) ≤ Chebyshev.psi (x ^ ((2 : ℝ)⁻¹)) :=
    Chebyshev.psi_mono (Real.rpow_le_rpow_of_exponent_le hx (by norm_num))
  rw [e]
  linarith

/- English proof (translation)
The claim follows from `claim_of hS thetaDiff psiTheta hR`.
-/
theorem claim_of_two (hS : SmallNat) (hR : RealIneq) : PI.PrimesDyadicRS.Claim :=
  claim_of hS thetaDiff psiTheta hR

end PI.PrimesDyadicRS.W
