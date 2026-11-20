import Formalism.LocalToGlobal.AlgebraicTheory.StatementA

noncomputable section
open scoped BigOperators

namespace Formalism.L2.AlgTh

/- English proof (translation)
Establish `h1` using `congrArg (PowerSeries.coeff i) h`. Rewrite `h1` using `[PowerSeries.coeff_derivative, PowerSeries.coeff_mul]`. Establish `key : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal i, ((i.choose p.1 : ℕ) : K) * (((p.1).factorial : ℕ) : K) * (((p.2).factorial : ℕ) : K) = ((i.factorial : ℕ) : K)`. Introduce `p hp`. Rewrite `hp` using `[Finset.HasAntidiagonal.mem_antidiagonal]`.

Establish `h2 : p.2 = i - p.1` using `by omega`. Rewrite using `[h2]`. Conclude with `Nat.choose_mul_factorial_mul_factorial (by omega : p.1 ≤ i)` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Nat.factorial_succ]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `_ = ((i.factorial : ℕ) : K) * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal i, PowerSeries.coeff p.1 a * PowerSeries.coeff p.2 F := by rw [h1]`. Use `_ = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal i, ((i.factorial : ℕ) : K) * (PowerSeries.coeff p.1 a * PowerSeries.coeff p.2 F) := by`. Rewrite using `[Finset.mul_sum]`.

Use `_ = _ := by`. Use `Finset.sum_congr rfl (fun p hp => ?_)` and prove the remaining obligations. Rewrite using `[← key p hp]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem jet_succ_eq {K : Type} [Field K] [CharZero K] (F a : PowerSeries K)
    (h : PowerSeries.derivative K F = a * F) (i : ℕ) :
    (((i + 1).factorial : ℕ) : K) * PowerSeries.coeff (i + 1) F =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal i, ((i.choose p.1 : ℕ) : K) *
        ((((p.1).factorial : ℕ) : K) * PowerSeries.coeff p.1 a) *
        ((((p.2).factorial : ℕ) : K) * PowerSeries.coeff p.2 F) := by
  have h1 := congrArg (PowerSeries.coeff i) h
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul] at h1
  have key : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal i,
      ((i.choose p.1 : ℕ) : K) * (((p.1).factorial : ℕ) : K) * (((p.2).factorial : ℕ) : K) =
        ((i.factorial : ℕ) : K) := by
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have h2 : p.2 = i - p.1 := by omega
    rw [h2]
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial (by omega : p.1 ≤ i)
  calc (((i + 1).factorial : ℕ) : K) * PowerSeries.coeff (i + 1) F
      = ((i.factorial : ℕ) : K) * (PowerSeries.coeff (i + 1) F * ((i : K) + 1)) := by
        rw [Nat.factorial_succ]; push_cast; ring
    _ = ((i.factorial : ℕ) : K) * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal i,
          PowerSeries.coeff p.1 a * PowerSeries.coeff p.2 F := by rw [h1]
    _ = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal i,
          ((i.factorial : ℕ) : K) * (PowerSeries.coeff p.1 a * PowerSeries.coeff p.2 F) := by
        rw [Finset.mul_sum]
    _ = _ := by
        refine Finset.sum_congr rfl (fun p hp => ?_)
        rw [← key p hp]
        ring

/- English proof (translation)
Introduce `K _ _ _ F a ρ hρ h hF0 ha i`. Establish `hρ0 : (0 : ℝ) ≤ ρ` using `le_trans zero_le_one hρ`. Proceed by induction on `i using Nat.strong_induction_on with`. Consider the case `_ i ih`. Consider the cases of `i with`.

Consider the case `zero => simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hF0`. Consider the case `succ i`. Rewrite using `[jet_succ_eq F a h i]`. Apply `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hρ0 _)` to reduce the goal to its premises. Introduce `p hp`.

Establish `hp'` using `Finset.HasAntidiagonal.mem_antidiagonal.mp hp`. Establish `hq : p.2 < i + 1` using `by omega`. Rewrite using `[norm_mul, norm_mul]`. Establish `h1 : ‖((i.choose p.1 : ℕ) : K)‖ ≤ 1` using `IsUltrametricDist.norm_natCast_le_one K _`. Establish `h2` using `ha p.1`.

Establish `h3` using `ih p.2 hq`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem log_derivative_jets_integral : LogDerJets := by
  intro K _ _ _ F a ρ hρ h hF0 ha i
  have hρ0 : (0 : ℝ) ≤ ρ := le_trans zero_le_one hρ
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    cases i with
    | zero => simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hF0
    | succ i =>
      rw [jet_succ_eq F a h i]
      apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hρ0 _)
      intro p hp
      have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      have hq : p.2 < i + 1 := by omega
      rw [norm_mul, norm_mul]
      have h1 : ‖((i.choose p.1 : ℕ) : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K _
      have h2 := ha p.1
      have h3 := ih p.2 hq
      calc ‖((i.choose p.1 : ℕ) : K)‖ * ‖(((p.1).factorial : ℕ) : K) * PowerSeries.coeff p.1 a‖ *
            ‖(((p.2).factorial : ℕ) : K) * PowerSeries.coeff p.2 F‖
          ≤ 1 * ρ * ρ ^ p.2 :=
            mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) zero_le_one) h3 (norm_nonneg _)
              (mul_nonneg zero_le_one hρ0)
        _ = ρ ^ (p.2 + 1) := by ring
        _ ≤ ρ ^ (i + 1) := pow_le_pow_right₀ hρ (by omega)

/- English proof (translation)
Introduce `K _ _ G V c M hM hc h`. Consider the cases of `M with`. Consider the case `zero => omega`. Consider the case `succ n`. Establish `hd` using `congrArg (PowerSeries.derivative K) h`.

Rewrite `hd` using `[Derivation.leibniz_pow, Derivation.leibniz, PowerSeries.derivative_C]`. Simplify using `only [smul_eq_mul, nsmul_eq_mul, smul_zero, add_zero, add_tsub_cancel_right] at hd`. Establish `hC : (PowerSeries.C (c ^ (n + 1)) : PowerSeries K) ≠ 0`. Introduce `h0`. Apply `pow_ne_zero (n + 1) hc` to reduce the goal to its premises.

Simplify using `using congrArg PowerSeries.constantCoeff h0`. Apply `mul_left_cancel₀ hC` to reduce the goal to its premises. Rewrite using `[map_natCast]`. Take the linear combination `(-((n + 1 : ℕ) : PowerSeries K) * PowerSeries.derivative K G) * h + G * hd`.
-/
theorem power_log_derivative_jets : PowLogDer := by
  intro K _ _ G V c M hM hc h
  cases M with
  | zero => omega
  | succ n =>
    have hd := congrArg (PowerSeries.derivative K) h
    rw [Derivation.leibniz_pow, Derivation.leibniz, PowerSeries.derivative_C] at hd
    simp only [smul_eq_mul, nsmul_eq_mul, smul_zero, add_zero, add_tsub_cancel_right] at hd
    have hC : (PowerSeries.C (c ^ (n + 1)) : PowerSeries K) ≠ 0 := by
      intro h0
      apply pow_ne_zero (n + 1) hc
      simpa using congrArg PowerSeries.constantCoeff h0
    apply mul_left_cancel₀ hC
    rw [map_natCast]
    linear_combination (-((n + 1 : ℕ) : PowerSeries K) * PowerSeries.derivative K G) * h + G * hd

end Formalism.L2.AlgTh
