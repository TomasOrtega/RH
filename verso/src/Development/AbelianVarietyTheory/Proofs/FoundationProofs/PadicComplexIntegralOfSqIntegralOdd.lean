import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta

/- English proof (translation)
Establish `h : ((2 : ℕ) : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] ((2 : ℕ) : ℚ_[p])` using `(map_natCast _ 2).symm`. Establish `h2 : (2 : ℂ_[p]) = ((2 : ℕ) : ℂ_[p])` using `by norm_num`. Rewrite using `[h2, h, norm_algebraMap', Padic.norm_natCast_eq_one_iff]`. Conclude with `(Nat.coprime_primes (Fact.out) Nat.prime_two).2 hp`.
-/
theorem norm_two_Cp_eq_one (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) : ‖(2 : ℂ_[p])‖ = 1 := by
  have h : ((2 : ℕ) : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] ((2 : ℕ) : ℚ_[p]) := (map_natCast _ 2).symm
  have h2 : (2 : ℂ_[p]) = ((2 : ℕ) : ℂ_[p]) := by norm_num
  rw [h2, h, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact (Nat.coprime_primes (Fact.out) Nat.prime_two).2 hp

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Simplify using `[PowerSeries.coeff_zero_eq_constantCoeff, h0]`.

Use `set f : ℕ × ℕ → ℂ_[p] := fun q => PowerSeries.coeff q.1 H * PowerSeries.coeff q.2 H with hf`. Establish `hsq : PowerSeries.coeff n (H ^ 2) = ∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, f q`. Rewrite using `[pow_two, PowerSeries.coeff_mul]`. Establish `m1 : ((0 : ℕ), n) ∈ Finset.HasAntidiagonal.antidiagonal n` using `by simp`. Establish `m2 : (n, (0 : ℕ)) ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (0, n)`.

Simplify using `only [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal, add_zero, and_true, ne_eq, Prod.mk.injEq]`. Use linear arithmetic over natural numbers and integers. Establish `c0 : PowerSeries.coeff 0 H = 1` using `by rw [PowerSeries.coeff_zero_eq_constantCoeff]; exact h0`. Use `set S := ∑ q ∈ ((Finset.HasAntidiagonal.antidiagonal n).erase (0, n)).erase (n, 0), f q with hS`. Establish `hdec : PowerSeries.coeff n (H ^ 2) = 2 * PowerSeries.coeff n H + S`.

Rewrite using `[hsq, ← Finset.add_sum_erase _ _ m1, ← Finset.add_sum_erase _ _ m2]`. Simplify using `only [hf, c0, one_mul, mul_one]`. Expand and normalize the polynomial expressions, which then agree. Establish `hSle : ‖S‖ ≤ 1`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_` and prove the remaining obligations.

Introduce `q hq`. Simplify using `only [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal, ne_eq] at hq`. Take `⟨hq1, hq2, hq3⟩` from `hq`. Take `⟨a, b⟩` from `q`. Simplify using `only [Prod.mk.injEq, Finset.HasAntidiagonal.mem_antidiagonal] at hq1 hq2 hq3`.

Establish `ha : a < n` using `by omega`. Establish `hb : b < n` using `by omega`. Simplify using `only [hf, norm_mul]`. Conclude with `mul_le_one₀ (ih a ha) (norm_nonneg _) (ih b hb)`. Establish `h2 : ‖2 * PowerSeries.coeff n H‖ = ‖PowerSeries.coeff n H‖`.

Rewrite using `[norm_mul, norm_two_Cp_eq_one p hp, one_mul]`. Establish `e : 2 * PowerSeries.coeff n H = PowerSeries.coeff n (H ^ 2) - S` using `by rw [hdec]; ring`. Rewrite using `[← h2, e]`. Rewrite using `[sub_eq_add_neg]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hH n) ?_)` and prove the remaining obligations.

Rewrite using `[norm_neg]`. Conclude with `hSle`.
-/
theorem intSer_of_sq (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (H : PowerSeries ℂ_[p])
    (h0 : PowerSeries.constantCoeff H = 1) (hH : IntSer (H ^ 2)) : IntSer H := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [PowerSeries.coeff_zero_eq_constantCoeff, h0]
    set f : ℕ × ℕ → ℂ_[p] := fun q => PowerSeries.coeff q.1 H * PowerSeries.coeff q.2 H with hf
    have hsq : PowerSeries.coeff n (H ^ 2) = ∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, f q := by
      rw [pow_two, PowerSeries.coeff_mul]
    have m1 : ((0 : ℕ), n) ∈ Finset.HasAntidiagonal.antidiagonal n := by simp
    have m2 : (n, (0 : ℕ)) ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (0, n) := by
      simp only [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal, add_zero, and_true, ne_eq, Prod.mk.injEq]
      omega
    have c0 : PowerSeries.coeff 0 H = 1 := by rw [PowerSeries.coeff_zero_eq_constantCoeff]; exact h0
    set S := ∑ q ∈ ((Finset.HasAntidiagonal.antidiagonal n).erase (0, n)).erase (n, 0), f q with hS
    have hdec : PowerSeries.coeff n (H ^ 2) = 2 * PowerSeries.coeff n H + S := by
      rw [hsq, ← Finset.add_sum_erase _ _ m1, ← Finset.add_sum_erase _ _ m2]
      simp only [hf, c0, one_mul, mul_one]
      ring
    have hSle : ‖S‖ ≤ 1 := by
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
      intro q hq
      simp only [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal, ne_eq] at hq
      obtain ⟨hq1, hq2, hq3⟩ := hq
      obtain ⟨a, b⟩ := q
      simp only [Prod.mk.injEq, Finset.HasAntidiagonal.mem_antidiagonal] at hq1 hq2 hq3
      have ha : a < n := by omega
      have hb : b < n := by omega
      simp only [hf, norm_mul]
      exact mul_le_one₀ (ih a ha) (norm_nonneg _) (ih b hb)
    have h2 : ‖2 * PowerSeries.coeff n H‖ = ‖PowerSeries.coeff n H‖ := by
      rw [norm_mul, norm_two_Cp_eq_one p hp, one_mul]
    have e : 2 * PowerSeries.coeff n H = PowerSeries.coeff n (H ^ 2) - S := by rw [hdec]; ring
    rw [← h2, e]
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hH n) ?_)
    rw [norm_neg]; exact hSle

/- English proof (translation)
Introduce `p _ hp H h0 hH` and use `intSer_of_sq p hp H h0 hH`.
-/
theorem intSer_of_sq_main : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ H : PowerSeries ℂ_[p],
    PowerSeries.constantCoeff H = 1 → IntSer (H ^ 2) → IntSer H :=
  fun p _ hp H h0 hH => intSer_of_sq p hp H h0 hH

end GlobalTheory.EvenTheta
