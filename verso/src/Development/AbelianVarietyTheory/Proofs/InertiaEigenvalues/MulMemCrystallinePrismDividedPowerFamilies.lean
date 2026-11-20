import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffOfW

noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

/- English proof (translation)
Unfold `dpDen`. Establish `h1` using `Nat.factorial_mul_factorial_dvd_factorial_add i₁ i₂`. Establish `h2 : (n₁ / e).factorial * (n₂ / e).factorial ∣ ((n₁ + n₂) / e).factorial` using `(Nat.factorial_mul_factorial_dvd_factorial_add _ _).trans (Nat.factorial_dvd_factorial (Nat.add_div_le_add_div n₁ n₂ e))`. Establish `h3` using `mul_dvd_mul h1 h2`. Rewrite `h3` using `[mul_mul_mul_comm]`. Then use the resulting hypothesis.
-/
theorem dpDen_mul_dvd_add (e i₁ i₂ n₁ n₂ : ℕ) :
    dpDen e i₁ n₁ * dpDen e i₂ n₂ ∣ dpDen e (i₁ + i₂) (n₁ + n₂) := by
  unfold dpDen
  have h1 := Nat.factorial_mul_factorial_dvd_factorial_add i₁ i₂
  have h2 : (n₁ / e).factorial * (n₂ / e).factorial ∣ ((n₁ + n₂) / e).factorial :=
    (Nat.factorial_mul_factorial_dvd_factorial_add _ _).trans
      (Nat.factorial_dvd_factorial (Nat.add_div_le_add_div n₁ n₂ e))
  have h3 := mul_dvd_mul h1 h2
  rwa [mul_mul_mul_comm] at h3

/- English proof (translation)
Introduce `l _ a e _ _ O K _ _ _ _ _ _ _ t x hx y hy`. Take `⟨w, rfl⟩` from `hx`. Take `⟨w', rfl⟩` from `hy`. Use `haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective`. Use `⟨fun p => ∑ q ∈ Finset.HasAntidiagonal.antidiagonal p.1, ∑ r ∈ Finset.HasAntidiagonal.antidiagonal p.2, ((dpDen e p.1 p.2 / (dpDen e q.1 r.1 * dpDen e q.2 r.2) : ℕ) : Wq l a) * (w (q.1, r.1) * w' (q.2, r.2)), ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `τ`. Use extensionality with `i n`. Rewrite using `[coeff_ofW, Pi.mul_apply, coeff_mul, map_sum, map_sum, map_sum, Finset.sum_div]`. Use `Finset.sum_congr rfl fun q hq => ?_` and prove the remaining obligations. Rewrite using `[coeff_mul, map_sum, map_sum, Finset.sum_div]`.

Use `Finset.sum_congr rfl fun r hr => ?_` and prove the remaining obligations. Rewrite using `[coeff_ofW, coeff_ofW]`. Simplify using `only [map_mul, map_natCast]`. Establish `hd` using `dpDen_mul_dvd_add e q.1 q.2 r.1 r.2`. Rewrite `hd` using `[Finset.HasAntidiagonal.mem_antidiagonal.1 hq, Finset.HasAntidiagonal.mem_antidiagonal.1 hr]`.

Establish `h1 : (dpDen e q.1 r.1 : K) ≠ 0` using `Nat.cast_ne_zero.2 (dpDen_pos _ _ _).ne'`. Establish `h2 : (dpDen e q.2 r.2 : K) ≠ 0` using `Nat.cast_ne_zero.2 (dpDen_pos _ _ _).ne'`. Establish `h3 : (dpDen e i n : K) ≠ 0` using `Nat.cast_ne_zero.2 (dpDen_pos _ _ _).ne'`. Rewrite using `[Nat.cast_div hd (by push_cast; exact mul_ne_zero h1 h2)]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts.
-/
theorem mul_mem_QSet_of_mem : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ x ∈ QSet t K e, ∀ y ∈ QSet t K e, x * y ∈ QSet t K e := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ t x hx y hy
  obtain ⟨w, rfl⟩ := hx
  obtain ⟨w', rfl⟩ := hy
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  refine ⟨fun p => ∑ q ∈ Finset.HasAntidiagonal.antidiagonal p.1, ∑ r ∈ Finset.HasAntidiagonal.antidiagonal p.2,
    ((dpDen e p.1 p.2 / (dpDen e q.1 r.1 * dpDen e q.2 r.2) : ℕ) : Wq l a) *
      (w (q.1, r.1) * w' (q.2, r.2)), ?_⟩
  funext τ
  ext i n
  rw [coeff_ofW, Pi.mul_apply, coeff_mul, map_sum, map_sum, map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [coeff_mul, map_sum, map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [coeff_ofW, coeff_ofW]
  simp only [map_mul, map_natCast]
  have hd := dpDen_mul_dvd_add e q.1 q.2 r.1 r.2
  rw [Finset.HasAntidiagonal.mem_antidiagonal.1 hq, Finset.HasAntidiagonal.mem_antidiagonal.1 hr] at hd
  have h1 : (dpDen e q.1 r.1 : K) ≠ 0 := Nat.cast_ne_zero.2 (dpDen_pos _ _ _).ne'
  have h2 : (dpDen e q.2 r.2 : K) ≠ 0 := Nat.cast_ne_zero.2 (dpDen_pos _ _ _).ne'
  have h3 : (dpDen e i n : K) ≠ 0 := Nat.cast_ne_zero.2 (dpDen_pos _ _ _).ne'
  rw [Nat.cast_div hd (by push_cast; exact mul_ne_zero h1 h2)]
  push_cast
  field_simp

end GlobalTheory.CrysPrism
