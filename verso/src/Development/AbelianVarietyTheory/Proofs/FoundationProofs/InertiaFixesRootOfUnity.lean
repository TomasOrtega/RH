import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems

namespace GlobalTheory.InertiaRootOfUnity

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem eq_one_of_val_sub_lt {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ)
    (N : ℕ) (hN : ¬ w (N : K) < 1) (u : K) (hu : u ^ N = 1) (h : w (u - 1) < 1) : u = 1 := by
  by_contra hne
  have hx : u - 1 ≠ 0 := sub_ne_zero.mpr hne
  have hw1 : w u = 1 := by
    have h' := Valuation.map_add_eq_of_lt_right w (x := u - 1) (y := 1) (by rw [map_one]; exact h)
    rwa [sub_add_cancel, map_one] at h'
  have hpow : ∀ i : ℕ, w (u ^ i - 1) < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have hr : u ^ (i + 1) - 1 = u * (u ^ i - 1) + (u - 1) := by ring
      rw [hr]
      refine Valuation.map_add_lt w ?_ h
      rw [map_mul, hw1, one_mul]
      exact ih
  have hsum : ∑ i ∈ Finset.range N, u ^ i = 0 := by
    have hg := geom_sum_mul u N
    rw [hu, sub_self] at hg
    exact (mul_eq_zero.mp hg).resolve_right hx
  have hNeq : (N : K) = -∑ i ∈ Finset.range N, (u ^ i - 1) := by
    rw [Finset.sum_sub_distrib, hsum]
    simp
  apply hN
  rw [hNeq, Valuation.map_neg]
  exact w.map_sum_lt one_ne_zero fun i _ => hpow i

/- English proof (translation)
Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem inertia_fixes_root_of_unity {Ω : Type} [Field Ω] [Algebra ℚ Ω] (N : ℕ) (v : GlobalTheory.Ord2.Pl)
    (B : ValuationSubring Ω) (hB : Formalism.ConjugateSelfDual.IsPlaceOver B v)
    (hN : ¬ ((N : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal))
    (s : Formalism.ConjugateSelfDual.G ℚ Ω) (hs : s ∈ ReciprocityTheory.Gal.Ine B) (ζ : Ω) (hζ : ζ ^ N = 1) : s ζ = ζ := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hN (by simpa using v.asIdeal.zero_mem)
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    simp [zero_pow hN0] at hζ
  have hwζ : B.valuation ζ = 1 := by
    have hp : B.valuation ζ ^ N = 1 := by rw [← map_pow, hζ, map_one]
    rcases lt_trichotomy (B.valuation ζ) 1 with hlt | heq | hgt
    · exact absurd hp (pow_lt_one₀ zero_le' hlt hN0).ne
    · exact heq
    · exact absurd hp (one_lt_pow₀ hgt hN0).ne'
  have hI := (ReciprocityTheory.Gal.mem_Ine.mp hs).2 ζ hwζ.le
  have hsζ : s ζ ^ N = 1 := by rw [← map_pow, hζ, map_one]
  have hone := eq_one_of_val_sub_lt B.valuation N ?_ (s ζ * ζ⁻¹) ?_ ?_
  · exact (mul_inv_eq_one₀ hζ0).mp hone
  · intro hlt
    exact hN ((hB N).mp (by simpa using hlt))
  · rw [mul_pow, hsζ, inv_pow, hζ, inv_one, mul_one]
  · have hr : s ζ * ζ⁻¹ - 1 = (s ζ - ζ) * ζ⁻¹ := by field_simp
    rw [hr, map_mul, map_inv₀, hwζ, inv_one, mul_one]
    exact hI

end GlobalTheory.InertiaRootOfUnity
