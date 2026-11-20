import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hξA : A.valuation ξ ≤ 1`. Establish `: ξ = (ξ - 1) + 1` using `by ring`. Rewrite using `[this]`. Conclude with `(Valuation.map_add _ _ _).trans (max_le h1.le (by simp))`.

Establish `hS : (∑ k ∈ Finset.range n, ξ ^ k) = 0`. Establish `h` using `geom_sum_mul ξ n`. Rewrite `h` using `[hξ, sub_self]`. Break down `mul_eq_zero.mp h with h | h` into its components or cases. Conclude with `h`.

Conclude with `absurd (sub_eq_zero.mp h) hne`. Establish `hsum : (n : Ω) = ∑ k ∈ Finset.range n, (1 - ξ ^ k)`. Rewrite using `[Finset.sum_sub_distrib, hS]`. Simplify using the standard rewrite rules. Establish `hlt : A.valuation (n : Ω) < 1`.

Rewrite using `[hsum]`. Use `Valuation.map_sum_lt _ one_ne_zero fun k _ => ?_` and prove the remaining obligations. Establish `e : 1 - ξ ^ k = -((∑ j ∈ Finset.range k, ξ ^ j) * (ξ - 1))`. Rewrite using `[geom_sum_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, Valuation.map_neg, Valuation.map_mul]`. Establish `hs : A.valuation (∑ j ∈ Finset.range k, ξ ^ j) ≤ 1` using `Valuation.map_sum_le _ fun j _ => by rw [Valuation.map_pow]; exact pow_le_one' hξA j`. Combine the equalities or inequalities in the displayed calculation. Rewrite `hlt` using `[hn]`. Conclude with `lt_irrefl _ hlt`.
-/
theorem eq_one_of_pow_eq_one_of_val_sub_lt {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {n : ℕ}
    (hn : A.valuation (n : Ω) = 1) {ξ : Ω} (hξ : ξ ^ n = 1) (h1 : A.valuation (ξ - 1) < 1) : ξ = 1 := by
  by_contra hne
  have hξA : A.valuation ξ ≤ 1 := by
    have : ξ = (ξ - 1) + 1 := by ring
    rw [this]
    exact (Valuation.map_add _ _ _).trans (max_le h1.le (by simp))
  have hS : (∑ k ∈ Finset.range n, ξ ^ k) = 0 := by
    have h := geom_sum_mul ξ n
    rw [hξ, sub_self] at h
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hne
  have hsum : (n : Ω) = ∑ k ∈ Finset.range n, (1 - ξ ^ k) := by
    rw [Finset.sum_sub_distrib, hS]; simp
  have hlt : A.valuation (n : Ω) < 1 := by
    rw [hsum]
    refine Valuation.map_sum_lt _ one_ne_zero fun k _ => ?_
    have e : 1 - ξ ^ k = -((∑ j ∈ Finset.range k, ξ ^ j) * (ξ - 1)) := by
      rw [geom_sum_mul]; ring
    rw [e, Valuation.map_neg, Valuation.map_mul]
    have hs : A.valuation (∑ j ∈ Finset.range k, ξ ^ j) ≤ 1 :=
      Valuation.map_sum_le _ fun j _ => by rw [Valuation.map_pow]; exact pow_le_one' hξA j
    calc A.valuation (∑ j ∈ Finset.range k, ξ ^ j) * A.valuation (ξ - 1)
        ≤ 1 * A.valuation (ξ - 1) := by gcongr
      _ < 1 := by rw [one_mul]; exact h1
  rw [hn] at hlt
  exact lt_irrefl _ hlt

/- English proof (translation)
Establish `h : A.valuation ζ ^ n = 1` using `by rw [← Valuation.map_pow, hζ, Valuation.map_one]`. Conclude with `valuation_eq_one_of_pow_eq_one A hn0 hζ`.
-/
theorem val_eq_one_of_pow_eq_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {n : ℕ} (hn0 : n ≠ 0)
    {ζ : Ω} (hζ : ζ ^ n = 1) : A.valuation ζ = 1 := by
  have h : A.valuation ζ ^ n = 1 := by rw [← Valuation.map_pow, hζ, Valuation.map_one]
  exact valuation_eq_one_of_pow_eq_one A hn0 hζ

/- English proof (translation)
Introduce `E Ω _ _ _ _ v A hA w π hπ ρ hρ`. Use `set n := normV v - 1 with hn_def`. Break down `eq_or_ne n 0 with hn0 | hn0` into its components or cases. Rewrite using `[hn0, pow_zero]`. Both sides reduce to the same expression.

Break down `eq_or_ne π 0 with hπ0 | hπ0` into its components or cases. Rewrite using `[hπ0, map_zero]`. Establish `hq1 : 1 ≤ normV v` using `by omega`. Establish `hqv : ((normV v : ℕ) : 𝓞 E) ∈ v.asIdeal`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast]`.

Use `show ((Nat.card (𝓞 E ⧸ v.asIdeal) : ℕ) : 𝓞 E ⧸ v.asIdeal) = 0`. Break down `finite_or_infinite (𝓞 E ⧸ v.asIdeal) with hf | hf` into its components or cases. Use `haveI := Fintype.ofFinite (𝓞 E ⧸ v.asIdeal)`. Rewrite using `[Nat.card_eq_fintype_card]`. Conclude with `Nat.cast_card_eq_zero _`.

Rewrite using `[Nat.card_eq_zero_of_infinite]`. Simplify using the standard rewrite rules. Establish `hqA : A.valuation ((normV v : ℕ) : Ω) < 1`. Use `(hA _).mpr hqv` as an intermediate fact. Simplify using `using this`.

Establish `hnA : A.valuation (n : Ω) = 1`. Rewrite using `[hn_def, Nat.cast_sub hq1, Nat.cast_one, Valuation.map_sub_swap]`. Conclude with `Valuation.map_one_sub_of_lt _ hqA`. Establish `hρπ : (ρ π) ^ n = π ^ n`. Rewrite using `[← map_pow, hπ]`.

Conclude with `ρ.commutes w`. Use `set ζ := ρ π * π⁻¹ with hζ_def`. Establish `hζn : ζ ^ n = 1`. Rewrite using `[hζ_def, mul_pow, hρπ, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hπ0)]`. Establish `hρπ' : ρ π = ζ * π` using `by rw [hζ_def, mul_assoc, inv_mul_cancel₀ hπ0, mul_one]`.

Establish `hζ1 : A.valuation ζ = 1` using `valuation_eq_one_of_pow_eq_one A hn0 hζn`. Establish `hζ0 : ζ ≠ 0` using `by intro h; rw [h, zero_pow hn0] at hζn; exact zero_ne_one hζn`. Establish `hρζn : (ρ ζ) ^ n = 1` using `by rw [← map_pow, hζn, map_one]`. Establish `hclose : A.valuation (ρ ζ - ζ) < 1` using `hρ.2 ζ hζ1.le`. Establish `hξ : ρ ζ * ζ⁻¹ = 1`.

Use `eq_one_of_pow_eq_one_of_val_sub_lt A hnA ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_pow, hρζn, inv_pow, hζn, inv_one, one_mul]`. Establish `e : ρ ζ * ζ⁻¹ - 1 = (ρ ζ - ζ) * ζ⁻¹` using `by field_simp`. Rewrite using `[e, Valuation.map_mul, map_inv₀, hζ1, inv_one, mul_one]`. Conclude with `hclose`.

Establish `hρζ : ρ ζ = ζ`. Use `congrArg (· * ζ) hξ` as an intermediate fact. Simplify `this` using `[mul_assoc, inv_mul_cancel₀ hζ0]`. Establish `key : ∀ k : ℕ, (ρ ^ k) π = ζ ^ k * π`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, hρζ, hρπ', pow_succ]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[key, hζn, one_mul]`.
-/
theorem ine_pow_normV_sub_one_apply_of_pow_mem : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (v : HeightOneSpectrum (𝓞 E))
    (A : ValuationSubring Ω), IsPlaceOver A v → ∀ (w : E) (π : Ω), π ^ (normV v - 1) = algebraMap E Ω w →
    ∀ ρ ∈ Ine (F := E) A, (ρ ^ (normV v - 1)) π = π := by
  intro E Ω _ _ _ _ v A hA w π hπ ρ hρ
  set n := normV v - 1 with hn_def
  rcases eq_or_ne n 0 with hn0 | hn0
  · rw [hn0, pow_zero]; rfl
  rcases eq_or_ne π 0 with hπ0 | hπ0
  · rw [hπ0, map_zero]

  have hq1 : 1 ≤ normV v := by omega
  have hqv : ((normV v : ℕ) : 𝓞 E) ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    show ((Nat.card (𝓞 E ⧸ v.asIdeal) : ℕ) : 𝓞 E ⧸ v.asIdeal) = 0
    rcases finite_or_infinite (𝓞 E ⧸ v.asIdeal) with hf | hf
    · haveI := Fintype.ofFinite (𝓞 E ⧸ v.asIdeal)
      rw [Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero _
    · rw [Nat.card_eq_zero_of_infinite]; simp
  have hqA : A.valuation ((normV v : ℕ) : Ω) < 1 := by
    have := (hA _).mpr hqv
    simpa using this
  have hnA : A.valuation (n : Ω) = 1 := by
    rw [hn_def, Nat.cast_sub hq1, Nat.cast_one, Valuation.map_sub_swap]
    exact Valuation.map_one_sub_of_lt _ hqA

  have hρπ : (ρ π) ^ n = π ^ n := by
    rw [← map_pow, hπ]; exact ρ.commutes w
  set ζ := ρ π * π⁻¹ with hζ_def
  have hζn : ζ ^ n = 1 := by
    rw [hζ_def, mul_pow, hρπ, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hπ0)]
  have hρπ' : ρ π = ζ * π := by rw [hζ_def, mul_assoc, inv_mul_cancel₀ hπ0, mul_one]
  have hζ1 : A.valuation ζ = 1 := valuation_eq_one_of_pow_eq_one A hn0 hζn
  have hζ0 : ζ ≠ 0 := by intro h; rw [h, zero_pow hn0] at hζn; exact zero_ne_one hζn
  have hρζn : (ρ ζ) ^ n = 1 := by rw [← map_pow, hζn, map_one]
  have hclose : A.valuation (ρ ζ - ζ) < 1 := hρ.2 ζ hζ1.le
  have hξ : ρ ζ * ζ⁻¹ = 1 := by
    refine eq_one_of_pow_eq_one_of_val_sub_lt A hnA ?_ ?_
    · rw [mul_pow, hρζn, inv_pow, hζn, inv_one, one_mul]
    · have e : ρ ζ * ζ⁻¹ - 1 = (ρ ζ - ζ) * ζ⁻¹ := by field_simp
      rw [e, Valuation.map_mul, map_inv₀, hζ1, inv_one, mul_one]; exact hclose
  have hρζ : ρ ζ = ζ := by
    have := congrArg (· * ζ) hξ
    simpa [mul_assoc, inv_mul_cancel₀ hζ0] using this
  have key : ∀ k : ℕ, (ρ ^ k) π = ζ ^ k * π := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, hρζ, hρπ', pow_succ]; ring
  rw [key, hζn, one_mul]

end GlobalTheory
