import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory

/- English proof (translation)
Establish `hp : p.Prime` using `Fact.out`. Establish `hA0 : A ≠ 0` using `fun h => hnc ⟨0, by simp [h]⟩`. Take `⟨A₁, D₁, hA₁, hD₁, hu⟩` from `extract_gcd A D`. Establish `hcop : IsCoprime A₁ D₁` using `(gcd_isUnit_iff A₁ D₁).1 hu`. Generalize the expression as in `gcd A D = g at hA₁ hD₁`.

Substitute `hA₁ hD₁` using the available equality. Establish `hg : g ≠ 0` using `left_ne_zero_of_mul hD`. Establish `hD1 : D₁ ≠ 0` using `right_ne_zero_of_mul hD`. Establish `hA1 : A₁ ≠ 0` using `right_ne_zero_of_mul hA0`. Establish `h1 : derivative A₁ * D₁ = A₁ * derivative D₁`.

Establish `h2 : g ^ 2 * (derivative A₁ * D₁) = g ^ 2 * (A₁ * derivative D₁)`. Simplify using `only [derivative_mul] at hder`. Take the linear combination `hder`. Conclude with `mul_left_cancel₀ (pow_ne_zero 2 hg) h2`. Establish `hdvd : D₁ ∣ derivative D₁` using `hcop.symm.dvd_of_dvd_mul_left ⟨derivative A₁, by rw [← h1, mul_comm]⟩`.

Establish `hD' : derivative D₁ = 0`. Assume the negation of the conclusion as `hne`. Conclude with `absurd (degree_le_of_dvd hdvd hne) (not_le.2 (degree_derivative_lt hD1))`. Establish `hA' : derivative A₁ = 0`. Rewrite `h1` using `[hD', mul_zero]`.

Conclude with `(mul_eq_zero.1 h1).resolve_right hD1`. Rewrite `hA` using `[natDegree_mul hg hA1]`. Rewrite `hDp` using `[natDegree_mul hg hD1]`. Establish `eD` using `expand_contract p hD' hp.ne_zero`. Establish `eA` using `expand_contract p hA' hp.ne_zero`.

Establish `nD` using `natDegree_expand p (contract p D₁)`. Establish `nA` using `natDegree_expand p (contract p A₁)`. Rewrite `nD` using `[eD]`. Rewrite `nA` using `[eA]`. Establish `hD0 : D₁.natDegree = 0`.

Break down `Nat.eq_zero_or_pos (contract p D₁).natDegree with h | h` into its components or cases. Rewrite using `[nD, h, zero_mul]`. Use `Nat.le_mul_of_pos_left p h` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨d, rfl⟩` from `natDegree_eq_zero.1 hD0`.

Establish `hd : d ≠ 0`. Introduce and unpack `rfl`. Conclude with `hD1 (map_zero _)`. Establish `hm : (contract p A₁).natDegree = 1`. Break down `Nat.lt_trichotomy (contract p A₁).natDegree 1 with h | h | h` into its components or cases.

It suffices to derive a contradiction. Establish `h0 : (contract p A₁).natDegree = 0` using `by omega`. Rewrite `nA` using `[h0, zero_mul]`. Take `⟨a, rfl⟩` from `natDegree_eq_zero.1 nA`. Use `hnc ⟨a * d⁻¹, ?_⟩` and prove the remaining obligations.

Establish `: (C a : k[X]) = C (a * d⁻¹) * C d`. Rewrite using `[← map_mul, inv_mul_cancel_right₀ hd]`. Rewrite using `[this]`. Simplify using `only [map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `h`. It suffices to derive a contradiction. Establish `h2 : 2 * p ≤ (contract p A₁).natDegree * p` using `Nat.mul_le_mul_right p h`. Use `hp.pos` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Rewrite `nA` using `[hm, one_mul]`. Establish `hg0 : g.natDegree = 0` using `by omega`. Take `⟨γ, rfl⟩` from `natDegree_eq_zero.1 hg0`. Establish `hγ : γ ≠ 0`. Introduce and unpack `rfl`.

Conclude with `hg (map_zero _)`. Take `⟨a, ha, b, hab⟩` from `natDegree_eq_one.1 hm`. Use `⟨a * d⁻¹, b * d⁻¹, γ * d, mul_ne_zero ha (inv_ne_zero hd), mul_ne_zero hγ hd, (map_mul _ _ _).symm, ?_⟩` and prove the remaining obligations. Establish `hdd : (C d : k[X]) * C d⁻¹ = 1` using `by rw [← map_mul, mul_inv_cancel₀ hd, map_one]`. Rewrite using `[← eA, ← hab]`.

Simplify using `only [map_add, map_mul, expand_C, expand_X]`. Take the linear combination `(-(C γ * (C a * X ^ p + C b))) * hdd`.
-/
theorem quotient_eq_linear_pow_char_of_derivative_eq_zero
    (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (A D : k[X]) (hD : D ≠ 0)
    (hA : A.natDegree ≤ p) (hDp : D.natDegree < p)
    (hder : derivative A * D = A * derivative D) (hnc : ¬ ∃ c : k, A = C c * D) :
    ∃ a b c : k, a ≠ 0 ∧ c ≠ 0 ∧ D = C c ∧ A = C c * (C a * X ^ p + C b) := by
  classical
  have hp : p.Prime := Fact.out
  have hA0 : A ≠ 0 := fun h => hnc ⟨0, by simp [h]⟩
  obtain ⟨A₁, D₁, hA₁, hD₁, hu⟩ := extract_gcd A D
  have hcop : IsCoprime A₁ D₁ := (gcd_isUnit_iff A₁ D₁).1 hu
  generalize gcd A D = g at hA₁ hD₁
  subst hA₁ hD₁
  have hg : g ≠ 0 := left_ne_zero_of_mul hD
  have hD1 : D₁ ≠ 0 := right_ne_zero_of_mul hD
  have hA1 : A₁ ≠ 0 := right_ne_zero_of_mul hA0
  have h1 : derivative A₁ * D₁ = A₁ * derivative D₁ := by
    have h2 : g ^ 2 * (derivative A₁ * D₁) = g ^ 2 * (A₁ * derivative D₁) := by
      simp only [derivative_mul] at hder
      linear_combination hder
    exact mul_left_cancel₀ (pow_ne_zero 2 hg) h2
  have hdvd : D₁ ∣ derivative D₁ :=
    hcop.symm.dvd_of_dvd_mul_left ⟨derivative A₁, by rw [← h1, mul_comm]⟩
  have hD' : derivative D₁ = 0 := by
    by_contra hne
    exact absurd (degree_le_of_dvd hdvd hne) (not_le.2 (degree_derivative_lt hD1))
  have hA' : derivative A₁ = 0 := by
    rw [hD', mul_zero] at h1
    exact (mul_eq_zero.1 h1).resolve_right hD1
  rw [natDegree_mul hg hA1] at hA
  rw [natDegree_mul hg hD1] at hDp
  have eD := expand_contract p hD' hp.ne_zero
  have eA := expand_contract p hA' hp.ne_zero
  have nD := natDegree_expand p (contract p D₁)
  have nA := natDegree_expand p (contract p A₁)
  rw [eD] at nD
  rw [eA] at nA
  have hD0 : D₁.natDegree = 0 := by
    rcases Nat.eq_zero_or_pos (contract p D₁).natDegree with h | h
    · rw [nD, h, zero_mul]
    · have := Nat.le_mul_of_pos_left p h
      omega
  obtain ⟨d, rfl⟩ := natDegree_eq_zero.1 hD0
  have hd : d ≠ 0 := by
    rintro rfl
    exact hD1 (map_zero _)
  have hm : (contract p A₁).natDegree = 1 := by
    rcases Nat.lt_trichotomy (contract p A₁).natDegree 1 with h | h | h
    · exfalso
      have h0 : (contract p A₁).natDegree = 0 := by omega
      rw [h0, zero_mul] at nA
      obtain ⟨a, rfl⟩ := natDegree_eq_zero.1 nA
      refine hnc ⟨a * d⁻¹, ?_⟩
      have : (C a : k[X]) = C (a * d⁻¹) * C d := by
        rw [← map_mul, inv_mul_cancel_right₀ hd]
      rw [this]
      simp only [map_mul]
      ring
    · exact h
    · exfalso
      have h2 : 2 * p ≤ (contract p A₁).natDegree * p := Nat.mul_le_mul_right p h
      have := hp.pos
      omega
  rw [hm, one_mul] at nA
  have hg0 : g.natDegree = 0 := by omega
  obtain ⟨γ, rfl⟩ := natDegree_eq_zero.1 hg0
  have hγ : γ ≠ 0 := by
    rintro rfl
    exact hg (map_zero _)
  obtain ⟨a, ha, b, hab⟩ := natDegree_eq_one.1 hm
  refine ⟨a * d⁻¹, b * d⁻¹, γ * d, mul_ne_zero ha (inv_ne_zero hd), mul_ne_zero hγ hd,
    (map_mul _ _ _).symm, ?_⟩
  have hdd : (C d : k[X]) * C d⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hd, map_one]
  rw [← eA, ← hab]
  simp only [map_add, map_mul, expand_C, expand_X]
  linear_combination (-(C γ * (C a * X ^ p + C b))) * hdd

end GlobalTheory
