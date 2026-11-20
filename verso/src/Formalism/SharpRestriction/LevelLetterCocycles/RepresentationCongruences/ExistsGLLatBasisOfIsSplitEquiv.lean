import Mathlib

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.LTA

open PowerSeries

variable {O : Type*} [CommRing O]

/- English proof (translation)
Establish `e : (C a : O⟦X⟧) = algebraMap O O⟦X⟧ a` using `by first`. Consider the case `rfl`. Consider the case `simp`. Consider the case `(rw [PowerSeries.algebraMap_apply']; rfl)`. Rewrite using `[e, AlgHom.commutes]`.
-/
theorem alg_C (h : O⟦X⟧ →ₐ[O] O⟦X⟧) (a : O) : h (C a) = C a := by
  have e : (C a : O⟦X⟧) = algebraMap O O⟦X⟧ a := by
    first
    | rfl
    | simp
    | (rw [PowerSeries.algebraMap_apply']; rfl)
  rw [e, AlgHom.commutes]

/- English proof (translation)
Take `⟨m, hm⟩ : ∃ m : O⟦X⟧, k = m * X + C (constantCoeff k)` from `by first`. Consider the case `exact ⟨_, PowerSeries.eq_shift_mul_X_add_const k⟩`. Consider the case `exact ⟨PowerSeries.mk fun p => coeff (p + 1) k, by`. Apply the tactic sequence `ext n; rcases n with _ | n <;> simp [PowerSeries.coeff_succ_mul_X]⟩`. Rewrite using `[hm]`.

Simplify using `[hX, alg_C]`.
-/
theorem constantCoeff_alg (h : O⟦X⟧ →ₐ[O] O⟦X⟧) (hX : constantCoeff (h X) = 0) (k : O⟦X⟧) :
    constantCoeff (h k) = constantCoeff k := by
  obtain ⟨m, hm⟩ : ∃ m : O⟦X⟧, k = m * X + C (constantCoeff k) := by
    first
    | exact ⟨_, PowerSeries.eq_shift_mul_X_add_const k⟩
    | exact ⟨PowerSeries.mk fun p => coeff (p + 1) k, by
        ext n; rcases n with _ | n <;> simp [PowerSeries.coeff_succ_mul_X]⟩
  rw [hm]
  simp [hX, alg_C]

/- English proof (translation)
Use `⟨∑ i ∈ Finset.range l, x ^ i * y ^ (l - 1 - i), ?_, ?_⟩` and prove the remaining obligations. Simplify using `[map_sum, hx, hy]`. Use `first`. Consider the case `exact (geom_sum₂_mul x y l).symm`. Consider the case `exact ((Commute.all x y).geom_sum₂_mul l).symm`.
-/
private theorem exists_pow_sub_pow_eq_mul_sub_of_constantCoeff_eq_one (l : ℕ) (x y : O⟦X⟧)
    (hx : constantCoeff x = 1) (hy : constantCoeff y = 1) :
    ∃ S : O⟦X⟧, constantCoeff S = l ∧ x ^ l - y ^ l = S * (x - y) := by
  refine ⟨∑ i ∈ Finset.range l, x ^ i * y ^ (l - 1 - i), ?_, ?_⟩
  · simp [map_sum, hx, hy]
  · first
    | exact (geom_sum₂_mul x y l).symm
    | exact ((Commute.all x y).geom_sum₂_mul l).symm

/- English proof (translation)
Take `⟨S, hS, e⟩` from `exists_pow_sub_pow_eq_mul_sub_of_constantCoeff_eq_one l (1 + X : O⟦X⟧) 1 (by simp) (by simp)`. Conclude with `⟨S, hS, by linear_combination e⟩`.
-/
theorem exists_GL_latBasis_of_isSplitEquiv (l : ℕ) :
    ∃ Q0 : O⟦X⟧, constantCoeff Q0 = l ∧ (1 + X : O⟦X⟧) ^ l - 1 = X * Q0 := by
  obtain ⟨S, hS, e⟩ := exists_pow_sub_pow_eq_mul_sub_of_constantCoeff_eq_one l (1 + X : O⟦X⟧) 1 (by simp) (by simp)
  exact ⟨S, hS, by linear_combination e⟩

/- English proof (translation)
Take `⟨S, hS, e⟩` from `exists_pow_sub_pow_eq_mul_sub_of_constantCoeff_eq_one l (1 + a) (1 + b) (by simp [ha]) (by simp [hb])`. Conclude with `⟨S, hS, by linear_combination e⟩`.
-/
theorem exists_S (l : ℕ) (a b : O⟦X⟧) (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    ∃ S : O⟦X⟧, constantCoeff S = l ∧ ((1 + a) ^ l - 1) - ((1 + b) ^ l - 1) = S * (a - b) := by
  obtain ⟨S, hS, e⟩ := exists_pow_sub_pow_eq_mul_sub_of_constantCoeff_eq_one l (1 + a) (1 + b) (by simp [ha]) (by simp [hb])
  exact ⟨S, hS, by linear_combination e⟩

variable [IsDomain O] [CharZero O]

/- English proof (translation)
Rewrite using `[mul_comm]`. Simplify using `using PowerSeries.coeff_mul_X_pow f n 0`.
-/
private theorem coeff_X_pow_mul_eq_constantCoeff (n : ℕ) (f : O⟦X⟧) :
    coeff n (X ^ n * f) = constantCoeff f := by
  rw [mul_comm]
  simpa using PowerSeries.coeff_mul_X_pow f n 0

/- English proof (translation)
Establish `key : ∀ γ₁ : O⟦X⟧ →ₐ[O] O⟦X⟧, (∀ f, φ₀ (γ₁ f) = γ₁ (φ₀ f)) → φ₀ (γ₁ X) = (1 + γ₁ X) ^ l - 1`. Introduce `γ₁ hγ`. Rewrite using `[hγ, hφ₀]`. Simplify using `only [map_sub, map_pow, map_add, map_one]`. Assume the negation of the conclusion as `hne`.

Establish `hd : γ X - γ' X ≠ 0` using `sub_ne_zero.mpr hne`. Take `⟨S, hS, hSe⟩` from `exists_S l (γ X) (γ' X) h0 h0'`. Establish `hφd : φ₀ (γ X - γ' X) = S * (γ X - γ' X)`. Rewrite using `[map_sub, key γ hc, key γ' hc']`. Conclude with `hSe`.

Establish `hex : ∃ m, coeff m (γ X - γ' X) ≠ 0`. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`. Conclude with `hd (PowerSeries.ext fun m => by rw [hall m, map_zero])`. Take `⟨n, hn, hmin⟩ : ∃ n, coeff n (γ X - γ' X) ≠ 0 ∧ ∀ m < n, coeff m (γ X - γ' X) = 0` from `⟨Nat.find hex, Nat.find_spec hex, fun m hm => by`.

Assume the negation of the conclusion as `hcm`. Conclude with `Nat.find_min hex hm hcm⟩`. Establish `hc0 : coeff 0 (γ X - γ' X) = 0`. Rewrite using `[map_sub]`. Simplify using `[h0, h0']`.

Establish `hc1 : coeff 1 (γ X - γ' X) = 0`. Rewrite using `[map_sub, h1, sub_self]`. Establish `hn2 : 2 ≤ n`. Assume the negation of the conclusion as `hlt2`. Use `push_neg at hlt2`.

Use `interval_cases n`. Conclude with `hn hc0`. Conclude with `hn hc1`. Take `⟨u, hu⟩` from `PowerSeries.X_pow_dvd_iff.mpr hmin`. Establish `hu0 : constantCoeff u = coeff n (γ X - γ' X)`.

Rewrite using `[hu, coeff_X_pow_mul_eq_constantCoeff]`. Take `⟨Q0, hQ0, hQe⟩` from `exists_GL_latBasis_of_isSplitEquiv (O := O) l`. Establish `hφX : φ₀ X = X * Q0` using `by rw [hφ₀, hQe]`. Establish `hcX : constantCoeff (φ₀ X) = 0`. Rewrite using `[hφX]`.

Simplify using the standard rewrite rules. Establish `lhs : coeff n (φ₀ (γ X - γ' X)) = (l : O) ^ n * constantCoeff u`. Rewrite using `[hu, map_mul, map_pow, hφX, mul_pow, mul_assoc, coeff_X_pow_mul_eq_constantCoeff, map_mul, map_pow, hQ0, constantCoeff_alg φ₀ hcX]`. Establish `rhs : coeff n (S * (γ X - γ' X)) = (l : O) * constantCoeff u`. Rewrite using `[hu, mul_left_comm, coeff_X_pow_mul_eq_constantCoeff, map_mul, hS]`.

Establish `heq : (l : O) ^ n * constantCoeff u = (l : O) * constantCoeff u`. Rewrite using `[← lhs, ← rhs, hφd]`. Establish `hcu : constantCoeff u ≠ 0`. Rewrite using `[hu0]`. Conclude with `hn`.

Establish `hpow : (l : O) ^ n = l` using `mul_right_cancel₀ hcu heq`. Establish `hnat : l ^ n = l` using `by exact_mod_cast hpow`. Establish `hl2 : 2 ≤ l` using `hp.out.two_le`. Establish `hle : l ^ 2 ≤ l ^ n` using `Nat.pow_le_pow_right (by omega) hn2`. Rewrite `hle` using `[hnat]`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem lt_unique (l : ℕ) [hp : Fact l.Prime]
    (φ₀ γ γ' : O⟦X⟧ →ₐ[O] O⟦X⟧) (hφ₀ : φ₀ X = (1 + X) ^ l - 1)
    (hc : ∀ f, φ₀ (γ f) = γ (φ₀ f)) (hc' : ∀ f, φ₀ (γ' f) = γ' (φ₀ f))
    (h0 : constantCoeff (γ X) = 0) (h0' : constantCoeff (γ' X) = 0)
    (h1 : coeff 1 (γ X) = coeff 1 (γ' X)) :
    γ X = γ' X := by
  classical
  have key : ∀ γ₁ : O⟦X⟧ →ₐ[O] O⟦X⟧, (∀ f, φ₀ (γ₁ f) = γ₁ (φ₀ f)) →
      φ₀ (γ₁ X) = (1 + γ₁ X) ^ l - 1 := by
    intro γ₁ hγ
    rw [hγ, hφ₀]
    simp only [map_sub, map_pow, map_add, map_one]
  by_contra hne
  have hd : γ X - γ' X ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨S, hS, hSe⟩ := exists_S l (γ X) (γ' X) h0 h0'
  have hφd : φ₀ (γ X - γ' X) = S * (γ X - γ' X) := by
    rw [map_sub, key γ hc, key γ' hc']
    exact hSe
  have hex : ∃ m, coeff m (γ X - γ' X) ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hd (PowerSeries.ext fun m => by rw [hall m, map_zero])
  obtain ⟨n, hn, hmin⟩ : ∃ n, coeff n (γ X - γ' X) ≠ 0 ∧ ∀ m < n, coeff m (γ X - γ' X) = 0 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => by
      by_contra hcm
      exact Nat.find_min hex hm hcm⟩
  have hc0 : coeff 0 (γ X - γ' X) = 0 := by
    rw [map_sub]
    simp [h0, h0']
  have hc1 : coeff 1 (γ X - γ' X) = 0 := by
    rw [map_sub, h1, sub_self]
  have hn2 : 2 ≤ n := by
    by_contra hlt2
    push_neg at hlt2
    interval_cases n
    · exact hn hc0
    · exact hn hc1
  obtain ⟨u, hu⟩ := PowerSeries.X_pow_dvd_iff.mpr hmin
  have hu0 : constantCoeff u = coeff n (γ X - γ' X) := by
    rw [hu, coeff_X_pow_mul_eq_constantCoeff]
  obtain ⟨Q0, hQ0, hQe⟩ := exists_GL_latBasis_of_isSplitEquiv (O := O) l
  have hφX : φ₀ X = X * Q0 := by rw [hφ₀, hQe]
  have hcX : constantCoeff (φ₀ X) = 0 := by
    rw [hφX]
    simp
  have lhs : coeff n (φ₀ (γ X - γ' X)) = (l : O) ^ n * constantCoeff u := by
    rw [hu, map_mul, map_pow, hφX, mul_pow, mul_assoc, coeff_X_pow_mul_eq_constantCoeff, map_mul, map_pow,
      hQ0, constantCoeff_alg φ₀ hcX]
  have rhs : coeff n (S * (γ X - γ' X)) = (l : O) * constantCoeff u := by
    rw [hu, mul_left_comm, coeff_X_pow_mul_eq_constantCoeff, map_mul, hS]
  have heq : (l : O) ^ n * constantCoeff u = (l : O) * constantCoeff u := by
    rw [← lhs, ← rhs, hφd]
  have hcu : constantCoeff u ≠ 0 := by
    rw [hu0]
    exact hn
  have hpow : (l : O) ^ n = l := mul_right_cancel₀ hcu heq
  have hnat : l ^ n = l := by exact_mod_cast hpow
  have hl2 : 2 ≤ l := hp.out.two_le
  have hle : l ^ 2 ≤ l ^ n := Nat.pow_le_pow_right (by omega) hn2
  rw [hnat] at hle
  nlinarith

end Formalism.MainNotions.N.FrobeniusPowerSeries.LTA
