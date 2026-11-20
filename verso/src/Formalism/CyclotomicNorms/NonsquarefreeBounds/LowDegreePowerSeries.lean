import Formalism.CyclotomicNorms.DiscardKernel

open PowerSeries

noncomputable section

namespace Formalism.CyclotomicNorms

/- English proof (translation)
Establish `hU : (U : R) * ↑U⁻¹ = 1` using `U.mul_inv`. Establish `h1 : x ^ m * y = (-(p * D' * ↑U⁻¹)) * y`. Take the linear combination `(↑U⁻¹ : R) * hD - (x ^ m * y) * hU`. Establish `h2 : ∀ k : ℕ, x ^ (m * k) * y = (-(p * D' * ↑U⁻¹)) ^ k * y`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h2 n]`.

Establish `: (-(p * D' * ↑U⁻¹)) ^ n = (-(D' * ↑U⁻¹)) ^ n * p ^ n` using `by ring`. Rewrite using `[this, hp]`. Simplify using the standard rewrite rules.
-/
theorem low_key {R : Type*} [CommRing R] (x p D' y : R) (U : Rˣ) (m n : ℕ)
    (hp : p ^ n = 0) (hD : (x ^ m * U + p * D') * y = 0) : x ^ (m * n) * y = 0 := by
  have hU : (U : R) * ↑U⁻¹ = 1 := U.mul_inv
  have h1 : x ^ m * y = (-(p * D' * ↑U⁻¹)) * y := by
    linear_combination (↑U⁻¹ : R) * hD - (x ^ m * y) * hU
  have h2 : ∀ k : ℕ, x ^ (m * k) * y = (-(p * D' * ↑U⁻¹)) ^ k * y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc x ^ (m * (k + 1)) * y = x ^ (m * k) * (x ^ m * y) := by ring
        _ = (-(p * D' * ↑U⁻¹)) * (x ^ (m * k) * y) := by rw [h1]; ring
        _ = (-(p * D' * ↑U⁻¹)) ^ (k + 1) * y := by rw [ih]; ring
  rw [h2 n]
  have : (-(p * D' * ↑U⁻¹)) ^ n = (-(D' * ↑U⁻¹)) ^ n * p ^ n := by ring
  rw [this, hp]
  simp

/- English proof (translation)
Take `⟨u, v, rfl⟩` from `Ideal.mem_span_pair.mp hf`. Rewrite using `[map_add, mul_comm u, coeff_C_mul, mul_comm v, coeff_X_pow_mul', if_neg (by omega), add_zero]`. Conclude with `dvd_mul_right a _`.
-/
theorem low_coeff_dvd {O : Type*} [CommRing O] (a : O) (M : ℕ) (f : PowerSeries O)
    (hf : f ∈ Ideal.span {PowerSeries.C a, (PowerSeries.X : PowerSeries O) ^ (M + 1)})
    (k : ℕ) (hk : k ≤ M) : a ∣ coeff k f := by
  obtain ⟨u, v, rfl⟩ := Ideal.mem_span_pair.mp hf
  rw [map_add, mul_comm u, coeff_C_mul, mul_comm v, coeff_X_pow_mul', if_neg (by omega), add_zero]
  exact dvd_mul_right a _

/- English proof (translation)
Use `⟨mk fun k => (h k).choose, ?_⟩` and prove the remaining obligations. Use extensionality with `k`. Rewrite using `[coeff_C_mul, coeff_mk]`. Conclude with `(h k).choose_spec`.
-/
theorem low_divide {O : Type*} [CommRing O] (a : O) (f : PowerSeries O)
    (h : ∀ k, a ∣ coeff k f) : ∃ f', f = C a * f' := by
  refine ⟨mk fun k => (h k).choose, ?_⟩
  ext k
  rw [coeff_C_mul, coeff_mk]
  exact (h k).choose_spec

/- English proof (translation)
Introduce `O _ _ _ ϖ n m₀ D g hϖ hord hg hmem`. Use `set Db := PowerSeries.map (IsLocalRing.residue O) D with hDb`. Establish `hne : Db ≠ 0`. Introduce `h`. Rewrite `hord` using `[h, order_zero]`.

Conclude with `absurd hord (by simp)`. Use `set m := Db.order.toNat with hm`. Establish `hmm : m ≤ m₀`. Use `coe_toNat_order hne` as an intermediate fact. Rewrite `hord` using `[← this]`.

Conclude with `hord` after adjusting the coercions. Use `set U : PowerSeries O := mk fun k => coeff (m + k) D with hU`. Establish `hUunit : IsUnit U`. Rewrite using `[isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply, hU, coeff_mk, add_zero, ← IsLocalRing.residue_ne_zero_iff_isUnit]`. Use `coeff_order hne` as an intermediate fact.

Rewrite `this` using `[hDb, coeff_map]`. Then use the resulting hypothesis. Establish `hdiv : ∀ k, ϖ ∣ coeff k (D - X ^ m * U)`. Introduce `k`. Rewrite using `[map_sub, coeff_X_pow_mul']`. Use `split_ifs with hk`.

Rewrite using `[hU, coeff_mk, Nat.add_sub_cancel' hk, sub_self]`. Conclude with `dvd_zero _`. Rewrite using `[sub_zero, ← Ideal.mem_span_singleton, ← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, ← IsLocalRing.residue_eq_zero_iff, ← coeff_map]`. Conclude with `coeff_of_lt_order_toNat (φ := Db) k (by omega)`. Take `⟨D', hD'⟩` from `low_divide ϖ _ hdiv`.

Establish `hDeq : D = X ^ m * U + C ϖ * D'` using `by rw [← hD']; ring`. Use `set I := Ideal.span {PowerSeries.C (ϖ ^ n), (PowerSeries.X : PowerSeries O) ^ (n * m₀ + 1)} with hI`. Set `q` to `Ideal.Quotient.mk I`. Establish `hp : (q (C ϖ)) ^ n = 0`. Rewrite using `[← map_pow, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `Ideal.subset_span (Set.mem_insert _ _)`. Establish `h0 : (q X ^ m * ↑((hUunit.map q).unit) + q (C ϖ) * q D') * q g = 0`. Establish `h` using `Ideal.Quotient.eq_zero_iff_mem.mpr hmem`. Rewrite `h` using `[hDeq]`. Simplify `h` using `[map_mul, map_add, map_pow]`.

Establish `h3` using `low_key _ _ _ _ _ m n hp h0`. Rewrite `h3` using `[← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]`. Establish `hmn : m * n ≤ n * m₀`. Rewrite using `[mul_comm]`. Conclude with `Nat.mul_le_mul_left n hmm`.

Use `low_coeff_dvd (ϖ ^ n) (n * m₀) _ h3 (m * n) hmn` as an intermediate fact. Rewrite `this` using `[coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply]`. Conclude with `hg (Ideal.mem_span_singleton.mpr this)`.
-/
theorem low_degree_power_series : LowPowerSeries := by
  intro O _ _ _ ϖ n m₀ D g hϖ hord hg hmem
  set Db := PowerSeries.map (IsLocalRing.residue O) D with hDb
  have hne : Db ≠ 0 := by
    intro h
    rw [h, order_zero] at hord
    exact absurd hord (by simp)
  set m := Db.order.toNat with hm
  have hmm : m ≤ m₀ := by
    have := coe_toNat_order hne
    rw [← this] at hord
    exact_mod_cast hord
  set U : PowerSeries O := mk fun k => coeff (m + k) D with hU
  have hUunit : IsUnit U := by
    rw [isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply, hU, coeff_mk, add_zero,
      ← IsLocalRing.residue_ne_zero_iff_isUnit]
    have := coeff_order hne
    rwa [hDb, coeff_map] at this
  have hdiv : ∀ k, ϖ ∣ coeff k (D - X ^ m * U) := by
    intro k
    rw [map_sub, coeff_X_pow_mul']
    split_ifs with hk
    · rw [hU, coeff_mk, Nat.add_sub_cancel' hk, sub_self]
      exact dvd_zero _
    · rw [sub_zero, ← Ideal.mem_span_singleton,
        ← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
        ← IsLocalRing.residue_eq_zero_iff, ← coeff_map]
      exact coeff_of_lt_order_toNat (φ := Db) k (by omega)
  obtain ⟨D', hD'⟩ := low_divide ϖ _ hdiv
  have hDeq : D = X ^ m * U + C ϖ * D' := by rw [← hD']; ring
  set I := Ideal.span {PowerSeries.C (ϖ ^ n), (PowerSeries.X : PowerSeries O) ^ (n * m₀ + 1)}
    with hI
  let q := Ideal.Quotient.mk I
  have hp : (q (C ϖ)) ^ n = 0 := by
    rw [← map_pow, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_insert _ _)
  have h0 : (q X ^ m * ↑((hUunit.map q).unit) + q (C ϖ) * q D') * q g = 0 := by
    have h := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [hDeq] at h
    simpa [map_mul, map_add, map_pow] using h
  have h3 := low_key _ _ _ _ _ m n hp h0
  rw [← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at h3
  have hmn : m * n ≤ n * m₀ := by
    rw [mul_comm]
    exact Nat.mul_le_mul_left n hmm
  have := low_coeff_dvd (ϖ ^ n) (n * m₀) _ h3 (m * n) hmn
  rw [coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply] at this
  exact hg (Ideal.mem_span_singleton.mpr this)

end Formalism.CyclotomicNorms
