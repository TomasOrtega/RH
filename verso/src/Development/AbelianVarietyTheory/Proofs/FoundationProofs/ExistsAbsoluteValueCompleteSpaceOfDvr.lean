import Mathlib
open scoped NNReal TensorProduct

namespace GlobalTheory.KLC

open IsDedekindDomain

/- English proof (translation)
Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible R`. Establish `hinjK : Function.Injective (algebraMap R K)` using `IsFractionRing.injective R K`. Set `em : R →+* WithAbs f` to `(WithAbs.equiv f).symm.toRingHom.comp (algebraMap R K)`. Establish `hnorm : ∀ x : R, ‖em x‖ = f (algebraMap R K x)` using `fun x => rfl`. Establish `hinj : Function.Injective em` using `(WithAbs.equiv f).symm.injective.comp hinjK`.

Establish `hem0 : em π ≠ 0` using `(map_ne_zero_iff _ hinj).2 hπ.ne_zero`. Establish `hpos : 0 < ‖em π‖` using `norm_pos_iff.2 hem0`. Establish `hle : ∀ x, ‖em x‖ ≤ 1` using `fun x => (h _).2 ⟨x, rfl⟩`. Establish `key : ∀ (n : ℕ) (x : R), x ∈ IsLocalRing.maximalIdeal R ^ n ↔ ‖em x‖ ≤ ‖em π‖ ^ n`. Introduce `n x`.

Rewrite using `[hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Rewrite using `[map_mul, map_pow, norm_mul, norm_pow]`. Conclude with `mul_le_of_le_one_right (by positivity) (hle y)`.

Introduce `hx`. Rewrite `hx` using `[hnorm, hnorm]`. Establish `hπK : algebraMap R K π ≠ 0` using `(map_ne_zero_iff _ hinjK).2 hπ.ne_zero`. Take `⟨y, hy⟩` from `(h (algebraMap R K x / algebraMap R K π ^ n)).1 (by`. Rewrite using `[map_div₀, map_pow]`.

Conclude with `div_le_one_of_le₀ hx (by positivity))`. Use `⟨y, hinjK ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, hy, mul_div_cancel₀ _ (pow_ne_zero _ hπK)]`. Establish `hlt : ‖em π‖ < 1`. Assume the negation of the conclusion as `hge`.

Establish `: (1 : R) ∈ IsLocalRing.maximalIdeal R ^ 1` using `(key 1 1).2 (by simpa using hge)`. Rewrite `this` using `[pow_one]`. Conclude with `(IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 this)`. Use `Metric.complete_of_convergent_controlled_sequences (fun n => ‖em π‖ ^ n) (fun n => by positivity) ?_` and prove the remaining obligations. Introduce `u hu`.

Establish `hv : ∀ n, ∃ v : R, em v = u n - u 0`. Introduce `n`. Take `⟨v, hv⟩` from `(h ((u n - u 0).ofAbs)).1 (by`. Use `hu 0 n 0 (Nat.zero_le _) le_rfl` as an intermediate fact. Rewrite `this` using `[dist_eq_norm, pow_zero, WithAbs.norm_eq_apply_ofAbs]`.

Conclude with `this.le)`. Use `⟨v, ?_⟩` and prove the remaining obligations. Use `show WithAbs.toAbs f (algebraMap R K v) = _`. Rewrite using `[hv, WithAbs.toAbs_ofAbs]`. Use `choose v hv using hv`.

Take `⟨L, hL⟩` from `IsPrecomplete.prec (I := IsLocalRing.maximalIdeal R) (M := R) inferInstance (f := v) (by`. Introduce `m n hmn`. Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, key, map_sub, hv, hv, sub_sub_sub_cancel_right]`. Use `hu m m n le_rfl hmn` as an intermediate fact. Rewrite `this` using `[dist_eq_norm]`.

Conclude with `this.le)`. Use `⟨em L + u 0, ?_⟩` and prove the remaining obligations. Rewrite using `[tendsto_iff_dist_tendsto_zero]`. Use `squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) (tendsto_pow_atTop_nhds_zero_of_lt_one hpos.le hlt)` and prove the remaining obligations. Use `hL n` as an intermediate fact.

Rewrite `this` using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, key, map_sub, hv]`. Rewrite using `[dist_eq_norm]`. Establish `e : u n - (em L + u 0) = u n - u 0 - em L` using `by abel`. Rewrite using `[e]`. Conclude with `this`.
-/
theorem completeSpace_withAbs_of_unitBall (R K : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Field K]
    [Algebra R K] [IsFractionRing R K] (f : AbsoluteValue K ℝ)
    (h : ∀ x : K, f x ≤ 1 ↔ x ∈ Set.range (algebraMap R K)) :
    CompleteSpace (WithAbs f) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hinjK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  let em : R →+* WithAbs f := (WithAbs.equiv f).symm.toRingHom.comp (algebraMap R K)
  have hnorm : ∀ x : R, ‖em x‖ = f (algebraMap R K x) := fun x => rfl
  have hinj : Function.Injective em := (WithAbs.equiv f).symm.injective.comp hinjK
  have hem0 : em π ≠ 0 := (map_ne_zero_iff _ hinj).2 hπ.ne_zero
  have hpos : 0 < ‖em π‖ := norm_pos_iff.2 hem0
  have hle : ∀ x, ‖em x‖ ≤ 1 := fun x => (h _).2 ⟨x, rfl⟩
  have key : ∀ (n : ℕ) (x : R), x ∈ IsLocalRing.maximalIdeal R ^ n ↔ ‖em x‖ ≤ ‖em π‖ ^ n := by
    intro n x
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, rfl⟩
      rw [map_mul, map_pow, norm_mul, norm_pow]
      exact mul_le_of_le_one_right (by positivity) (hle y)
    · intro hx
      rw [hnorm, hnorm] at hx
      have hπK : algebraMap R K π ≠ 0 := (map_ne_zero_iff _ hinjK).2 hπ.ne_zero
      obtain ⟨y, hy⟩ := (h (algebraMap R K x / algebraMap R K π ^ n)).1 (by
        rw [map_div₀, map_pow]
        exact div_le_one_of_le₀ hx (by positivity))
      refine ⟨y, hinjK ?_⟩
      rw [map_mul, map_pow, hy, mul_div_cancel₀ _ (pow_ne_zero _ hπK)]
  have hlt : ‖em π‖ < 1 := by
    by_contra hge
    have : (1 : R) ∈ IsLocalRing.maximalIdeal R ^ 1 := (key 1 1).2 (by simpa using hge)
    rw [pow_one] at this
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 this)
  refine Metric.complete_of_convergent_controlled_sequences (fun n => ‖em π‖ ^ n)
    (fun n => by positivity) ?_
  intro u hu
  have hv : ∀ n, ∃ v : R, em v = u n - u 0 := by
    intro n
    obtain ⟨v, hv⟩ := (h ((u n - u 0).ofAbs)).1 (by
      have := hu 0 n 0 (Nat.zero_le _) le_rfl
      rw [dist_eq_norm, pow_zero, WithAbs.norm_eq_apply_ofAbs] at this
      exact this.le)
    refine ⟨v, ?_⟩
    show WithAbs.toAbs f (algebraMap R K v) = _
    rw [hv, WithAbs.toAbs_ofAbs]
  choose v hv using hv
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := IsLocalRing.maximalIdeal R) (M := R) inferInstance
    (f := v) (by
      intro m n hmn
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, key, map_sub, hv, hv,
        sub_sub_sub_cancel_right]
      have := hu m m n le_rfl hmn
      rw [dist_eq_norm] at this
      exact this.le)
  refine ⟨em L + u 0, ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hpos.le hlt)
  have := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, key, map_sub, hv] at this
  rw [dist_eq_norm]
  have e : u n - (em L + u 0) = u n - u 0 - em L := by abel
  rw [e]
  exact this

/- English proof (translation)
Introduce `R K _ _ _ _ _ _ _`. Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible R`. Set `v` to `IsDiscreteValuationRing.maximalIdeal R`. Establish `hb : (1 : ℝ≥0) < 2` using `one_lt_two`. Establish `hball : ∀ x : K, v.adicAbv hb x ≤ 1 ↔ x ∈ Set.range (algebraMap R K)`.

Introduce `x`. Establish `: v.adicAbv hb x ≤ 1 ↔ v.valuation K x ≤ 1`. Rewrite using `[← WithZeroMulInt.toNNReal_le_one_iff hb, ← NNReal.coe_le_coe]`. Both sides reduce to the same expression. Rewrite using `[this]`.

Conclude with `⟨IsDiscreteValuationRing.exists_lift_of_le_one, fun ⟨y, hy⟩ => hy ▸ v.valuation_le_one y⟩`. Use `⟨v.adicAbv hb, v.isNonarchimedean_adicAbv hb, ?_, hball, completeSpace_withAbs_of_unitBall R K _ hball⟩` and prove the remaining obligations. Establish `hπK : algebraMap R K π ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hπ.ne_zero`. Establish `h1 : v.valuation K (algebraMap R K π) < 1` using `(v.valuation_lt_one_iff_mem π).2 (show π ∈ IsLocalRing.maximalIdeal R from (IsLocalRing.mem_maximalIdeal π).2 hπ.not_isUnit)`. Establish `h2 : WithZeroMulInt.toNNReal (ne_zero_of_lt hb) (v.valuation K (algebraMap R K π)) < 1`.

Use `WithZeroMulInt.toNNReal_strictMono hb h1` as an intermediate fact. Rewrite `this` using `[map_one]`. Then use the resulting hypothesis. Use `⟨algebraMap R K π, hπK, ?_⟩` and prove the remaining obligations. Introduce `heq`. Establish `: ((WithZeroMulInt.toNNReal (ne_zero_of_lt hb) (v.valuation K (algebraMap R K π)) : ℝ≥0) : ℝ) = 1` using `heq`.

Conclude with `absurd (NNReal.coe_lt_coe.2 h2) (by rw [this]; simp)`.
-/
theorem exists_absoluteValue_completeSpace_of_isDiscreteValuationRing :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Field K] [Algebra R K]
      [IsFractionRing R K], ∃ f : AbsoluteValue K ℝ, IsNonarchimedean f ∧ f.IsNontrivial ∧
      (∀ x : K, f x ≤ 1 ↔ x ∈ Set.range (algebraMap R K)) ∧ CompleteSpace (WithAbs f) := by
  intro R K _ _ _ _ _ _ _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let v := IsDiscreteValuationRing.maximalIdeal R
  have hb : (1 : ℝ≥0) < 2 := one_lt_two
  have hball : ∀ x : K, v.adicAbv hb x ≤ 1 ↔ x ∈ Set.range (algebraMap R K) := by
    intro x
    have : v.adicAbv hb x ≤ 1 ↔ v.valuation K x ≤ 1 := by
      rw [← WithZeroMulInt.toNNReal_le_one_iff hb, ← NNReal.coe_le_coe]
      rfl
    rw [this]
    exact ⟨IsDiscreteValuationRing.exists_lift_of_le_one,
      fun ⟨y, hy⟩ => hy ▸ v.valuation_le_one y⟩
  refine ⟨v.adicAbv hb, v.isNonarchimedean_adicAbv hb, ?_, hball,
    completeSpace_withAbs_of_unitBall R K _ hball⟩
  have hπK : algebraMap R K π ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hπ.ne_zero
  have h1 : v.valuation K (algebraMap R K π) < 1 :=
    (v.valuation_lt_one_iff_mem π).2
      (show π ∈ IsLocalRing.maximalIdeal R from (IsLocalRing.mem_maximalIdeal π).2 hπ.not_isUnit)
  have h2 : WithZeroMulInt.toNNReal (ne_zero_of_lt hb) (v.valuation K (algebraMap R K π)) < 1 := by
    have := WithZeroMulInt.toNNReal_strictMono hb h1
    rwa [map_one] at this
  refine ⟨algebraMap R K π, hπK, ?_⟩
  intro heq
  have : ((WithZeroMulInt.toNNReal (ne_zero_of_lt hb) (v.valuation K (algebraMap R K π)) : ℝ≥0) : ℝ)
      = 1 := heq
  exact absurd (NNReal.coe_lt_coe.2 h2) (by rw [this]; simp)

end GlobalTheory.KLC
