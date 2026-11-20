import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesVecReduceModUMulVec

noncomputable section

namespace PositivityTheory.CompleteLocalMinorRing.Minor

open PowerSeries GlobalTheory.BK Filter Topology

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K]

omit [IsUltrametricDist K] in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, rfl⟩`. Rewrite using `[map_mul, norm_mul]`. Conclude with `mul_le_of_le_one_right (norm_nonneg _) (norm_algebraMap_le c)`. Introduce `h`.

Take `⟨c, hc⟩` from `(IsUnitBall.mem_range_iff (O := O) (algebraMap O K x / algebraMap O K y)).2 (by`. Rewrite using `[norm_div]`. Conclude with `div_le_one_of_le₀ h (norm_nonneg _))`. Use `⟨c, IsUnitBall.inj (O := O) (K := K) ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hc, mul_div_cancel₀ _ hy]`.
-/
theorem dvd_iff_norm {x y : O} (hy : algebraMap O K y ≠ 0) :
    y ∣ x ↔ ‖algebraMap O K x‖ ≤ ‖algebraMap O K y‖ := by
  constructor
  · rintro ⟨c, rfl⟩
    rw [map_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_algebraMap_le c)
  · intro h
    obtain ⟨c, hc⟩ := (IsUnitBall.mem_range_iff (O := O)
      (algebraMap O K x / algebraMap O K y)).2 (by
        rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _))
    refine ⟨c, IsUnitBall.inj (O := O) (K := K) ?_⟩
    rw [map_mul, hc, mul_div_cancel₀ _ hy]

omit [IsUltrametricDist K] in
/- English proof (translation)
Rewrite using `[isUnit_iff_dvd_one]`. Distinguish the cases in `hx : algebraMap O K x = 0`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc⟩`. Use `congrArg (algebraMap O K) hc` as an intermediate fact.

Rewrite `this` using `[map_mul, hx, zero_mul, map_one]`. Conclude with `absurd this one_ne_zero`. Introduce `h`. Rewrite `h` using `[hx, norm_zero]`. Conclude with `absurd h zero_ne_one`.

Rewrite using `[dvd_iff_norm hx, map_one, norm_one]`. Conclude with `⟨fun h => le_antisymm (norm_algebraMap_le x) h, fun h => h.ge⟩`.
-/
theorem isUnit_iff_norm {x : O} : IsUnit x ↔ ‖algebraMap O K x‖ = 1 := by
  rw [isUnit_iff_dvd_one]
  by_cases hx : algebraMap O K x = 0
  · constructor
    · rintro ⟨c, hc⟩
      have := congrArg (algebraMap O K) hc
      rw [map_mul, hx, zero_mul, map_one] at this
      exact absurd this one_ne_zero
    · intro h
      rw [hx, norm_zero] at h
      exact absurd h zero_ne_one
  · rw [dvd_iff_norm hx, map_one, norm_one]
    exact ⟨fun h => le_antisymm (norm_algebraMap_le x) h, fun h => h.ge⟩

variable (O K) in
include K in
/- English proof (translation)
Establish `: Nontrivial O` using `(algebraMap O K).domain_nontrivial`. Use `IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_` and prove the remaining obligations. Rewrite using `[isUnit_iff_norm (K := K), isUnit_iff_norm (K := K)]`. Assume the negation of the conclusion as `h`. Use `push Not at h`.

Establish `h1` using `lt_of_le_of_ne (norm_algebraMap_le (K := K) x) h.1`. Establish `h2` using `lt_of_le_of_ne (norm_algebraMap_le (K := K) (1 - x)) h.2`. Establish `h3` using `IsUltrametricDist.norm_add_le_max (algebraMap O K x) (algebraMap O K (1 - x))`. Rewrite `h3` using `[← map_add, add_sub_cancel, map_one, norm_one]`. Conclude with `absurd (h3.trans_lt (max_lt h1 h2)) (lt_irrefl _)`.
-/
theorem isLocalRing : IsLocalRing O := by
  have : Nontrivial O := (algebraMap O K).domain_nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  rw [isUnit_iff_norm (K := K), isUnit_iff_norm (K := K)]
  by_contra h
  push Not at h
  have h1 := lt_of_le_of_ne (norm_algebraMap_le (K := K) x) h.1
  have h2 := lt_of_le_of_ne (norm_algebraMap_le (K := K) (1 - x)) h.2
  have h3 := IsUltrametricDist.norm_add_le_max (algebraMap O K x) (algebraMap O K (1 - x))
  rw [← map_add, add_sub_cancel, map_one, norm_one] at h3
  exact absurd (h3.trans_lt (max_lt h1 h2)) (lt_irrefl _)

omit [IsUltrametricDist K] in
/- English proof (translation)
Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_norm (K := K)]`. Conclude with `⟨fun h => lt_of_le_of_ne (norm_algebraMap_le x) h, fun h => h.ne⟩`.
-/
theorem mem_max_iff [IsLocalRing O] {x : O} :
    x ∈ IsLocalRing.maximalIdeal O ↔ ‖algebraMap O K x‖ < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_norm (K := K)]
  exact ⟨fun h => lt_of_le_of_ne (norm_algebraMap_le x) h, fun h => h.ne⟩

omit [IsUltrametricDist K] in
/- English proof (translation)
Establish `hmem : ∀ (n : ℕ) (x : O), x ∈ (Ideal.span {c} ^ n • ⊤ : Submodule O O) ↔ ‖algebraMap O K x‖ ≤ ‖algebraMap O K c‖ ^ n`. Introduce `n x`. Rewrite using `[smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton, dvd_iff_norm (K := K) (by rw [map_pow]; exact pow_ne_zero _ h0), map_pow, norm_pow]`. Establish `hlim` using `tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (algebraMap O K c)) h1`. Establish `: IsHausdorff (Ideal.span {c}) O` using `⟨fun x hx => by`.

Apply `IsUnitBall.inj (O := O) (K := K)` to reduce the goal to its premises. Rewrite using `[map_zero, ← norm_le_zero_iff]`. Use `ge_of_tendsto' hlim fun n => ?_` and prove the remaining obligations. Use `hx n` as an intermediate fact. Rewrite using `[SModEq.zero, hmem] at this⟩` and apply the resulting hypothesis.

Establish `: IsPrecomplete (Ideal.span {c}) O` using `⟨fun f hf => by`. Establish `hd : ∀ m n, m ≤ n → ‖algebraMap O K (f m) - algebraMap O K (f n)‖ ≤ ‖algebraMap O K c‖ ^ m` using `fun m n h => by`. Use `hf h` as an intermediate fact. Rewrite `this` using `[SModEq.sub_mem, hmem, map_sub]`. Then use the resulting hypothesis. Establish `hc : CauchySeq fun n => algebraMap O K (f n)` using `cauchySeq_of_le_tendsto_0' _ (fun m n h => by rw [dist_eq_norm]; exact hd m n h) hlim`.

Take `⟨y, hy⟩` from `cauchySeq_tendsto_of_complete hc`. Take `⟨L, hL⟩` from `(IsUnitBall.mem_range_iff (O := O) y).2 (le_of_tendsto' hy.norm fun n => norm_algebraMap_le _)`. Use `⟨L, fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[SModEq.sub_mem, hmem, map_sub, hL]`. Use `le_of_tendsto (hy.const_sub (algebraMap O K (f n))).norm ?_` and prove the remaining obligations.

Conclude with `eventually_atTop.2 ⟨n, fun m hm => hd n m hm⟩⟩`. Conclude with `{}`.
-/
theorem isAdicComplete_span [CompleteSpace K] {c : O} (h0 : algebraMap O K c ≠ 0)
    (h1 : ‖algebraMap O K c‖ < 1) : IsAdicComplete (Ideal.span {c}) O := by
  have hmem : ∀ (n : ℕ) (x : O), x ∈ (Ideal.span {c} ^ n • ⊤ : Submodule O O) ↔
      ‖algebraMap O K x‖ ≤ ‖algebraMap O K c‖ ^ n := by
    intro n x
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
      dvd_iff_norm (K := K) (by rw [map_pow]; exact pow_ne_zero _ h0), map_pow, norm_pow]
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (algebraMap O K c)) h1
  have : IsHausdorff (Ideal.span {c}) O := ⟨fun x hx => by
    apply IsUnitBall.inj (O := O) (K := K)
    rw [map_zero, ← norm_le_zero_iff]
    refine ge_of_tendsto' hlim fun n => ?_
    have := hx n
    rwa [SModEq.zero, hmem] at this⟩
  have : IsPrecomplete (Ideal.span {c}) O := ⟨fun f hf => by
    have hd : ∀ m n, m ≤ n → ‖algebraMap O K (f m) - algebraMap O K (f n)‖ ≤
        ‖algebraMap O K c‖ ^ m := fun m n h => by
      have := hf h
      rwa [SModEq.sub_mem, hmem, map_sub] at this
    have hc : CauchySeq fun n => algebraMap O K (f n) :=
      cauchySeq_of_le_tendsto_0' _ (fun m n h => by rw [dist_eq_norm]; exact hd m n h) hlim
    obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hc
    obtain ⟨L, hL⟩ := (IsUnitBall.mem_range_iff (O := O) y).2
      (le_of_tendsto' hy.norm fun n => norm_algebraMap_le _)
    refine ⟨L, fun n => ?_⟩
    rw [SModEq.sub_mem, hmem, map_sub, hL]
    refine le_of_tendsto (hy.const_sub (algebraMap O K (f n))).norm ?_
    exact eventually_atTop.2 ⟨n, fun m hm => hd n m hm⟩⟩
  exact {}

variable (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]

include K l in
/- English proof (translation)
Establish `: ProperSpace K` using `FiniteDimensional.proper ℚ_[l] K`. Establish `hc : IsCompact (Metric.ball (0 : K) 1)` using `(isCompact_closedBall (0 : K) 1).of_isClosed_subset (IsUltrametricDist.isClosed_ball _ _) Metric.ball_subset_closedBall`. Take `⟨y, hy, hmax⟩` from `hc.exists_isMaxOn ⟨0, by simp⟩ continuous_norm.continuousOn`. Rewrite `hy` using `[mem_ball_zero_iff]`. Take `⟨c, rfl⟩` from `(IsUnitBall.mem_range_iff (O := O) y).2 hy.le`.

Establish `h0 : algebraMap O K c ≠ 0`. Establish `: ‖(l : K)‖ ≤ ‖algebraMap O K c‖` using `hmax (mem_ball_zero_iff.2 (norm_l_lt_one l))`. Conclude with `norm_pos_iff.1 ((norm_pos_iff.2 (l_ne_zero l)).trans_le this)`. Establish `: IsLocalRing.maximalIdeal O = Ideal.span {c}`. Use extensionality with `x`.

Rewrite using `[mem_max_iff (K := K), Ideal.mem_span_singleton, dvd_iff_norm h0]`. Conclude with `⟨fun h => hmax (mem_ball_zero_iff.2 h), fun h => h.trans_lt hy⟩`. Rewrite using `[this]`. Conclude with `isAdicComplete_span h0 hy`.
-/
theorem isAdicComplete_max [CompleteSpace K] [FiniteDimensional ℚ_[l] K] [IsLocalRing O] :
    IsAdicComplete (IsLocalRing.maximalIdeal O) O := by
  have : ProperSpace K := FiniteDimensional.proper ℚ_[l] K
  have hc : IsCompact (Metric.ball (0 : K) 1) :=
    (isCompact_closedBall (0 : K) 1).of_isClosed_subset (IsUltrametricDist.isClosed_ball _ _)
      Metric.ball_subset_closedBall
  obtain ⟨y, hy, hmax⟩ := hc.exists_isMaxOn ⟨0, by simp⟩ continuous_norm.continuousOn
  rw [mem_ball_zero_iff] at hy
  obtain ⟨c, rfl⟩ := (IsUnitBall.mem_range_iff (O := O) y).2 hy.le
  have h0 : algebraMap O K c ≠ 0 := by
    have : ‖(l : K)‖ ≤ ‖algebraMap O K c‖ := hmax (mem_ball_zero_iff.2 (norm_l_lt_one l))
    exact norm_pos_iff.1 ((norm_pos_iff.2 (l_ne_zero l)).trans_le this)
  have : IsLocalRing.maximalIdeal O = Ideal.span {c} := by
    ext x
    rw [mem_max_iff (K := K), Ideal.mem_span_singleton, dvd_iff_norm h0]
    exact ⟨fun h => hmax (mem_ball_zero_iff.2 h), fun h => h.trans_lt hy⟩
  rw [this]
  exact isAdicComplete_span h0 hy

omit [IsUltrametricDist K] in
/- English proof (translation)
Introduce `c hc`. Rewrite `hc` using `[mem_max_iff (K := K)]`. Take `⟨n, hn⟩` from `exists_pow_lt_of_lt_one (norm_pos_iff.2 (l_ne_zero (K := K) l)) hc`. Use `⟨n, (dvd_iff_norm (K := K) (by rw [map_natCast]; exact l_ne_zero l)).2 ?_⟩` and prove the remaining obligations. Rewrite using `[map_pow, norm_pow, map_natCast]`.

Conclude with `hn.le`.
-/
theorem l_dvd_pow [IsLocalRing O] (K : Type) [NormedField K] [Algebra O K] [IsUnitBall O K]
    [NormedAlgebra ℚ_[l] K] : ∀ c ∈ IsLocalRing.maximalIdeal O, ∃ n : ℕ, (l : O) ∣ c ^ n := by
  intro c hc
  rw [mem_max_iff (K := K)] at hc
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 (l_ne_zero (K := K) l)) hc
  refine ⟨n, (dvd_iff_norm (K := K) (by rw [map_natCast]; exact l_ne_zero l)).2 ?_⟩
  rw [map_pow, norm_pow, map_natCast]
  exact hn.le

/- English proof (translation)
Introduce `n`. Rewrite using `[coeff_C]`. Apply the tactic sequence `split_ifs <;> simp [hc]`.
-/
theorem C_mem_A {c : K} (hc : ‖c‖ ≤ 1) : (C c : K⟦X⟧) ∈ A O K := by
  intro n
  rw [coeff_C]
  split_ifs <;> simp [hc]

variable (O K) in
/- English proof (translation)
Establish `: ProperSpace K` using `FiniteDimensional.proper ℚ_[l] K`. Establish `hl : (l : K) ^ n ≠ 0` using `pow_ne_zero _ (l_ne_zero l)`. Take `⟨T0, hT0, hT0f, hcov⟩` from `finite_cover_balls_of_compact (isCompact_closedBall (0 : K) 1) (norm_pos_iff.2 hl)`. Establish `hX : (X : K⟦X⟧) ∈ A O K` using `HasU.X_mem`. Proceed by induction on `m with`.

Consider the case `zero`. Use `⟨{0}, Set.finite_singleton _, by simp, fun f hf => ⟨0, rfl, 0, zero_mem _, f, hf, by simp⟩⟩` and prove the remaining obligations. Consider the case `succ m ih`. Take `⟨T, hTf, hTA, hT⟩` from `ih`. Use `⟨Set.image2 (fun t c => t + X ^ m * C c) T T0, hTf.image2 _ hT0f, ?_, fun f hf => ?_⟩` and prove the remaining obligations.

Introduce and unpack `_ ⟨t, ht, c, hc, rfl⟩`. Conclude with `add_mem (hTA t ht) (mul_mem (pow_mem hX _) (C_mem_A (mem_closedBall_zero_iff.1 (hT0 hc))))`. Take `⟨t, ht, g, hg, h, hh, rfl⟩` from `hT f hf`. Establish `h0 : constantCoeff h ∈ Metric.closedBall (0 : K) 1`. Rewrite using `[mem_closedBall_zero_iff, ← coeff_zero_eq_constantCoeff_apply]`.

Conclude with `hh 0`. Take `⟨c, hc, hc'⟩` from `Set.mem_iUnion₂.1 (hcov h0)`. Rewrite `hc'` using `[mem_ball_iff_norm]`. Use `⟨_, ⟨t, ht, c, hc, rfl⟩, g + X ^ m * C ((constantCoeff h - c) / (l : K) ^ n), add_mem hg (mul_mem (pow_mem hX _) (C_mem_A ?_)), PowerSeries.mk fun p => coeff (p + 1) h, fun p => by rw [coeff_mk]; exact hh _, ?_⟩` and prove the remaining obligations. Rewrite using `[norm_div]`.

Conclude with `div_le_one_of_le₀ hc'.le (norm_nonneg _)`. Establish `h1` using `eq_X_mul_shift_add_const h`. Establish `h2 : (l : K⟦X⟧) ^ n * C ((constantCoeff h - c) / (l : K) ^ n) = C (constantCoeff h) - C c`. Rewrite using `[← map_natCast (C (R := K)), ← map_pow, ← map_mul, mul_div_cancel₀ _ hl, map_sub]`. Take the linear combination `X ^ m * h1 - X ^ m * h2`.
-/
theorem exists_finite_representatives_A_mod_pow_l_pow_X [FiniteDimensional ℚ_[l] K] (n m : ℕ) :
    ∃ T : Set K⟦X⟧, T.Finite ∧ (∀ t ∈ T, t ∈ A O K) ∧ ∀ f ∈ A O K, ∃ t ∈ T, ∃ g ∈ A O K,
      ∃ h ∈ A O K, f = t + (l : K⟦X⟧) ^ n * g + X ^ m * h := by
  have : ProperSpace K := FiniteDimensional.proper ℚ_[l] K
  have hl : (l : K) ^ n ≠ 0 := pow_ne_zero _ (l_ne_zero l)
  obtain ⟨T0, hT0, hT0f, hcov⟩ := finite_cover_balls_of_compact (isCompact_closedBall (0 : K) 1)
    (norm_pos_iff.2 hl)
  have hX : (X : K⟦X⟧) ∈ A O K := HasU.X_mem
  induction m with
  | zero =>
    refine ⟨{0}, Set.finite_singleton _, by simp, fun f hf => ⟨0, rfl, 0, zero_mem _, f, hf, by simp⟩⟩
  | succ m ih =>
    obtain ⟨T, hTf, hTA, hT⟩ := ih
    refine ⟨Set.image2 (fun t c => t + X ^ m * C c) T T0, hTf.image2 _ hT0f, ?_, fun f hf => ?_⟩
    · rintro _ ⟨t, ht, c, hc, rfl⟩
      exact add_mem (hTA t ht) (mul_mem (pow_mem hX _) (C_mem_A (mem_closedBall_zero_iff.1 (hT0 hc))))
    · obtain ⟨t, ht, g, hg, h, hh, rfl⟩ := hT f hf
      have h0 : constantCoeff h ∈ Metric.closedBall (0 : K) 1 := by
        rw [mem_closedBall_zero_iff, ← coeff_zero_eq_constantCoeff_apply]
        exact hh 0
      obtain ⟨c, hc, hc'⟩ := Set.mem_iUnion₂.1 (hcov h0)
      rw [mem_ball_iff_norm] at hc'
      refine ⟨_, ⟨t, ht, c, hc, rfl⟩, g + X ^ m * C ((constantCoeff h - c) / (l : K) ^ n),
        add_mem hg (mul_mem (pow_mem hX _) (C_mem_A ?_)), PowerSeries.mk fun p => coeff (p + 1) h,
        fun p => by rw [coeff_mk]; exact hh _, ?_⟩
      · rw [norm_div]
        exact div_le_one_of_le₀ hc'.le (norm_nonneg _)
      · have h1 := eq_X_mul_shift_add_const h
        have h2 : (l : K⟦X⟧) ^ n * C ((constantCoeff h - c) / (l : K) ^ n) =
            C (constantCoeff h) - C c := by
          rw [← map_natCast (C (R := K)), ← map_pow, ← map_mul, mul_div_cancel₀ _ hl, map_sub]
        linear_combination X ^ m * h1 - X ^ m * h2

end PositivityTheory.CompleteLocalMinorRing.Minor
