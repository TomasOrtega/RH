import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

namespace BoundedMonomials

def chartNorm (A : HermLine n) (c : (k : ι) → Fin (n k + 1)) (d : ι → ℕ)
    (e : MvPolynomial (Coord n) ℤ) (z : Cone n ℂ) : ℝ :=
  ‖evalCone z e‖ / (‖evalCone z (chartMonomial c d)‖ * A.metric z)

omit [Fintype ι] in

/- English proof (translation)
Simplify using `only [Finsupp.weight_apply, coordDeg, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero, Finsupp.prod]`. Repeatedly rewrite using `[← Finset.prod_pow_eq_pow_sum]`. Rewrite using `[Finset.prod_comm]`. Use `Finset.prod_congr rfl fun v _ ↦ ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_eq_single v.1 (fun k _ hk ↦ by simp [hk]) (fun h ↦ absurd (Finset.mem_univ _) h)]`.

Simplify using the standard rewrite rules.
-/
theorem prod_pow_weight [Fintype ι] {F : Type*} [CommRing F] (u : ι → F) (m : Coord n →₀ ℕ) :
    (m.prod fun v e ↦ u v.1 ^ e) = ∏ k, u k ^ Finsupp.weight (coordDeg n) m k := by
  simp only [Finsupp.weight_apply, coordDeg, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_apply, mul_ite, mul_one, mul_zero, Finsupp.prod]
  simp_rw [← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  rw [Finset.prod_eq_single v.1 (fun k _ hk ↦ by simp [hk]) (fun h ↦ absurd (Finset.mem_univ _) h)]
  simp

/- English proof (translation)
Use `conv_lhs => rw [f.as_sum]`. Use `conv_rhs => rw [f.as_sum]`. Simplify using `only [evalCone, eval₂_sum, eval₂_monomial, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m hm ↦ ?_` and prove the remaining obligations. Establish `hw : Finsupp.weight (coordDeg n) m = δ` using `hf (mem_support_iff.mp hm)`.

Rewrite using `[← hw, ← prod_pow_weight u m]`. Simplify using `only [mul_pow, Finsupp.prod_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem evalCone_scale {F : Type*} [CommRing F] (u : ι → F) (z : Cone n F)
    {f : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ} (hf : IsWeightedHomogeneous (coordDeg n) f δ) :
    evalCone (fun k i ↦ u k * z k i) f = (∏ k, u k ^ δ k) * evalCone z f := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  simp only [evalCone, eval₂_sum, eval₂_monomial, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hw : Finsupp.weight (coordDeg n) m = δ := hf (mem_support_iff.mp hm)
  rw [← hw, ← prod_pow_weight u m]
  simp only [mul_pow, Finsupp.prod_mul]
  ring

omit [Fintype ι] [DecidableEq ι] in

/- English proof (translation)
Establish `h : (fun z : Cone n ℂ ↦ evalCone z f) = fun z ↦ eval (fun v : Coord n ↦ z v.1 v.2) (map (Int.castRingHom ℂ) f)`. Use function extensionality and compare the values at `z`. Rewrite using `[eval_map]`. Both sides reduce to the same expression. Rewrite using `[h]`.

Conclude with `(continuous_eval _).comp (continuous_pi fun v ↦ (continuous_apply v.2).comp (continuous_apply v.1))`.
-/
theorem continuous_evalCone (f : MvPolynomial (Coord n) ℤ) :
    Continuous fun z : Cone n ℂ ↦ evalCone z f := by
  have h : (fun z : Cone n ℂ ↦ evalCone z f) =
      fun z ↦ eval (fun v : Coord n ↦ z v.1 v.2) (map (Int.castRingHom ℂ) f) := by
    funext z
    rw [eval_map]
    rfl
  rw [h]
  exact (continuous_eval _).comp
    (continuous_pi fun v ↦ (continuous_apply v.2).comp (continuous_apply v.1))

omit [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Simplify using `[evalCone]`.
-/
theorem evalCone_X {F : Type*} [CommRing F] (z : Cone n F) (k : ι) (i : Fin (n k + 1)) :
    evalCone z (X ⟨k, i⟩) = z k i := by
  simp [evalCone]

omit [DecidableEq ι] in
/- English proof (translation)
Simplify using `[evalCone, chartMonomial, eval₂_prod]`.
-/
theorem evalCone_chartMonomial' {F : Type*} [CommRing F] (z : Cone n F)
    (c : (k : ι) → Fin (n k + 1)) (d : ι → ℕ) :
    evalCone z (chartMonomial c d) = ∏ k, z k (c k) ^ d k := by
  simp [evalCone, chartMonomial, eval₂_prod]

omit [DecidableEq ι] in
/- English proof (translation)
Rewrite using `[evalCone_chartMonomial']`. Conclude with `Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)`.
-/
theorem evalCone_chartMonomial_ne_zero {z : Cone n ℂ} {c : (k : ι) → Fin (n k + 1)} (d : ι → ℕ)
    (hc : ∀ k, z k (c k) ≠ 0) : evalCone z (chartMonomial c d) ≠ 0 := by
  rw [evalCone_chartMonomial']
  exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)

/- English proof (translation)
Use `set m := chartMonomial c d`. Use `set m' := chartMonomial c' d'`. Establish `hmem : e * m' - e' * m ∈ P.ideal`. Establish `h : s.den * (e * m' - e' * m) = (s.den * e - s.num * m) * m' - (s.den * e' - s.num * m') * m` using `by ring`. Establish `h2 : s.den * (e * m' - e' * m) ∈ P.ideal`.

Rewrite using `[h]`. Conclude with `P.ideal.sub_mem (P.ideal.mul_mem_right _ he.2) (P.ideal.mul_mem_right _ he'.2)`. Conclude with `(P.isPrime.mem_or_mem h2).resolve_left s.den_not_mem`. Establish `h0 : evalCone z (e * m' - e' * m) = 0` using `hz.2 _ hmem`. Simplify using `only [evalCone, eval₂_sub, eval₂_mul, sub_eq_zero] at h0`.

Establish `hn : ‖evalCone z e‖ * ‖evalCone z m'‖ = ‖evalCone z e'‖ * ‖evalCone z m‖`. Rewrite using `[← norm_mul, ← norm_mul]`. Conclude with `congrArg norm h0`. Establish `hh : 0 < A.metric z` using `A.metric_pos z hz.1`. Establish `hm : ‖evalCone z m‖ ≠ 0` using `norm_ne_zero_iff.mpr (evalCone_chartMonomial_ne_zero d hc)`.

Establish `hm' : ‖evalCone z m'‖ ≠ 0` using `norm_ne_zero_iff.mpr (evalCone_chartMonomial_ne_zero d' hc')`. Unfold `chartNorm`. Rewrite using `[div_eq_div_iff (mul_ne_zero hm hh.ne') (mul_ne_zero hm' hh.ne')]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem chartNorm_eq {P : ArithVariety n} {A : HermLine n} (s : IntegralSection P A.deg) {z : Cone n ℂ}
    (hz : z ∈ P.points ℂ) {c c' : (k : ι) → Fin (n k + 1)} {d d' : ι → ℕ} {e e' : MvPolynomial (Coord n) ℤ}
    (he : IsChartForm P A.deg s.num s.den c d e) (he' : IsChartForm P A.deg s.num s.den c' d' e')
    (hc : ∀ k, z k (c k) ≠ 0) (hc' : ∀ k, z k (c' k) ≠ 0) :
    chartNorm A c d e z = chartNorm A c' d' e' z := by
  set m := chartMonomial c d
  set m' := chartMonomial c' d'
  have hmem : e * m' - e' * m ∈ P.ideal := by
    have h : s.den * (e * m' - e' * m) =
        (s.den * e - s.num * m) * m' - (s.den * e' - s.num * m') * m := by ring
    have h2 : s.den * (e * m' - e' * m) ∈ P.ideal := by
      rw [h]
      exact P.ideal.sub_mem (P.ideal.mul_mem_right _ he.2) (P.ideal.mul_mem_right _ he'.2)
    exact (P.isPrime.mem_or_mem h2).resolve_left s.den_not_mem
  have h0 : evalCone z (e * m' - e' * m) = 0 := hz.2 _ hmem
  simp only [evalCone, eval₂_sub, eval₂_mul, sub_eq_zero] at h0
  have hn : ‖evalCone z e‖ * ‖evalCone z m'‖ = ‖evalCone z e'‖ * ‖evalCone z m‖ := by
    rw [← norm_mul, ← norm_mul]
    exact congrArg norm h0
  have hh : 0 < A.metric z := A.metric_pos z hz.1
  have hm : ‖evalCone z m‖ ≠ 0 := norm_ne_zero_iff.mpr (evalCone_chartMonomial_ne_zero d hc)
  have hm' : ‖evalCone z m'‖ ≠ 0 := norm_ne_zero_iff.mpr (evalCone_chartMonomial_ne_zero d' hc')
  unfold chartNorm
  rw [div_eq_div_iff (mul_ne_zero hm hh.ne') (mul_ne_zero hm' hh.ne')]
  calc ‖evalCone z e‖ * (‖evalCone z m'‖ * A.metric z)
      = (‖evalCone z e‖ * ‖evalCone z m'‖) * A.metric z := by ring
    _ = (‖evalCone z e'‖ * ‖evalCone z m‖) * A.metric z := by rw [hn]
    _ = ‖evalCone z e'‖ * (‖evalCone z m‖ * A.metric z) := by ring

/- English proof (translation)
Unfold `chartNorm`. Rewrite using `[evalCone_scale u z he, evalCone_scale u z (isWeightedHomogeneous_chartMonomial c d), A.metric_smul u z hu hz, norm_mul, norm_mul, norm_prod, norm_prod]`. Simplify using `only [norm_pow]`. Establish `hQ : ∏ k, ‖u k‖ ^ δ k = (∏ k, ‖u k‖ ^ d k) * ∏ k, ‖u k‖ ^ A.deg k`. Rewrite using `[← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun k _ ↦ ?_` and prove the remaining obligations. Establish `hk : ‖u k‖ ≠ 0` using `norm_ne_zero_iff.mpr (hu k)`. Rewrite using `[← zpow_natCast, ← zpow_natCast, hδ k, zpow_add₀ hk, mul_comm]`. Establish `hD : (∏ k, ‖u k‖ ^ d k) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (norm_ne_zero_iff.mpr (hu k))`. Establish `hH : (∏ k, ‖u k‖ ^ A.deg k) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ (norm_ne_zero_iff.mpr (hu k))`.

Rewrite using `[hQ]`. Establish `h : (∏ k, ‖u k‖ ^ d k) * ‖evalCone z (chartMonomial c d)‖ * ((∏ k, ‖u k‖ ^ A.deg k) * A.metric z) = ((∏ k, ‖u k‖ ^ d k) * ∏ k, ‖u k‖ ^ A.deg k) * (‖evalCone z (chartMonomial c d)‖ * A.metric z)` using `by ring`. Rewrite using `[h, mul_div_mul_left _ _ (mul_ne_zero hD hH)]`.
-/
theorem chartNorm_scale (A : HermLine n) (c : (k : ι) → Fin (n k + 1)) (d : ι → ℕ)
    {e : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ} (he : IsWeightedHomogeneous (coordDeg n) e δ)
    (hδ : ∀ k, (δ k : ℤ) = A.deg k + d k) {u : ι → ℂ} (hu : ∀ k, u k ≠ 0) {z : Cone n ℂ}
    (hz : BlockNonzero z) :
    chartNorm A c d e (fun k i ↦ u k * z k i) = chartNorm A c d e z := by
  unfold chartNorm
  rw [evalCone_scale u z he, evalCone_scale u z (isWeightedHomogeneous_chartMonomial c d),
    A.metric_smul u z hu hz, norm_mul, norm_mul, norm_prod, norm_prod]
  simp only [norm_pow]
  have hQ : ∏ k, ‖u k‖ ^ δ k = (∏ k, ‖u k‖ ^ d k) * ∏ k, ‖u k‖ ^ A.deg k := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    have hk : ‖u k‖ ≠ 0 := norm_ne_zero_iff.mpr (hu k)
    rw [← zpow_natCast, ← zpow_natCast, hδ k, zpow_add₀ hk, mul_comm]
  have hD : (∏ k, ‖u k‖ ^ d k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (norm_ne_zero_iff.mpr (hu k))
  have hH : (∏ k, ‖u k‖ ^ A.deg k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ (norm_ne_zero_iff.mpr (hu k))
  rw [hQ]
  have h : (∏ k, ‖u k‖ ^ d k) * ‖evalCone z (chartMonomial c d)‖ *
      ((∏ k, ‖u k‖ ^ A.deg k) * A.metric z) =
      ((∏ k, ‖u k‖ ^ d k) * ∏ k, ‖u k‖ ^ A.deg k) *
        (‖evalCone z (chartMonomial c d)‖ * A.metric z) := by ring
  rw [h, mul_div_mul_left _ _ (mul_ne_zero hD hH)]

def unitChart (c : (k : ι) → Fin (n k + 1)) : Set (Cone n ℂ) :=
  {z | (∀ k, z k (c k) = 1) ∧ ∀ k i, ‖z k i‖ ≤ 1}

omit [DecidableEq ι] in
/- English proof (translation)
Use `Metric.isCompact_of_isClosed_isBounded ?_ ?_` and prove the remaining obligations. Establish `h : unitChart c = (⋂ k, {z : Cone n ℂ | z k (c k) = 1}) ∩ ⋂ k, ⋂ i, {z : Cone n ℂ | ‖z k i‖ ≤ 1}`. Use extensionality with `z`. Simplify using `[unitChart]`. Rewrite using `[h]`.

Use `(isClosed_iInter fun k ↦ ?_).inter (isClosed_iInter fun k ↦ isClosed_iInter fun i ↦ ?_)` and prove the remaining obligations. Conclude with `isClosed_eq ((continuous_apply (c k)).comp (continuous_apply k)) continuous_const`. Conclude with `isClosed_le ((continuous_apply i).comp (continuous_apply k)).norm continuous_const`. Use `(Metric.isBounded_closedBall (x := (0 : Cone n ℂ)) (r := 1)).subset fun z hz ↦ ?_` and prove the remaining obligations. Rewrite using `[Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]`.

Introduce `k`. Rewrite using `[pi_norm_le_iff_of_nonneg zero_le_one]`. Conclude with `hz.2 k`.
-/
theorem isCompact_unitChart (c : (k : ι) → Fin (n k + 1)) : IsCompact (unitChart c) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have h : unitChart c = (⋂ k, {z : Cone n ℂ | z k (c k) = 1}) ∩
        ⋂ k, ⋂ i, {z : Cone n ℂ | ‖z k i‖ ≤ 1} := by
      ext z
      simp [unitChart]
    rw [h]
    refine (isClosed_iInter fun k ↦ ?_).inter (isClosed_iInter fun k ↦ isClosed_iInter fun i ↦ ?_)
    · exact isClosed_eq ((continuous_apply (c k)).comp (continuous_apply k)) continuous_const
    · exact isClosed_le ((continuous_apply i).comp (continuous_apply k)).norm continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : Cone n ℂ)) (r := 1)).subset fun z hz ↦ ?_
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro k
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    exact hz.2 k

omit [DecidableEq ι] in

/- English proof (translation)
Establish `hnz : ∀ z ∈ unitChart c, BlockNonzero z` using `fun z hz k h0 ↦ by`. Use `hz.1 k` as an intermediate fact. Rewrite `this` using `[h0]`. Conclude with `zero_ne_one this`. Establish `hcont : ContinuousOn (chartNorm A c d e) (unitChart c)`.

Use `ContinuousOn.div (continuous_evalCone e).norm.continuousOn (((continuous_evalCone _).norm.continuousOn).mul (A.metric_smooth.continuousOn.mono fun z hz ↦ hnz z hz)) fun z hz ↦ ?_` and prove the remaining obligations. Use `mul_ne_zero (norm_ne_zero_iff.mpr (evalCone_chartMonomial_ne_zero d fun k ↦ ?_)) (A.metric_pos z (hnz z hz)).ne'` and prove the remaining obligations. Rewrite using `[hz.1 k]`. Conclude with `one_ne_zero`. Take `⟨B, hB⟩` from `(isCompact_unitChart c).exists_bound_of_continuousOn hcont`.

Conclude with `⟨B, fun z hz ↦ (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hB z hz))⟩`.
-/
theorem exists_bound_unitChart (A : HermLine n) (c : (k : ι) → Fin (n k + 1)) (d : ι → ℕ)
    (e : MvPolynomial (Coord n) ℤ) : ∃ B : ℝ, ∀ z ∈ unitChart c, chartNorm A c d e z ≤ B := by
  have hnz : ∀ z ∈ unitChart c, BlockNonzero z := fun z hz k h0 ↦ by
    have := hz.1 k
    rw [h0] at this
    exact zero_ne_one this
  have hcont : ContinuousOn (chartNorm A c d e) (unitChart c) := by
    refine ContinuousOn.div (continuous_evalCone e).norm.continuousOn
      (((continuous_evalCone _).norm.continuousOn).mul
        (A.metric_smooth.continuousOn.mono fun z hz ↦ hnz z hz)) fun z hz ↦ ?_
    refine mul_ne_zero (norm_ne_zero_iff.mpr (evalCone_chartMonomial_ne_zero d fun k ↦ ?_))
      (A.metric_pos z (hnz z hz)).ne'
    rw [hz.1 k]
    exact one_ne_zero
  obtain ⟨B, hB⟩ := (isCompact_unitChart c).exists_bound_of_continuousOn hcont
  exact ⟨B, fun z hz ↦ (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hB z hz))⟩

/- English proof (translation)
Distinguish the cases in `hlive : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal`. Take `⟨d₀, e₀, he₀⟩` from `s.regular c hlive`. Take `⟨B, hB⟩` from `exists_bound_unitChart A c d₀ e₀`. Use `⟨B, fun z hz hc hmax d e he ↦ ?_⟩` and prove the remaining obligations. Take `⟨δ, hδe, hδ⟩` from `he₀.1`.

Use `set u : ι → ℂ := fun k ↦ (z k (c k))⁻¹`. Establish `hu : ∀ k, u k ≠ 0` using `fun k ↦ inv_ne_zero (hc k)`. Rewrite using `[chartNorm_eq s hz he he₀ hc hc, ← chartNorm_scale A c d₀ hδe hδ hu hz.1]`. Use `hB _ ⟨fun k ↦ inv_mul_cancel₀ (hc k), fun k i ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[norm_mul, norm_inv, inv_mul_le_iff₀ (norm_pos_iff.mpr (hc k)), mul_one]`.

Conclude with `hmax k i`. Use `⟨0, fun z hz hc _ d e _ ↦ ?_⟩` and prove the remaining obligations. Simplify using `only [not_forall, not_not] at hlive`. Take `⟨k, hk⟩` from `hlive`. Establish `h0` using `hz.2 _ hk`.

Rewrite `h0` using `[evalCone_X]`. Conclude with `absurd h0 (hc k)`.
-/
theorem exists_bound_chart {P : ArithVariety n} {A : HermLine n} (s : IntegralSection P A.deg)
    (c : (k : ι) → Fin (n k + 1)) :
    ∃ B : ℝ, ∀ z ∈ P.points ℂ, (∀ k, z k (c k) ≠ 0) → (∀ k i, ‖z k i‖ ≤ ‖z k (c k)‖) →
      ∀ (d : ι → ℕ) (e : MvPolynomial (Coord n) ℤ), IsChartForm P A.deg s.num s.den c d e →
        chartNorm A c d e z ≤ B := by
  by_cases hlive : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal
  · obtain ⟨d₀, e₀, he₀⟩ := s.regular c hlive
    obtain ⟨B, hB⟩ := exists_bound_unitChart A c d₀ e₀
    refine ⟨B, fun z hz hc hmax d e he ↦ ?_⟩
    obtain ⟨δ, hδe, hδ⟩ := he₀.1
    set u : ι → ℂ := fun k ↦ (z k (c k))⁻¹
    have hu : ∀ k, u k ≠ 0 := fun k ↦ inv_ne_zero (hc k)
    rw [chartNorm_eq s hz he he₀ hc hc, ← chartNorm_scale A c d₀ hδe hδ hu hz.1]
    refine hB _ ⟨fun k ↦ inv_mul_cancel₀ (hc k), fun k i ↦ ?_⟩
    rw [norm_mul, norm_inv, inv_mul_le_iff₀ (norm_pos_iff.mpr (hc k)), mul_one]
    exact hmax k i
  · refine ⟨0, fun z hz hc _ d e _ ↦ ?_⟩
    simp only [not_forall, not_not] at hlive
    obtain ⟨k, hk⟩ := hlive
    have h0 := hz.2 _ hk
    rw [evalCone_X] at h0
    exact absurd h0 (hc k)

/- English proof (translation)
Introduce `ι _ _ n P A s`. Use `⟨fun z hz c c' d d' e e' he he' hc hc' ↦ chartNorm_eq s hz he he' hc hc', ?_⟩` and prove the remaining obligations. Use `choose B hB using exists_bound_chart s`. Use `⟨Real.log (∑ c, |B c| + 1), fun z hz c d e he hc ↦ ?_⟩` and prove the remaining obligations. Establish `hS : 0 < ∑ c, |B c| + 1` using `by positivity`.

Rewrite using `[Real.exp_log hS]`. Establish `hmax : ∀ k, ∃ i, ∀ j, ‖z k j‖ ≤ ‖z k i‖` using `fun k ↦ by`. Take `⟨i, -, hi⟩` from `Finset.exists_max_image Finset.univ (fun j ↦ ‖z k j‖) Finset.univ_nonempty`. Conclude with `⟨i, fun j ↦ hi j (Finset.mem_univ j)⟩`. Use `choose c₀ hc₀ using hmax`.

Establish `hc₀z : ∀ k, z k (c₀ k) ≠ 0` using `fun k h0 ↦ by`. Take `⟨j, hj⟩` from `Function.ne_iff.mp (hz.1 k)`. Use `hc₀ k j` as an intermediate fact. Rewrite `this` using `[h0, norm_zero]`. Conclude with `hj (norm_le_zero_iff.mp this)`.

Establish `hlive : ∀ k, (X ⟨k, c₀ k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal` using `fun k hk ↦ by`. Establish `h0` using `hz.2 _ hk`. Rewrite `h0` using `[evalCone_X]`. Conclude with `hc₀z k h0`. Take `⟨d₀, e₀, he₀⟩` from `s.regular c₀ hlive`.

Express the relevant statement in the definitionally equal form `chartNorm A c d e z ≤ _`. Rewrite using `[chartNorm_eq s hz he he₀ hc hc₀z]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem proof : BoundedMonomials.Statement := by
  intro ι _ _ n P A s
  refine ⟨fun z hz c c' d d' e e' he he' hc hc' ↦ chartNorm_eq s hz he he' hc hc', ?_⟩
  choose B hB using exists_bound_chart s
  refine ⟨Real.log (∑ c, |B c| + 1), fun z hz c d e he hc ↦ ?_⟩
  have hS : 0 < ∑ c, |B c| + 1 := by positivity
  rw [Real.exp_log hS]

  have hmax : ∀ k, ∃ i, ∀ j, ‖z k j‖ ≤ ‖z k i‖ := fun k ↦ by
    obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j ↦ ‖z k j‖) Finset.univ_nonempty
    exact ⟨i, fun j ↦ hi j (Finset.mem_univ j)⟩
  choose c₀ hc₀ using hmax
  have hc₀z : ∀ k, z k (c₀ k) ≠ 0 := fun k h0 ↦ by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp (hz.1 k)
    have := hc₀ k j
    rw [h0, norm_zero] at this
    exact hj (norm_le_zero_iff.mp this)
  have hlive : ∀ k, (X ⟨k, c₀ k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal := fun k hk ↦ by
    have h0 := hz.2 _ hk
    rw [evalCone_X] at h0
    exact hc₀z k h0
  obtain ⟨d₀, e₀, he₀⟩ := s.regular c₀ hlive
  change chartNorm A c d e z ≤ _
  rw [chartNorm_eq s hz he he₀ hc hc₀z]
  calc chartNorm A c₀ d₀ e₀ z ≤ B c₀ := hB c₀ z hz hc₀z hc₀ d₀ e₀ he₀
    _ ≤ |B c₀| := le_abs_self _
    _ ≤ ∑ c, |B c| := Finset.single_le_sum (fun c _ ↦ abs_nonneg (B c)) (Finset.mem_univ c₀)
    _ ≤ ∑ c, |B c| + 1 := by linarith

end BoundedMonomials

end

end GroundTheory.Heights₂.Heights
