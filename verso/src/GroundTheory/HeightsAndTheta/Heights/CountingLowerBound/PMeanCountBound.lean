import Mathlib
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

open Real MeasureTheory Filter Topology Finset

noncomputable section

universe u

/- English proof (translation)
Introduce `X _ μ lam cnt a ka r h`. Use `h.isProbability` as an intermediate fact. Take `⟨θ, hθ⟩ : ∃ θ : ℝ, θ = 1 / 12` from `⟨_, rfl⟩`. Establish `hθ0 : 0 < θ` using `by rw [hθ]; norm_num`. Establish `hθ1 : θ ≤ 1` using `by rw [hθ]; norm_num`.

Establish `hθ12 : 12 * θ = 1` using `by rw [hθ]; norm_num`. Establish `hr` using `h.r_pos`. Establish `ha0 : a ≠ 0` using `by have := h.one_le_a; omega`. Use `set m := meanCount μ cnt r with hm`. Establish `hm0 : 0 ≤ m` using `integral_nonneg (h.cnt_nonneg r)`.

Establish `hprod : ∀ j : ℕ, (12 : ℝ) ^ j * θ ^ j = 1` using `fun j => by`. Rewrite using `[← mul_pow, hθ12, one_pow]`. Establish `hpt : ∀ (j : ℕ) (z : X), lam z < r → θ ^ (j + 1) * r ≤ lam z → cnt r z ≤ (3 * 12 ^ (j + 1)) ^ a`. Introduce `j z hlt hle`. Establish `hl` using `h.lam_pos z`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[div_le_iff₀ hl]`. Combine the equalities or inequalities in the displayed calculation. Take the linear combination `(-(3 * r)) * hprod (j + 1)`. Use `_ ≤ 3 * 12 ^ (j + 1) * lam z := by gcongr`.

Establish `hterm : ∀ k : ℕ, (36 * 12 ^ (k + 1) : ℝ) ^ a * meanCount μ cnt (θ ^ (k + 1) * r) ≤ 1 / 4 * (1 / 2) ^ k * m`. Introduce `k`. Establish `hy0 : 0 < θ ^ (k + 1)` using `pow_pos hθ0 _`. Establish `hy1 : θ ^ (k + 1) ≤ 1` using `pow_le_one₀ hθ0.le hθ1`. Rewrite using `[h.scaling _ _ hy0 hr, ← mul_assoc]`.

Use `mul_le_mul_of_nonneg_right ?_ hm0` and prove the remaining obligations. Establish `hka : (θ ^ (k + 1)) ^ ka ≤ (θ ^ (k + 1)) ^ (3 * a)`. Rewrite using `[← Real.rpow_natCast (θ ^ (k + 1)) (3 * a)]`. Apply `Real.rpow_le_rpow_of_exponent_ge hy0 hy1` to reduce the goal to its premises. Use `h.three_a_le_ka` as an intermediate fact.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `heq : (36 * 12 ^ (k + 1) : ℝ) ^ a * (θ ^ (k + 1)) ^ (3 * a) = (36 * (θ ^ (k + 1)) ^ 2) ^ a`. Rewrite using `[pow_mul, ← mul_pow]`. Use `congr 1`.

Take the linear combination `(36 * (θ ^ (k + 1)) ^ 2) * hprod (k + 1)`. Establish `hsq : 36 * (θ ^ (k + 1)) ^ 2 = 1 / 4 * (θ ^ 2) ^ k`. Establish `: θ ^ 2 = 1 / 144` using `by rw [hθ]; norm_num`. Rewrite using `[← pow_mul, show (k + 1) * 2 = 2 + 2 * k by ring, pow_add, pow_mul, this]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hθ2 : θ ^ 2 ≤ 1 / 2` using `by rw [hθ]; norm_num`. Establish `hs1 : 1 / 4 * (θ ^ 2) ^ k ≤ 1 / 4 * (1 / 2) ^ k` using `by gcongr`. Establish `hs2 : 1 / 4 * (θ ^ 2) ^ k ≤ 1`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.

Set `S : ℕ → Set X` to `fun N => {z | θ ^ (N + 1) * r ≤ lam z}`. Establish `hSmeas : ∀ N, MeasurableSet (S N)` using `fun N => measurableSet_le measurable_const h.lam_meas`. Establish `hSmono : Monotone S`. Introduce `N M hNM z hz`. Simplify using `only [S, Set.mem_ofPred_eq] at hz ⊢`.

Establish `: θ ^ (M + 1) ≤ θ ^ (N + 1)` using `pow_le_pow_of_le_one hθ0.le hθ1 (by omega)`. Use the polynomial consequences of the given equalities and inequalities. Establish `hSunion : ⋃ N, S N = Set.univ`. Use `Set.eq_univ_of_forall fun z => ?_` and prove the remaining obligations. Take `⟨n, hn⟩` from `exists_pow_lt_of_lt_one (div_pos (h.lam_pos z) hr) (show θ < 1 by rw [hθ]; norm_num)`.

Use `Set.mem_iUnion.2 ⟨n, ?_⟩` and prove the remaining obligations. Simplify using `only [S, Set.mem_ofPred_eq]`. Establish `h1 : θ ^ (n + 1) ≤ θ ^ n` using `pow_le_pow_of_le_one hθ0.le hθ1 (by omega)`. Rewrite `hn` using `[lt_div_iff₀ hr]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hbound : ∀ N, ∫ z in S N, cnt r z ∂μ ≤ 36 ^ a + m / 2`. Introduce `N`. Use `set G : X → ℝ := fun z => 36 ^ a + ∑ i ∈ range N, (36 * 12 ^ (i + 1) : ℝ) ^ a * cnt (θ ^ (i + 1) * r) z with hG`. Establish `hint : ∀ i : ℕ, Integrable (cnt (θ ^ (i + 1) * r)) μ` using `fun i => h.integrable _ (mul_pos (pow_pos hθ0 _) hr)`. Establish `hGi : Integrable G μ` using `(integrable_const _).add (integrable_finsetSum _ fun i _ => (hint i).const_mul _)`.

Establish `hsum_nonneg : ∀ z, 0 ≤ ∑ i ∈ range N, (36 * 12 ^ (i + 1) : ℝ) ^ a * cnt (θ ^ (i + 1) * r) z` using `fun z => sum_nonneg fun i _ => mul_nonneg (by positivity) (h.cnt_nonneg _ _)`. Establish `hG0 : ∀ z, 0 ≤ G z` using `fun z => add_nonneg (by positivity) (hsum_nonneg z)`. Establish `hle : ∀ z ∈ S N, cnt r z ≤ G z`. Introduce `z hz`. Simplify using `only [S, Set.mem_ofPred_eq] at hz`.

Break down `le_or_gt r (lam z) with hrl | hlr` into its components or cases. Rewrite using `[h.zero r hr z hrl]`. Conclude with `hG0 z`. Establish `hex : ∃ j, θ ^ (j + 1) * r ≤ lam z` using `⟨N, hz⟩`. Use `set j := Nat.find hex with hj`.

Establish `hjle : j ≤ N` using `Nat.find_min' hex hz`. Establish `hjspec : θ ^ (j + 1) * r ≤ lam z` using `Nat.find_spec hex`. Break down `Nat.eq_zero_or_eq_succ_pred j with hj0 | hjs` into its components or cases. Combine the equalities or inequalities in the displayed calculation. Use `set k := j.pred`.

Establish `hk : k < N` using `by omega`. Establish `hnot : ¬ θ ^ (k + 1) * r ≤ lam z` using `Nat.find_min hex (by omega)`. Establish `hone : 1 ≤ cnt (θ ^ (k + 1) * r) z` using `h.one _ (mul_pos (pow_pos hθ0 _) hr) (mul_le_of_le_one_left hr.le (pow_le_one₀ hθ0.le hθ1)) z (lt_of_not_ge hnot)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hjs, Nat.succ_eq_add_one]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ (36 * 12 ^ (k + 1) : ℝ) ^ a * cnt (θ ^ (k + 1) * r) z := le_mul_of_one_le_right (by positivity) hone`. Use `_ ≤ ∑ i ∈ range N, (36 * 12 ^ (i + 1) : ℝ) ^ a * cnt (θ ^ (i + 1) * r) z := single_le_sum (f := fun i => (36 * 12 ^ (i + 1) : ℝ) ^ a * cnt (θ ^ (i + 1) * r) z) (fun i _ => mul_nonneg (by positivity) (h.cnt_nonneg _ _)) (mem_range.2 hk)`. Use `_ ≤ G z := le_add_of_nonneg_left (by positivity)`.

Establish `hGint : ∫ z, G z ∂μ = 36 ^ a + ∑ i ∈ range N, (36 * 12 ^ (i + 1) : ℝ) ^ a * meanCount μ cnt (θ ^ (i + 1) * r)`. Rewrite using `[hG, integral_add (integrable_const _) (integrable_finsetSum _ fun i _ => (hint i).const_mul _), integral_finsetSum _ fun i _ => (hint i).const_mul _]`. Simplify using `[integral_const_mul, meanCount]`. Establish `hgeo : ∑ i ∈ range N, (36 * 12 ^ (i + 1) : ℝ) ^ a * meanCount μ cnt (θ ^ (i + 1) * r) ≤ m / 2`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_sum]; exact sum_congr rfl fun i _ => by ring`. Use `_ ≤ 1 / 4 * m * 2 := by gcongr; exact sum_geometric_two_le N`. Use `_ = m / 2 := by ring`. Combine the equalities or inequalities in the displayed calculation. Establish `ht` using `tendsto_setIntegral_of_monotone hSmeas hSmono (by rw [hSunion]; exact (h.integrable r hr).integrableOn)`.

Rewrite `ht` using `[hSunion, Measure.restrict_univ]`. Establish `hfin : m ≤ 36 ^ a + m / 2` using `le_of_tendsto' ht hbound`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem MeanCountBound.proof : MeanCountBound.Statement := by
  intro X _ μ lam cnt a ka r h
  have := h.isProbability
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = 1 / 12 := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by rw [hθ]; norm_num
  have hθ1 : θ ≤ 1 := by rw [hθ]; norm_num
  have hθ12 : 12 * θ = 1 := by rw [hθ]; norm_num
  have hr := h.r_pos
  have ha0 : a ≠ 0 := by have := h.one_le_a; omega
  set m := meanCount μ cnt r with hm
  have hm0 : 0 ≤ m := integral_nonneg (h.cnt_nonneg r)
  have hprod : ∀ j : ℕ, (12 : ℝ) ^ j * θ ^ j = 1 := fun j => by
    rw [← mul_pow, hθ12, one_pow]

  have hpt : ∀ (j : ℕ) (z : X), lam z < r → θ ^ (j + 1) * r ≤ lam z →
      cnt r z ≤ (3 * 12 ^ (j + 1)) ^ a := by
    intro j z hlt hle
    have hl := h.lam_pos z
    calc cnt r z ≤ (3 * r / lam z) ^ a := h.count r hr le_rfl z hlt
      _ ≤ (3 * 12 ^ (j + 1)) ^ a := by
        gcongr
        rw [div_le_iff₀ hl]
        calc 3 * r = 3 * 12 ^ (j + 1) * (θ ^ (j + 1) * r) := by
              linear_combination (-(3 * r)) * hprod (j + 1)
          _ ≤ 3 * 12 ^ (j + 1) * lam z := by gcongr

  have hterm : ∀ k : ℕ, (36 * 12 ^ (k + 1) : ℝ) ^ a * meanCount μ cnt (θ ^ (k + 1) * r)
      ≤ 1 / 4 * (1 / 2) ^ k * m := by
    intro k
    have hy0 : 0 < θ ^ (k + 1) := pow_pos hθ0 _
    have hy1 : θ ^ (k + 1) ≤ 1 := pow_le_one₀ hθ0.le hθ1
    rw [h.scaling _ _ hy0 hr, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ hm0
    have hka : (θ ^ (k + 1)) ^ ka ≤ (θ ^ (k + 1)) ^ (3 * a) := by
      rw [← Real.rpow_natCast (θ ^ (k + 1)) (3 * a)]
      apply Real.rpow_le_rpow_of_exponent_ge hy0 hy1
      have := h.three_a_le_ka
      push_cast
      linarith
    have heq : (36 * 12 ^ (k + 1) : ℝ) ^ a * (θ ^ (k + 1)) ^ (3 * a)
        = (36 * (θ ^ (k + 1)) ^ 2) ^ a := by
      rw [pow_mul, ← mul_pow]
      congr 1
      linear_combination (36 * (θ ^ (k + 1)) ^ 2) * hprod (k + 1)
    have hsq : 36 * (θ ^ (k + 1)) ^ 2 = 1 / 4 * (θ ^ 2) ^ k := by
      have : θ ^ 2 = 1 / 144 := by rw [hθ]; norm_num
      rw [← pow_mul, show (k + 1) * 2 = 2 + 2 * k by ring, pow_add, pow_mul, this]
      ring
    have hθ2 : θ ^ 2 ≤ 1 / 2 := by rw [hθ]; norm_num
    have hs1 : 1 / 4 * (θ ^ 2) ^ k ≤ 1 / 4 * (1 / 2) ^ k := by gcongr
    have hs2 : 1 / 4 * (θ ^ 2) ^ k ≤ 1 := by
      calc 1 / 4 * (θ ^ 2) ^ k ≤ 1 / 4 * 1 := by
            gcongr; exact pow_le_one₀ (by positivity) (by linarith)
        _ ≤ 1 := by norm_num
    calc (36 * 12 ^ (k + 1) : ℝ) ^ a * (θ ^ (k + 1)) ^ ka
        ≤ (36 * 12 ^ (k + 1) : ℝ) ^ a * (θ ^ (k + 1)) ^ (3 * a) := by gcongr
      _ = (1 / 4 * (θ ^ 2) ^ k) ^ a := by rw [heq, hsq]
      _ ≤ 1 / 4 * (θ ^ 2) ^ k := pow_le_of_le_one (by positivity) hs2 ha0
      _ ≤ 1 / 4 * (1 / 2) ^ k := hs1

  let S : ℕ → Set X := fun N => {z | θ ^ (N + 1) * r ≤ lam z}
  have hSmeas : ∀ N, MeasurableSet (S N) := fun N =>
    measurableSet_le measurable_const h.lam_meas
  have hSmono : Monotone S := by
    intro N M hNM z hz
    simp only [S, Set.mem_ofPred_eq] at hz ⊢
    have : θ ^ (M + 1) ≤ θ ^ (N + 1) := pow_le_pow_of_le_one hθ0.le hθ1 (by omega)
    nlinarith
  have hSunion : ⋃ N, S N = Set.univ := by
    refine Set.eq_univ_of_forall fun z => ?_
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos (h.lam_pos z) hr)
      (show θ < 1 by rw [hθ]; norm_num)
    refine Set.mem_iUnion.2 ⟨n, ?_⟩
    simp only [S, Set.mem_ofPred_eq]
    have h1 : θ ^ (n + 1) ≤ θ ^ n := pow_le_pow_of_le_one hθ0.le hθ1 (by omega)
    rw [lt_div_iff₀ hr] at hn
    nlinarith

  have hbound : ∀ N, ∫ z in S N, cnt r z ∂μ ≤ 36 ^ a + m / 2 := by
    intro N
    set G : X → ℝ := fun z => 36 ^ a +
      ∑ i ∈ range N, (36 * 12 ^ (i + 1) : ℝ) ^ a * cnt (θ ^ (i + 1) * r) z with hG
    have hint : ∀ i : ℕ, Integrable (cnt (θ ^ (i + 1) * r)) μ := fun i =>
      h.integrable _ (mul_pos (pow_pos hθ0 _) hr)
    have hGi : Integrable G μ :=
      (integrable_const _).add (integrable_finsetSum _ fun i _ => (hint i).const_mul _)
    have hsum_nonneg : ∀ z, 0 ≤ ∑ i ∈ range N, (36 * 12 ^ (i + 1) : ℝ) ^ a *
        cnt (θ ^ (i + 1) * r) z := fun z =>
      sum_nonneg fun i _ => mul_nonneg (by positivity) (h.cnt_nonneg _ _)
    have hG0 : ∀ z, 0 ≤ G z := fun z => add_nonneg (by positivity) (hsum_nonneg z)
    have hle : ∀ z ∈ S N, cnt r z ≤ G z := by
      intro z hz
      simp only [S, Set.mem_ofPred_eq] at hz
      rcases le_or_gt r (lam z) with hrl | hlr
      · rw [h.zero r hr z hrl]; exact hG0 z
      classical
      have hex : ∃ j, θ ^ (j + 1) * r ≤ lam z := ⟨N, hz⟩
      set j := Nat.find hex with hj
      have hjle : j ≤ N := Nat.find_min' hex hz
      have hjspec : θ ^ (j + 1) * r ≤ lam z := Nat.find_spec hex
      rcases Nat.eq_zero_or_eq_succ_pred j with hj0 | hjs
      · calc cnt r z ≤ (3 * 12 ^ (j + 1)) ^ a := hpt j z hlr hjspec
          _ = 36 ^ a := by rw [hj0]; norm_num
          _ ≤ G z := le_add_of_nonneg_right (hsum_nonneg z)
      · set k := j.pred
        have hk : k < N := by omega
        have hnot : ¬ θ ^ (k + 1) * r ≤ lam z := Nat.find_min hex (by omega)
        have hone : 1 ≤ cnt (θ ^ (k + 1) * r) z :=
          h.one _ (mul_pos (pow_pos hθ0 _) hr)
            (mul_le_of_le_one_left hr.le (pow_le_one₀ hθ0.le hθ1)) z (lt_of_not_ge hnot)
        calc cnt r z ≤ (3 * 12 ^ (j + 1)) ^ a := hpt j z hlr hjspec
          _ = (36 * 12 ^ (k + 1) : ℝ) ^ a := by
              rw [hjs, Nat.succ_eq_add_one]; congr 1; ring
          _ ≤ (36 * 12 ^ (k + 1) : ℝ) ^ a * cnt (θ ^ (k + 1) * r) z :=
              le_mul_of_one_le_right (by positivity) hone
          _ ≤ ∑ i ∈ range N, (36 * 12 ^ (i + 1) : ℝ) ^ a * cnt (θ ^ (i + 1) * r) z :=
              single_le_sum (f := fun i => (36 * 12 ^ (i + 1) : ℝ) ^ a *
                cnt (θ ^ (i + 1) * r) z)
                (fun i _ => mul_nonneg (by positivity) (h.cnt_nonneg _ _))
                (mem_range.2 hk)
          _ ≤ G z := le_add_of_nonneg_left (by positivity)
    have hGint : ∫ z, G z ∂μ = 36 ^ a + ∑ i ∈ range N,
        (36 * 12 ^ (i + 1) : ℝ) ^ a * meanCount μ cnt (θ ^ (i + 1) * r) := by
      rw [hG, integral_add (integrable_const _)
        (integrable_finsetSum _ fun i _ => (hint i).const_mul _),
        integral_finsetSum _ fun i _ => (hint i).const_mul _]
      simp [integral_const_mul, meanCount]
    have hgeo : ∑ i ∈ range N, (36 * 12 ^ (i + 1) : ℝ) ^ a *
        meanCount μ cnt (θ ^ (i + 1) * r) ≤ m / 2 := by
      calc _ ≤ ∑ i ∈ range N, 1 / 4 * (1 / 2 : ℝ) ^ i * m := sum_le_sum fun i _ => hterm i
        _ = 1 / 4 * m * ∑ i ∈ range N, (1 / 2 : ℝ) ^ i := by
            rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
        _ ≤ 1 / 4 * m * 2 := by gcongr; exact sum_geometric_two_le N
        _ = m / 2 := by ring
    calc ∫ z in S N, cnt r z ∂μ ≤ ∫ z in S N, G z ∂μ :=
          setIntegral_mono_on (h.integrable r hr).integrableOn hGi.integrableOn (hSmeas N) hle
      _ ≤ ∫ z, G z ∂μ := setIntegral_le_integral hGi (ae_of_all _ hG0)
      _ ≤ 36 ^ a + m / 2 := by rw [hGint]; linarith
  have ht := tendsto_setIntegral_of_monotone hSmeas hSmono
    (by rw [hSunion]; exact (h.integrable r hr).integrableOn)
  rw [hSunion, Measure.restrict_univ] at ht
  have hfin : m ≤ 36 ^ a + m / 2 := le_of_tendsto' ht hbound
  linarith

end

end GroundTheory.Heights₂.Heights.LowerBound
