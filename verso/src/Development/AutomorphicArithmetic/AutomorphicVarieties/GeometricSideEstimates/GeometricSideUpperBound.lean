import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.MomentBoundOfPointwiseMoments

open UpperTheory.V.Lit.Geo

/- English proof (translation)
Introduce `N`. Choose the witnesses or unpack the hypotheses as in `⟨⟨K, hK, hK1⟩⟩ : Nonempty {K : ℝ // K ^ N * Real.exp (-K) < 1 / (2 * Real.exp Real.pi) ∧ 1 ≤ K} := by`. Take `⟨K, hK⟩` from `(((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero N).eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (2 * Real.exp Real.pi) by positivity))).and (Filter.eventually_ge_atTop (1 : ℝ))).exists`. Conclude with `⟨⟨K, hK⟩⟩`. Establish `hK0 : 0 ≤ K` using `by linarith`.

Establish `ha : Real.exp (-Real.pi * (K - 1)) * K ^ N ≤ 1 / 2`. Establish `e1 : Real.exp (-Real.pi * (K - 1)) = Real.exp Real.pi * Real.exp (-(Real.pi * K))`. Rewrite using `[← Real.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `e2 : Real.exp (-(Real.pi * K)) ≤ Real.exp (-K)` using `Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three])`. Establish `hKN : 0 ≤ K ^ N` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Use `⟨2 * K ^ N, by positivity, ?_⟩` and prove the remaining obligations. Introduce `ι q i₀ μ hS hμ hμ1 hgap`.

Establish `hKμ : 1 / μ ≤ K / μ` using `by gcongr`. Take `⟨hsY, hY⟩` from `hS.2 (1 / μ) (K / μ) (by positivity) hKμ`. Establish `hsX : Summable fun i => Real.exp (-Real.pi * (K / μ * q i))` using `(hS.2 (K / μ) (K / μ) (by positivity) le_rfl).1`. Establish `hsI : Summable (fun i => if i = i₀ then (1 : ℝ) else 0)` using `(hasSum_ite_eq i₀ (1 : ℝ)).summable`. Establish `hX2 : ∑' i, Real.exp (-Real.pi * (K / μ * q i)) ≤ 1 + Real.exp (-Real.pi * (K - 1)) * ∑' i, Real.exp (-Real.pi * (1 / μ * q i))`.

Combine the equalities or inequalities in the displayed calculation. Use `Summable.tsum_le_tsum (fun i => ?_) hsX (hsI.add (hsY.mul_left _))` and prove the remaining obligations. Distinguish the cases in `h : i = i₀`. Establish `hq` using `hS.1 i`. Establish `h0 : -Real.pi * (K / μ * q i) ≤ 0`.

Establish `: 0 ≤ K / μ * q i` using `by positivity`. Use polynomial arithmetic with `[Real.pi_pos]`. Establish `h1` using `Real.exp_le_one_iff.mpr h0`. Establish `h2 : 0 ≤ Real.exp (-Real.pi * (K - 1)) * Real.exp (-Real.pi * (1 / μ * q i))` using `by positivity`. Rewrite using `[if_pos h]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hr : 1 ≤ q i / μ`. Rewrite using `[le_div_iff₀ hμ]`. Combine the linear relations using `[hgap i h]`. Rewrite using `[if_neg h, zero_add, ← Real.exp_add]`.

Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `e3 : K / μ * q i = K * (q i / μ)` using `by ring`. Establish `e4 : 1 / μ * q i = q i / μ` using `by ring`. Rewrite using `[e3, e4]`. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.2 hK1) (sub_nonneg.2 hr), Real.pi_pos]`.

Use `_ = 1 + Real.exp (-Real.pi * (K - 1)) * ∑' i, Real.exp (-Real.pi * (1 / μ * q i)) := by`. Rewrite using `[Summable.tsum_add hsI (hsY.mul_left _), tsum_mul_left]`. Use `congr 1`. Conclude with `tsum_ite_eq i₀ (fun _ => (1 : ℝ))`. Establish `eK : K / μ / (1 / μ) = K` using `by field_simp`.

Rewrite `hY` using `[eK]`. Establish `hX0 : 0 ≤ ∑' i, Real.exp (-Real.pi * (K / μ * q i))` using `tsum_nonneg fun i => (Real.exp_pos _).le`. Establish `hX : ∑' i, Real.exp (-Real.pi * (K / μ * q i)) ≤ 2`. Establish `ha0 : 0 ≤ Real.exp (-Real.pi * (K - 1))` using `(Real.exp_pos _).le`. Use `mul_le_mul_of_nonneg_left hY ha0` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Establish `h1K : 1 ≤ K / μ`. Rewrite using `[le_div_iff₀ hμ]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨-, hS1⟩` from `hS.2 1 (K / μ) one_pos h1K`.

Simplify using `only [one_mul, div_one] at hS1`. Establish `hpow : 0 ≤ (K / μ) ^ N` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.geometric_side_upper_bound :
    ThetaUp := by
  classical
  intro N
  obtain ⟨⟨K, hK, hK1⟩⟩ : Nonempty {K : ℝ // K ^ N * Real.exp (-K) < 1 / (2 * Real.exp Real.pi) ∧ 1 ≤ K} := by
    obtain ⟨K, hK⟩ := (((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero N).eventually
      (gt_mem_nhds (show (0 : ℝ) < 1 / (2 * Real.exp Real.pi) by positivity))).and
      (Filter.eventually_ge_atTop (1 : ℝ))).exists
    exact ⟨⟨K, hK⟩⟩
  have hK0 : 0 ≤ K := by linarith
  have ha : Real.exp (-Real.pi * (K - 1)) * K ^ N ≤ 1 / 2 := by
    have e1 : Real.exp (-Real.pi * (K - 1)) = Real.exp Real.pi * Real.exp (-(Real.pi * K)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have e2 : Real.exp (-(Real.pi * K)) ≤ Real.exp (-K) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three])
    have hKN : 0 ≤ K ^ N := by positivity
    calc Real.exp (-Real.pi * (K - 1)) * K ^ N
        = Real.exp Real.pi * (K ^ N * Real.exp (-(Real.pi * K))) := by rw [e1]; ring
      _ ≤ Real.exp Real.pi * (K ^ N * Real.exp (-K)) := by gcongr
      _ ≤ Real.exp Real.pi * (1 / (2 * Real.exp Real.pi)) := by gcongr
      _ = 1 / 2 := by field_simp
  refine ⟨2 * K ^ N, by positivity, ?_⟩
  intro ι q i₀ μ hS hμ hμ1 hgap
  have hKμ : 1 / μ ≤ K / μ := by gcongr
  obtain ⟨hsY, hY⟩ := hS.2 (1 / μ) (K / μ) (by positivity) hKμ
  have hsX : Summable fun i => Real.exp (-Real.pi * (K / μ * q i)) :=
    (hS.2 (K / μ) (K / μ) (by positivity) le_rfl).1
  have hsI : Summable (fun i => if i = i₀ then (1 : ℝ) else 0) := (hasSum_ite_eq i₀ (1 : ℝ)).summable
  have hX2 : ∑' i, Real.exp (-Real.pi * (K / μ * q i)) ≤
      1 + Real.exp (-Real.pi * (K - 1)) * ∑' i, Real.exp (-Real.pi * (1 / μ * q i)) := by
    calc ∑' i, Real.exp (-Real.pi * (K / μ * q i))
        ≤ ∑' i, ((if i = i₀ then (1 : ℝ) else 0) +
            Real.exp (-Real.pi * (K - 1)) * Real.exp (-Real.pi * (1 / μ * q i))) := by
          refine Summable.tsum_le_tsum (fun i => ?_) hsX (hsI.add (hsY.mul_left _))
          by_cases h : i = i₀
          · have hq := hS.1 i
            have h0 : -Real.pi * (K / μ * q i) ≤ 0 := by
              have : 0 ≤ K / μ * q i := by positivity
              nlinarith [Real.pi_pos]
            have h1 := Real.exp_le_one_iff.mpr h0
            have h2 : 0 ≤ Real.exp (-Real.pi * (K - 1)) * Real.exp (-Real.pi * (1 / μ * q i)) := by positivity
            rw [if_pos h]
            linarith
          · have hr : 1 ≤ q i / μ := by
              rw [le_div_iff₀ hμ]
              linarith [hgap i h]
            rw [if_neg h, zero_add, ← Real.exp_add]
            apply Real.exp_le_exp.mpr
            have e3 : K / μ * q i = K * (q i / μ) := by ring
            have e4 : 1 / μ * q i = q i / μ := by ring
            rw [e3, e4]
            nlinarith [mul_nonneg (sub_nonneg.2 hK1) (sub_nonneg.2 hr), Real.pi_pos]
      _ = 1 + Real.exp (-Real.pi * (K - 1)) * ∑' i, Real.exp (-Real.pi * (1 / μ * q i)) := by
          rw [Summable.tsum_add hsI (hsY.mul_left _), tsum_mul_left]
          congr 1
          exact tsum_ite_eq i₀ (fun _ => (1 : ℝ))
  have eK : K / μ / (1 / μ) = K := by field_simp
  rw [eK] at hY
  have hX0 : 0 ≤ ∑' i, Real.exp (-Real.pi * (K / μ * q i)) := tsum_nonneg fun i => (Real.exp_pos _).le
  have hX : ∑' i, Real.exp (-Real.pi * (K / μ * q i)) ≤ 2 := by
    have ha0 : 0 ≤ Real.exp (-Real.pi * (K - 1)) := (Real.exp_pos _).le
    have := mul_le_mul_of_nonneg_left hY ha0
    nlinarith
  have h1K : 1 ≤ K / μ := by
    rw [le_div_iff₀ hμ]
    linarith
  obtain ⟨-, hS1⟩ := hS.2 1 (K / μ) one_pos h1K
  simp only [one_mul, div_one] at hS1
  have hpow : 0 ≤ (K / μ) ^ N := by positivity
  calc ∑' i, Real.exp (-Real.pi * q i) ≤ (K / μ) ^ N * ∑' i, Real.exp (-Real.pi * (K / μ * q i)) := hS1
    _ ≤ (K / μ) ^ N * 2 := by gcongr
    _ = 2 * K ^ N / μ ^ N := by rw [div_pow]; ring
