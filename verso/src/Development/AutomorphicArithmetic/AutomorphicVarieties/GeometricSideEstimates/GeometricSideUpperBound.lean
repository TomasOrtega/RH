import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.MomentBoundOfPointwiseMoments

open UpperTheory.V.Lit.Geo

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Expand and normalize the polynomial expressions, which then agree.

Establish an intermediate fact. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Chain the equalities or inequalities of the calculation. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite the conclusion using the stated equalities.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use the polynomial consequences of the given equalities and inequalities.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Establish an intermediate fact.

Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
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
