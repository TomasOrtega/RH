import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianSpaceMomentIdentity
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.TraceFormCauchySchwarzCmDatum
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.MomentBoundOfPointwiseMoments
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GeometryOfNumbersLatticeEstimate
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianSpaceGeometricEstimate
open UpperTheory.V.Lit.Geo

/- English proof (translation)
Establish `hc2 : 0 < c ^ 2` using `by positivity`. Break down `h3 with h | h` into its components or cases. Rewrite using `[h]`. Check the signs of the components of the expression. Establish `hz : c ^ 2 ≤ z` using `(pow_le_pow_left₀ hc.le h 2).trans h1`.

Establish `hz0 : 0 ≤ z` using `hc2.le.trans hz`. Rewrite using `[div_mul_eq_mul_div, le_div_iff₀ hc2]`. Establish `a1 : z * c ^ 2 ≤ z * z` using `mul_le_mul_of_nonneg_left hz hz0`. Establish `a2 : z * z ≤ (W * q) * (W * q)` using `mul_self_le_mul_self hz0 h2`. Establish `a3 : q ^ 2 ≤ (1 + q) ^ 2` using `by nlinarith`.

Establish `a4 : W ^ 2 * q ^ 2 ≤ W ^ 2 * (1 + q) ^ 2` using `mul_le_mul_of_nonneg_left a3 (sq_nonneg W)`. Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem gradB_pt {z n W q c : ℝ} (hc : 0 < c) (hq : 0 ≤ q)
    (h1 : n ^ 2 ≤ z) (h2 : z ≤ W * q) (h3 : z = 0 ∨ c ≤ n) :
    z ≤ W ^ 2 / c ^ 2 * (1 + q) ^ 2 := by
  have hc2 : 0 < c ^ 2 := by positivity
  rcases h3 with h | h
  · rw [h]; positivity
  · have hz : c ^ 2 ≤ z := (pow_le_pow_left₀ hc.le h 2).trans h1
    have hz0 : 0 ≤ z := hc2.le.trans hz
    rw [div_mul_eq_mul_div, le_div_iff₀ hc2]
    have a1 : z * c ^ 2 ≤ z * z := mul_le_mul_of_nonneg_left hz hz0
    have a2 : z * z ≤ (W * q) * (W * q) := mul_self_le_mul_self hz0 h2
    have a3 : q ^ 2 ≤ (1 + q) ^ 2 := by nlinarith
    have a4 : W ^ 2 * q ^ 2 ≤ W ^ 2 * (1 + q) ^ 2 := mul_le_mul_of_nonneg_left a3 (sq_nonneg W)
    nlinarith

/- English proof (translation)
Introduce `E _ _ _ a ha L hL`. Take `⟨N, hN⟩` from `UpperTheory.geometry_of_numbers_lattice_estimate E a ha L hL`. Take `⟨C, hC0, hC⟩` from `UpperTheory.moment_bound_of_pointwise_moments N 2`. Use `⟨C, fun g w c hc hsep => ?_⟩` and prove the remaining obligations. Take `⟨hs, hle⟩` from `hC _ _ (hN g)`.

Establish `hTh : 1 ≤ Th L g` using `((UpperTheory.hermitian_space_geometric_estimate E a ha L hL).1 g).1`. Establish `hTh0 : 0 < Th L g` using `lt_of_lt_of_le one_pos hTh`. Establish `hR` using `(UpperTheory.traceForm_cauchy_schwarz_cmDatum E a w).2.2`. Rewrite using `[UpperTheory.hermitian_space_moment_identity E a ha L hL g, div_le_iff₀ hTh0]`. Establish `hK : 0 ≤ qf w ^ 2 / c ^ 2` using `by positivity`.

Establish `hpt : ∀ v : lat L g, quad (Matrix.vecMulVec w (star w)) (pt (rt g) v.1) * gauss (pt (rt g) v.1) ≤ qf w ^ 2 / c ^ 2 * ((1 + qf (pt (rt g) v.1)) ^ 2 * Real.exp (-Real.pi * qf (pt (rt g) v.1)))`. Introduce `v`. Take `⟨r1, r2, r3⟩` from `hR (pt (rt g) v.1)`. Rewrite using `[← mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_right (gradB_pt hc (qf_nonneg _) r1 r2 ((hsep v.1 v.2).imp r3 id)) (Real.exp_pos _).le`.

Establish `hnn : ∀ v : lat L g, 0 ≤ quad (Matrix.vecMulVec w (star w)) (pt (rt g) v.1) * gauss (pt (rt g) v.1)` using `fun v => mul_nonneg ((sq_nonneg _).trans (hR _).1) (Real.exp_pos _).le`. Establish `hs2` using `hs.mul_left (qf w ^ 2 / c ^ 2)`. Establish `hs1` using `Summable.of_nonneg_of_le hnn hpt hs2`. Use `(hs1.tsum_le_tsum hpt hs2).trans ?_` and prove the remaining obligations. Rewrite using `[tsum_mul_left]`.

Use `(mul_le_mul_of_nonneg_left hle hK).trans (le_of_eq ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ * (C * Th L g) = _`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.hermitian_space_gradient_estimate :
    GradB := by
  intro E _ _ _ a ha L hL
  obtain ⟨N, hN⟩ := UpperTheory.geometry_of_numbers_lattice_estimate E a ha L hL
  obtain ⟨C, hC0, hC⟩ := UpperTheory.moment_bound_of_pointwise_moments N 2
  refine ⟨C, fun g w c hc hsep => ?_⟩
  obtain ⟨hs, hle⟩ := hC _ _ (hN g)
  have hTh : 1 ≤ Th L g := ((UpperTheory.hermitian_space_geometric_estimate E a ha L hL).1 g).1
  have hTh0 : 0 < Th L g := lt_of_lt_of_le one_pos hTh
  have hR := (UpperTheory.traceForm_cauchy_schwarz_cmDatum E a w).2.2
  rw [UpperTheory.hermitian_space_moment_identity E a ha L hL g, div_le_iff₀ hTh0]
  have hK : 0 ≤ qf w ^ 2 / c ^ 2 := by positivity
  have hpt : ∀ v : lat L g, quad (Matrix.vecMulVec w (star w)) (pt (rt g) v.1) * gauss (pt (rt g) v.1) ≤
      qf w ^ 2 / c ^ 2 * ((1 + qf (pt (rt g) v.1)) ^ 2 * Real.exp (-Real.pi * qf (pt (rt g) v.1))) := by
    intro v
    obtain ⟨r1, r2, r3⟩ := hR (pt (rt g) v.1)
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (gradB_pt hc (qf_nonneg _) r1 r2 ((hsep v.1 v.2).imp r3 id)) (Real.exp_pos _).le
  have hnn : ∀ v : lat L g, 0 ≤ quad (Matrix.vecMulVec w (star w)) (pt (rt g) v.1) * gauss (pt (rt g) v.1) :=
    fun v => mul_nonneg ((sq_nonneg _).trans (hR _).1) (Real.exp_pos _).le
  have hs2 := hs.mul_left (qf w ^ 2 / c ^ 2)
  have hs1 := Summable.of_nonneg_of_le hnn hpt hs2
  refine (hs1.tsum_le_tsum hpt hs2).trans ?_
  rw [tsum_mul_left]
  refine (mul_le_mul_of_nonneg_left hle hK).trans (le_of_eq ?_)
  change _ * (C * Th L g) = _
  ring
