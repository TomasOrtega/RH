import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexHessianLogOneAddNormSqStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.FSDet

/- English proof (translation)
Establish `h` using `EuclideanSpace.norm_sq_eq v`. Establish `h2 : ((‖v‖ : ℂ)) ^ 2 = ((‖v‖ ^ 2 : ℝ) : ℂ)` using `by push_cast; rfl`. Rewrite using `[h2, h]`. Use `push_cast`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Complex.conj_mul']`.
-/
theorem sum_conj_mul_self {n : ℕ} (v : ReciprocityTheory.L2DbarEstimates.V n) :
    (∑ j, starRingEnd ℂ (v j) * v j) = (‖v‖ : ℂ) ^ 2 := by
  have h := EuclideanSpace.norm_sq_eq v
  have h2 : ((‖v‖ : ℂ)) ^ 2 = ((‖v‖ ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [h2, h]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.conj_mul']

/- English proof (translation)
Use `Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Unit) a b` as an intermediate fact. Rewrite using `[Matrix.vecMulVec_eq (ι := Unit), this, dotProduct_comm]`.
-/
theorem det_one_add_vecMulVec' {m : Type} [Fintype m] [DecidableEq m] (a b : m → ℂ) :
    (1 + Matrix.vecMulVec a b).det = 1 + a ⬝ᵥ b := by
  have := Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Unit) a b
  rw [Matrix.vecMulVec_eq (ι := Unit), this, dotProduct_comm]

end GlobalTheory.FSDet

namespace GlobalTheory.FSDet

/- English proof (translation)
Introduce `n v`. Rewrite using `[GlobalTheory.T.complexHessian_log_one_add_normSq n v]`. Use `set t : ℂ := 1 + (‖v‖ : ℂ) ^ 2 with ht`. Establish `htr : t = ((1 + ‖v‖ ^ 2 : ℝ) : ℂ)` using `by rw [ht]; push_cast; rfl`. Establish `ht0 : t ≠ 0`.

Rewrite using `[htr]; exact_mod_cast (by positivity : (1 + ‖v‖ ^ 2 : ℝ) ≠ 0)`. Establish `hM : (Matrix.of (fun j l => (if j = l then (1:ℂ) else 0) / t - (starRingEnd ℂ (v j) * v l) / t ^ 2) : Matrix (Fin n) (Fin n) ℂ) = t⁻¹ • (1 + Matrix.vecMulVec (fun j => -(starRingEnd ℂ (v j)) / t) (fun l => v l))`. Use extensionality with `j l`. Simplify using `only [Matrix.of_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hM, Matrix.det_smul, det_one_add_vecMulVec', Fintype.card_fin]`. Establish `hdot : (fun j => -(starRingEnd ℂ (v j)) / t) ⬝ᵥ (fun l => v l) = -((‖v‖ : ℂ) ^ 2) / t`. Rewrite using `[← sum_conj_mul_self v, dotProduct, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Establish `hval : t⁻¹ ^ n * (1 + -((‖v‖ : ℂ) ^ 2) / t) = (((1 + ‖v‖ ^ 2 : ℝ) ^ (n + 1))⁻¹ : ℝ)`. Establish `h1 : (1 + -((‖v‖ : ℂ) ^ 2) / t) = t⁻¹`. Clear the denominators using the available nonvanishing facts. Rewrite using `[ht]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1, ← pow_succ, inv_pow, htr]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[hdot, hval, Complex.ofReal_re]`.
-/
theorem det_fubiniStudy_hess :
    ∀ (n : ℕ) (v : ReciprocityTheory.L2DbarEstimates.V n), (ReciprocityTheory.L2DbarEstimates.cHess n (fun w => (Real.log (1 + ‖w‖ ^ 2) : ℂ)) v).det.re = ((1 + ‖v‖ ^ 2) ^ (n + 1))⁻¹ := by
  intro n v
  rw [GlobalTheory.T.complexHessian_log_one_add_normSq n v]
  set t : ℂ := 1 + (‖v‖ : ℂ) ^ 2 with ht
  have htr : t = ((1 + ‖v‖ ^ 2 : ℝ) : ℂ) := by rw [ht]; push_cast; rfl
  have ht0 : t ≠ 0 := by
    rw [htr]; exact_mod_cast (by positivity : (1 + ‖v‖ ^ 2 : ℝ) ≠ 0)
  have hM : (Matrix.of (fun j l => (if j = l then (1:ℂ) else 0) / t - (starRingEnd ℂ (v j) * v l) / t ^ 2) : Matrix (Fin n) (Fin n) ℂ)
      = t⁻¹ • (1 + Matrix.vecMulVec (fun j => -(starRingEnd ℂ (v j)) / t) (fun l => v l)) := by
    ext j l
    simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    field_simp
    ring
  rw [hM, Matrix.det_smul, det_one_add_vecMulVec', Fintype.card_fin]
  have hdot : (fun j => -(starRingEnd ℂ (v j)) / t) ⬝ᵥ (fun l => v l) = -((‖v‖ : ℂ) ^ 2) / t := by
    rw [← sum_conj_mul_self v, dotProduct, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hval : t⁻¹ ^ n * (1 + -((‖v‖ : ℂ) ^ 2) / t) = (((1 + ‖v‖ ^ 2 : ℝ) ^ (n + 1))⁻¹ : ℝ) := by
    have h1 : (1 + -((‖v‖ : ℂ) ^ 2) / t) = t⁻¹ := by
      field_simp
      rw [ht]; ring
    rw [h1, ← pow_succ, inv_pow, htr]
    push_cast
    rfl
  rw [hdot, hval, Complex.ofReal_re]

end GlobalTheory.FSDet
