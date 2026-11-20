import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GeometricSideComparison
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianSpaceMomentIdentity
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.MomentBoundOfPointwiseMoments
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GeometryOfNumbersLatticeEstimate
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GlobalGeometricEstimateOfLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianSpaceGeometricEstimate
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GeometricSideQuadraticFormIdentity
open UpperTheory.V.Lit.Geo

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor in
/- English proof (translation)
Introduce `v v' h`. Establish `hu : IsUnit (GeneralLinearGroup.map (pInf E) g).val` using `Units.isUnit _`. Establish `h1 : vInf v = vInf v'` using `Matrix.vecMul_injective_of_isUnit hu h`. Use function extensionality and compare the values at `i`. Establish `h2 : ((pInf E).comp (algebraMap E (Ad E))) (v i) = ((pInf E).comp (algebraMap E (Ad E))) (v' i)` using `congrFun h1 i`.

Conclude with `((pInf E).comp (algebraMap E (Ad E))).injective h2`.
-/
private theorem pt_injective {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (g : GA E a) :
    Function.Injective (pt g) := by
  intro v v' h
  have hu : IsUnit (GeneralLinearGroup.map (pInf E) g).val := Units.isUnit _
  have h1 : vInf v = vInf v' := Matrix.vecMul_injective_of_isUnit hu h
  funext i
  have h2 : ((pInf E).comp (algebraMap E (Ad E))) (v i) = ((pInf E).comp (algebraMap E (Ad E))) (v' i) := congrFun h1 i
  exact ((pInf E).comp (algebraMap E (Ad E))).injective h2

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor in
/- English proof (translation)
Introduce `E _ _ _ a ha L hL`. Take `⟨c, hc, hlow⟩` from `UpperTheory.geometric_side_comparison`. Take `⟨N, hN⟩` from `UpperTheory.geometry_of_numbers_lattice_estimate E a ha L hL`. Take `⟨C, -, hC⟩` from `UpperTheory.moment_bound_of_pointwise_moments N 1`. Establish `hD : (0 : ℝ) < (a : ℝ) * Fintype.card (InfinitePlace E)`.

Establish `h1 : (0 : ℝ) < a` using `by exact_mod_cast ha`. Establish `h2 : (0 : ℝ) < Fintype.card (InfinitePlace E)` using `by exact_mod_cast Fintype.card_pos`. Conclude with `mul_pos h1 h2`. Use `⟨c / ((a : ℝ) * Fintype.card (InfinitePlace E)), div_pos hc hD, fun g hg => ?_⟩` and prove the remaining obligations. Establish `hell : ell E a (toL (mom L g).1) = trF (mom L g).1 1 / ((a : ℝ) * Fintype.card (InfinitePlace E))`.

Simplify using `only [trF, mul_one, Matrix.trace, Matrix.diag, Finset.sum_apply, Complex.re_sum]`. Both sides reduce to the same expression. Rewrite using `[hell]`. Use `div_le_div_of_nonneg_right ?_ hD.le` and prove the remaining obligations. Rewrite using `[UpperTheory.hermitian_space_moment_identity E a ha L hL g 1, le_div_iff₀ (by linarith)]`.

Simplify using `only [(UpperTheory.geometric_side_quadraticForm_identity E a).1]`. Set `φ : lat L g →+ EuclideanSpace ℂ (Fin a × InfinitePlace E)` to `((euc (E := E) (a := a)).toLinearMap.toAddMonoidHom.comp (pt (rt g))).comp (lat L g).subtype`. Establish `hφ : ∀ v : lat L g, ‖φ v‖ ^ 2 = qf (pt (rt g) v.1)` using `fun v => norm_euc_sq _`. Establish `hinj : Function.Injective φ` using `fun v v' h => Subtype.ext (pt_injective (rt g) ((euc (E := E) (a := a)).injective h))`. Establish `hs0 : Summable fun v : lat L g => Real.exp (-Real.pi * qf (pt (rt g) v.1))`.

Simplify `((hN g).2 1 1 one_pos le_rfl).1` using `only [one_mul]`. Establish `hs1 : Summable fun v : lat L g => qf (pt (rt g) v.1) * Real.exp (-Real.pi * qf (pt (rt g) v.1))`. Use `((hC _ _ (hN g)).1.sub hs0).congr fun v => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Use `hlow (lat L g) _ φ hinj` as an intermediate fact.

Simplify using `only [hφ] at this`. Conclude with `this hs0 hs1 hg`.
-/
theorem UpperTheory.hermitian_point_embedding_injective :
    GradA := by
  intro E _ _ _ a ha L hL
  obtain ⟨c, hc, hlow⟩ := UpperTheory.geometric_side_comparison
  obtain ⟨N, hN⟩ := UpperTheory.geometry_of_numbers_lattice_estimate E a ha L hL
  obtain ⟨C, -, hC⟩ := UpperTheory.moment_bound_of_pointwise_moments N 1
  have hD : (0 : ℝ) < (a : ℝ) * Fintype.card (InfinitePlace E) := by
    have h1 : (0 : ℝ) < a := by exact_mod_cast ha
    have h2 : (0 : ℝ) < Fintype.card (InfinitePlace E) := by exact_mod_cast Fintype.card_pos
    exact mul_pos h1 h2
  refine ⟨c / ((a : ℝ) * Fintype.card (InfinitePlace E)), div_pos hc hD, fun g hg => ?_⟩
  have hell : ell E a (toL (mom L g).1) = trF (mom L g).1 1 / ((a : ℝ) * Fintype.card (InfinitePlace E)) := by
    simp only [trF, mul_one, Matrix.trace, Matrix.diag, Finset.sum_apply, Complex.re_sum]
    rfl
  rw [hell]
  refine div_le_div_of_nonneg_right ?_ hD.le
  rw [UpperTheory.hermitian_space_moment_identity E a ha L hL g 1, le_div_iff₀ (by linarith)]
  simp only [(UpperTheory.geometric_side_quadraticForm_identity E a).1]
  let φ : lat L g →+ EuclideanSpace ℂ (Fin a × InfinitePlace E) :=
    ((euc (E := E) (a := a)).toLinearMap.toAddMonoidHom.comp (pt (rt g))).comp (lat L g).subtype
  have hφ : ∀ v : lat L g, ‖φ v‖ ^ 2 = qf (pt (rt g) v.1) := fun v => norm_euc_sq _
  have hinj : Function.Injective φ := fun v v' h =>
    Subtype.ext (pt_injective (rt g) ((euc (E := E) (a := a)).injective h))
  have hs0 : Summable fun v : lat L g => Real.exp (-Real.pi * qf (pt (rt g) v.1)) := by
    simpa only [one_mul] using ((hN g).2 1 1 one_pos le_rfl).1
  have hs1 : Summable fun v : lat L g => qf (pt (rt g) v.1) * Real.exp (-Real.pi * qf (pt (rt g) v.1)) := by
    refine ((hC _ _ (hN g)).1.sub hs0).congr fun v => ?_
    ring
  have := hlow (lat L g) _ φ hinj
  simp only [hφ] at this
  exact this hs0 hs1 hg
