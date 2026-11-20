import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.GJGlobalModulus

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace VectorMeasureTranspose

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

def trM (g : GA E k) : GA E k :=
  ⟨(g.val)ᵀ, (g⁻¹.val)ᵀ, by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]⟩

/- English proof (translation)
Conclude with `Units.ext (Matrix.det_transpose g.val)`.
-/
theorem det_trM (g : GA E k) : GeneralLinearGroup.det (trM g) = GeneralLinearGroup.det g := by
  exact Units.ext (Matrix.det_transpose g.val)

/- English proof (translation)
Unfold `Dt`. Rewrite using `[det_trM]`.
-/
theorem Dt_trM (g : GA E k) : Dt (trM g) = Dt g := by
  unfold Dt
  rw [det_trM]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem vecMeasure_eq : vecMeasure E (Fin k) = GroundTheory.Automorphic.GJMatrix.adeleMeasurePi E := rfl

/- English proof (translation)
Establish `hm : Measurable fun x : Fin k → Ad E => x ᵥ* g.val` using `GroundTheory.Automorphic.GJGlobal.Modulus.measurable_vecMul' g`. Establish `e1 : ∫⁻ x, F x ∂((GroundTheory.Automorphic.GJMatrix.adeleMeasurePi E).map fun x : Fin k → Ad E => x ᵥ* g.val) = ∫⁻ x, F (x ᵥ* g.val) ∂GroundTheory.Automorphic.GJMatrix.adeleMeasurePi E` using `lintegral_map hF hm`. Establish `h` using `GroundTheory.Automorphic.GJGlobal.Modulus.map_vecMul_adeleMeasurePi g`. Unfold `Dt`. Rewrite using `[vecMeasure_eq, ← e1, h, lintegral_smul_measure]`.

Apply the tactic sequence `try rw [smul_eq_mul]`.
-/
theorem vecMul_eq (g : GA E k) (F : (Fin k → Ad E) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F (x ᵥ* g.val) ∂vecMeasure E (Fin k) = ENNReal.ofReal (Dt g)⁻¹ * ∫⁻ x, F x ∂vecMeasure E (Fin k) := by
  have hm : Measurable fun x : Fin k → Ad E => x ᵥ* g.val := GroundTheory.Automorphic.GJGlobal.Modulus.measurable_vecMul' g
  have e1 : ∫⁻ x, F x ∂((GroundTheory.Automorphic.GJMatrix.adeleMeasurePi E).map fun x : Fin k → Ad E => x ᵥ* g.val) =
      ∫⁻ x, F (x ᵥ* g.val) ∂GroundTheory.Automorphic.GJMatrix.adeleMeasurePi E := lintegral_map hF hm
  have h := GroundTheory.Automorphic.GJGlobal.Modulus.map_vecMul_adeleMeasurePi g
  unfold Dt
  rw [vecMeasure_eq, ← e1, h, lintegral_smul_measure]
  try rw [smul_eq_mul]

/- English proof (translation)
Establish `e : ∀ x : Fin k → Ad E, F (g.val *ᵥ x) = F (x ᵥ* (trM g).val)` using `fun x => by show F (g.val *ᵥ x) = F (x ᵥ* (g.val)ᵀ)`. Rewrite using `[Matrix.vecMul_transpose]`. Use `(lintegral_congr e).trans ?_` and prove the remaining obligations. Rewrite using `[vecMul_eq (trM g) F hF, Dt_trM]`.
-/
theorem mulVec_eq (g : GA E k) (F : (Fin k → Ad E) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F (g.val *ᵥ x) ∂vecMeasure E (Fin k) = ENNReal.ofReal (Dt g)⁻¹ * ∫⁻ x, F x ∂vecMeasure E (Fin k) := by
  have e : ∀ x : Fin k → Ad E, F (g.val *ᵥ x) = F (x ᵥ* (trM g).val) := fun x => by
    show F (g.val *ᵥ x) = F (x ᵥ* (g.val)ᵀ)
    rw [Matrix.vecMul_transpose]
  refine (lintegral_congr e).trans ?_
  rw [vecMul_eq (trM g) F hF, Dt_trM]

end VectorMeasureTranspose

/- English proof (translation)
Introduce `_ E _ _ _ k g F hF`. Conclude with `⟨VectorMeasureTranspose.mulVec_eq g F hF, VectorMeasureTranspose.vecMul_eq g F hF⟩`.
-/
theorem linear_change_variables_of : D0 → AdelicLinearChange := by
  intro _ E _ _ _ k g F hF
  exact ⟨VectorMeasureTranspose.mulVec_eq g F hF, VectorMeasureTranspose.vecMul_eq g F hF⟩

end PositivityTheory.AdelicQuotientData

end
