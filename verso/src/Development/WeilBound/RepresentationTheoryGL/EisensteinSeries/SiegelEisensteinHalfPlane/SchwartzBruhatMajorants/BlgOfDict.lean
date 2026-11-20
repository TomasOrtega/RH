import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.Descend2
import GroundTheory.IdeleRoots.TorusPowers.HeckeIdem
import GroundTheory.GlobalFields.TateThesis.Nonvanishing
import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.EllipticTorusNorm
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension

open PositivityTheory.RgEis PositivityTheory.RgEis.So
open NumberField
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.RgEisSo.Hd

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Evaluate the numerical expressions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem blg_of_dict : Dict → BLg := by
  intro hD F E _ _ _ _ _ σ χ c hσ _ _ _
  obtain ⟨-, -, -, -, h5⟩ := hD F E
  have key : ∀ x : (IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)ˣ, (adCM σ χ).lg x =
      Real.log (GlobalTheory.Doubling.absE F E x : ℝ) := fun x => by
    show Real.log (GroundTheory.Global.IdeleGroup.ideleModule E (Units.map (eqv F E).toRingHom.toMonoidHom x) : ℝ) = _
    rw [h5]
  refine ⟨fun x => ?_, fun x => ?_⟩
  · have e : Units.map (eqv F E).toRingHom.toMonoidHom (Units.map (nuCM F E).toMonoidHom x) =
        GroundTheory.Global.ideleEmbedding F E x := by
      apply Units.ext
      exact GroundTheory.BlockD.ThmBHecke.adeleEquiv_algebraMap (x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)
    show Real.log (GroundTheory.Global.IdeleGroup.ideleModule E (Units.map (eqv F E).toRingHom.toMonoidHom (Units.map (nuCM F E).toMonoidHom x)) : ℝ) =
      2 * Real.log (GroundTheory.Global.IdeleGroup.ideleModule F x : ℝ)
    rw [e, ← GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := F),
      GroundTheory.Global.ideleNorm_ideleEmbedding, hσ.2.2.1, map_pow]
    have : (((GroundTheory.Global.IdeleGroup.ideleModule F x) ^ 2 : {r : ℝ // 0 < r}) : ℝ) =
      (GroundTheory.Global.IdeleGroup.ideleModule F x : ℝ) ^ 2 := rfl
    rw [this, Real.log_pow]
    norm_num
  · rw [key, key]
    have e : Units.map (adCM σ χ).σ.toMonoidHom x = GlobalTheory.Doubling.conjUnit σ x := by
      apply Units.ext
      rfl
    rw [e, GlobalTheory.Doubling.absE_conjUnit]
end GlobalTheory.CompanionTheory.RgEisSo.Hd
