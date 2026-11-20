import Mathlib
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsAffineOpenBiInfOfLe
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBHomologyFiniteOfAffineCover
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSmulHomologyEqZeroOfAcyclicFibre
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SubsingletonOfPoints
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MumfordBundleCechFiniteVanishesOffOrigin
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MumfordBundleCechCohomologyFinrank
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleLBGenericOfSpecial
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibAc
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.PicField

/- English proof (translation)
Take `⟨p⟩ : Nonempty (Sp k)` from `inferInstance`. Take `⟨V, hV, hc⟩` from `exists_pull_eq_zero c p`. Establish `hV' : V = ⊤`. Establish `hs : Subsingleton (Sp k)`. Unfold `Sp`.

Use `infer_instance`. Use extensionality with `x`. Simplify using `only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]`. Conclude with `(Subsingleton.elim x p) ▸ hV`. Substitute `hV'` using the available equality.

Establish `: IsIso (⊤ : (Sp k).Opens).ι` using `(Sp k).topIso.isIso_hom`. Establish `e : c = CechPic.pull (inv (⊤ : (Sp k).Opens).ι) (CechPic.pull (⊤ : (Sp k).Opens).ι c)`. Rewrite using `[← pull_comp, IsIso.inv_hom_id, pull_id]`. Rewrite using `[e, hc, map_zero]`.
-/
theorem pic_eq_zero (k : Type) [Field k] (c : Pic (Sp k)) : c = 0 := by
  obtain ⟨p⟩ : Nonempty (Sp k) := inferInstance
  obtain ⟨V, hV, hc⟩ := exists_pull_eq_zero c p
  have hV' : V = ⊤ := by
    have hs : Subsingleton (Sp k) := by
      unfold Sp; infer_instance
    ext x
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    exact (Subsingleton.elim x p) ▸ hV
  subst hV'
  have : IsIso (⊤ : (Sp k).Opens).ι := (Sp k).topIso.isIso_hom
  have e : c = CechPic.pull (inv (⊤ : (Sp k).Opens).ι) (CechPic.pull (⊤ : (Sp k).Opens).ι c) := by
    rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  rw [e, hc, map_zero]

end GlobalTheory.CompanionTheory.PicField
