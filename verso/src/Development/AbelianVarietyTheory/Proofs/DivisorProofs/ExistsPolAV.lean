import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PolarisationOfFaithfullyFlat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProperRelAmpleKTrivOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfFaithfullyFlat
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SmoothOfRelativeDimensionOfFibre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PolFieldDescent

/- English proof (translation)
Introduce `K K' _ _ ga G _ _ L hL hS A' α hP hw`. Use `letI : Algebra K K' := ga.toAlgebra`. Establish `hP' : IsGrpPullback A'.A G (spMap (algebraMap K K')) α` using `hP`. Establish `: Flat (spMap ga)` using `Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)`. Establish `: Surjective (spMap ga)` using `⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := K) (B := K')⟩`.

Establish `: QuasiCompact (spMap ga)` using `inferInstance`. Establish `hAb : IsAbelianScheme G` using `PolFlatDescent.isAbelianScheme_of_pull hP A'.isAb`. Establish `hdim : SmoothOfRelativeDimension A'.g G.hom` using `CM.smoothOfRelativeDimension_of_fibre K K' ga G A'.A.left α A'.A.hom A'.g hAb hP.1 A'.smoothDim`. Establish `hrig : Out.Rigidified G L` using `DVR.exists_gen_of_local L hL _ _`. Establish `hamp : Out.RelAmple G L` using `AmpleDescent.relAmple_of_faithfullyFlat K K' G A'.A α L A'.L hAb hP' hL A'.isLB hw A'.ample`.

Establish `hK : Out.KTriv G L` using `AmpleDescent.kTriv_of_pull hP hL A'.isLB hw A'.ktriv`. Use `⟨⟨G, hAb, A'.g, hdim, L, hL, hrig, hS, hamp, hK⟩, Iso.refl G, ?_, ?_⟩` and prove the remaining obligations. Use `show IsMonHom (𝟙 G)`. Use `infer_instance`. Conclude with `GlobalTheory.lbIso_pull_id hL`.
-/
theorem exists_polAV : ∀ (K K' : Type) [Field K] [Field K'] (ga : K →+* K') (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G] (L : LB G.left), L.IsLB → Out.Sym G L → ∀ (A' : PolAV (Sp K')) (α : A'.A.left ⟶ G.left), IsGrpPullback A'.A G (spMap ga) α → LBIso A'.L (L.pull α) → ∃ (A : PolAV (Sp K)) (gen : G ≅ A.A), IsMonHom gen.hom ∧ LBIso (A.L.pull gen.hom.left) L := by
  intro K K' _ _ ga G _ _ L hL hS A' α hP hw
  letI : Algebra K K' := ga.toAlgebra
  have hP' : IsGrpPullback A'.A G (spMap (algebraMap K K')) α := hP
  have : Flat (spMap ga) := Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : Surjective (spMap ga) := ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := K) (B := K')⟩
  have : QuasiCompact (spMap ga) := inferInstance
  have hAb : IsAbelianScheme G := PolFlatDescent.isAbelianScheme_of_pull hP A'.isAb
  have hdim : SmoothOfRelativeDimension A'.g G.hom :=
    CM.smoothOfRelativeDimension_of_fibre K K' ga G A'.A.left α A'.A.hom A'.g hAb hP.1 A'.smoothDim
  have hrig : Out.Rigidified G L := DVR.exists_gen_of_local L hL _ _
  have hamp : Out.RelAmple G L :=
    AmpleDescent.relAmple_of_faithfullyFlat K K' G A'.A α L A'.L hAb hP' hL A'.isLB hw A'.ample
  have hK : Out.KTriv G L := AmpleDescent.kTriv_of_pull hP hL A'.isLB hw A'.ktriv
  refine ⟨⟨G, hAb, A'.g, hdim, L, hL, hrig, hS, hamp, hK⟩, Iso.refl G, ?_, ?_⟩
  · show IsMonHom (𝟙 G); infer_instance
  · exact GlobalTheory.lbIso_pull_id hL

end GlobalTheory.PolFieldDescent
