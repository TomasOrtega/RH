import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsobaricCuspidalMultiplicityOneOfTwisted
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsobaricRigidOfPin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Adm2OfPublishedInputsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChiOneAwayFromType
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TotallyComplexHostE
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ChiOneAbove

/- English proof (translation)
Establish `hrig : IsobaricRigid D.nd D.naut` using `GlobalTheory.NPin.isobaricRigid_of_pin hPr.fin hPr.js hL D P`. Establish `han1` using `GlobalTheory.RowClose.isobaricCuspidalMultiplicityOne_of_twisted _ _ _ D.nd D.naut hrig`. Establish `han2` using `GlobalTheory.SpehRigid.isobaricDiscreteSelfDualMultOne_of_isobaricSumMultOne _ _ _ D.nd D.naut hrig`. Establish `hcheb` using `GlobalTheory.ChebSplitDense.chebSplit_nd hPr.cheb D`. Conclude with `(Formalism.MainNotions.SumRepresentations.condition_iff_additive_maps D).2 ⟨han1, han2, fun Sg hSg => by`.

Establish `hd` using `(hcheb hSg.toFinset).closure_eq`. Use `hd using 4 with σ` and compare the differences between its conclusion and the goal. Simplify using `[Set.Finite.mem_toFinset]⟩`.
-/
theorem adm5 (hPr : GlobalTheory.NRows.Hypotheses₂) (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) :
    Formalism.MainNotions.SumRepresentations.adm5 D := by
  have hrig : IsobaricRigid D.nd D.naut := GlobalTheory.NPin.isobaricRigid_of_pin hPr.fin hPr.js hL D P
  have han1 := GlobalTheory.RowClose.isobaricCuspidalMultiplicityOne_of_twisted _ _ _ D.nd D.naut hrig
  have han2 := GlobalTheory.SpehRigid.isobaricDiscreteSelfDualMultOne_of_isobaricSumMultOne _ _ _ D.nd D.naut hrig
  have hcheb := GlobalTheory.ChebSplitDense.chebSplit_nd hPr.cheb D
  exact (Formalism.MainNotions.SumRepresentations.condition_iff_additive_maps D).2 ⟨han1, han2, fun Sg hSg => by
    have hd := (hcheb hSg.toFinset).closure_eq
    convert hd using 4 with σ
    simp [Set.Finite.mem_toFinset]⟩

/- English proof (translation)
Introduce `hPr hL D P i w hw`. Establish `hB : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.BlockCharParam D` using `GlobalTheory.BlockCharInf.main D P.cf P.C P.tp P.chr`. Establish `h2 : Formalism.MainNotions.SumRepresentations.adm2 D` using `GlobalTheory.T.adm2_of_prints_localLanglands hPr hL D P`. Establish `h5` using `adm5 hPr hL D P`. Take `⟨ρ, hρc, haway, habove⟩` from `(h2 i).2.2 (D.naut.tw (D.naut.muC i) D.naut.etaTinv) (GlobalTheory.ChiOneNoPt.sOne D) (GlobalTheory.ChiOneNoPt.integral D hB i)`.

Establish `hρ` using `GlobalTheory.ChiOneNoPt.eq_chi D h5 i w hw ρ hρc haway`. Take `⟨hdR, hwd, -⟩` from `habove w hw`. Substitute `hρ` using the available equality. Use `⟨((D.loc_tie i w hw).2.1 1 _ (GlobalTheory.JumpDictionaryFoundation.continuous_chiGL D i 1)).2.1.1 hdR, hwd⟩` and prove the remaining obligations.
-/
theorem main : ∀ (hPr : GlobalTheory.NRows.Hypotheses₂) (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (i : D.nd.Loc)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    Br.IsdRW D.loc D.nbr i w hw (PairedCharacterCondition.chiGL (D := D) i) ∧
    D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (PairedCharacterCondition.chiGL (D := D) i)) w =
      D.naut.lpTw (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w)
        (((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2) := by
  intro hPr hL D P i w hw
  have hB : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.BlockCharParam D := GlobalTheory.BlockCharInf.main D P.cf P.C P.tp P.chr
  have h2 : Formalism.MainNotions.SumRepresentations.adm2 D := GlobalTheory.T.adm2_of_prints_localLanglands hPr hL D P
  have h5 := adm5 hPr hL D P
  obtain ⟨ρ, hρc, haway, habove⟩ :=
    (h2 i).2.2 (D.naut.tw (D.naut.muC i) D.naut.etaTinv) (GlobalTheory.ChiOneNoPt.sOne D)
      (GlobalTheory.ChiOneNoPt.integral D hB i)
  have hρ := GlobalTheory.ChiOneNoPt.eq_chi D h5 i w hw ρ hρc haway
  obtain ⟨hdR, hwd, -⟩ := habove w hw
  subst hρ
  refine ⟨((D.loc_tie i w hw).2.1 1 _ (GlobalTheory.JumpDictionaryFoundation.continuous_chiGL D i 1)).2.1.1 hdR, hwd⟩

end GlobalTheory.ChiOneAbove
