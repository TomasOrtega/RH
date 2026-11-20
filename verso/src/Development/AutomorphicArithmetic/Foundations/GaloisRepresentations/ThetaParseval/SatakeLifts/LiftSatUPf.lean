import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.CompUnit
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueSplitPlaceComponentDefiniteUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharUnrAtUnderOfCompNormUnramified
open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.CuspRep UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `hPS hCU E _ _ _ n d hnd Bs χX χW mX mW lam U U' hU hL w hw hX hW B hB`. Take `⟨v, hvw⟩ : ∃ v, w.under (𝓞 (maximalRealSubfield E)) = v` from `⟨_, rfl⟩`. Establish `hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E` using `E) v := by`. Take `⟨u, hne, hu⟩` from `id hw`. Substitute `hvw` using the available equality.

Conclude with `⟨w, u, hne.symm, rfl, congrArg HeightOneSpectrum.asIdeal hu⟩`. Take `⟨t, rfl⟩` from `GlobalTheory.LFun.SplitChart.exists_splitPrime_eq (GlobalTheory.GalOfCusp.isCMExt_real E) hv hvw`. Take `⟨τ, hτ, hs⟩` from `hB`. Take `⟨⟨τ', hτ'⟩, -⟩` from `GlobalTheory.T.exists_unique_splitPlaceComponent_definiteUnitary E d U' hL.aut _ hw`. Conclude with `⟨τ', hτ', hPS E n d hnd v t χX χW τ τ' (hL.loc v t τ τ' hτ hτ') (hCU E n U hU _ hw τ hτ) hX hW B hs⟩`.
-/
theorem UpperTheory.Gal.TP.Loc.liftSatU :
    UpperTheory.Gal.TP.Loc.PairSat → UpperTheory.Gal.TP.Loc.CompUnit → UpperTheory.Gal.TP.Loc.LiftSatU := by
  intro hPS hCU E _ _ _ n d hnd Bs χX χW mX mW lam U U' hU hL w hw hX hW B hB
  obtain ⟨v, hvw⟩ : ∃ v, w.under (𝓞 (maximalRealSubfield E)) = v := ⟨_, rfl⟩
  have hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v := by
    obtain ⟨u, hne, hu⟩ := id hw
    subst hvw
    exact ⟨w, u, hne.symm, rfl, congrArg HeightOneSpectrum.asIdeal hu⟩
  obtain ⟨t, rfl⟩ := GlobalTheory.LFun.SplitChart.exists_splitPrime_eq (GlobalTheory.GalOfCusp.isCMExt_real E) hv hvw
  obtain ⟨τ, hτ, hs⟩ := hB
  obtain ⟨⟨τ', hτ'⟩, -⟩ := GlobalTheory.T.exists_unique_splitPlaceComponent_definiteUnitary E d U' hL.aut _ hw
  exact ⟨τ', hτ', hPS E n d hnd v t χX χW τ τ' (hL.loc v t τ τ' hτ hτ')
    (hCU E n U hU _ hw τ hτ) hX hW B hs⟩
