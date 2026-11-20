import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftPairDefinitePlaceCharacterDataStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteScalarComponentIsCuspAndCongruenceFixedAStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarComponentParametersContainStringStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeStringGivesSimplePoleHypothesesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftFockVectorsSphericalPrincipalFixedStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealIntegralThetaLiftDefiniteFormNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralQuotientEqSetIntegralFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicUnitaryTopCong
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

namespace GlobalTheory.Core.Rk.NonVanAt

/- English proof (translation)
Establish `hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ A) (fun g => thetaKO om g h f * u g)`. Introduce `γ hγ g`. Establish `e : ((γ * g, h) : GA D A × GA D W) = (γ, 1) * (g, h)` using `by simp`. Establish `h1 : thetaKO om (γ * g) h f = thetaKO om g h f`. Unfold `thetaKO`.

Rewrite using `[e, map_mul, Module.End.mul_apply]`. Conclude with `hW.om_aut γ hγ 1 (one_mem _) _ (hW.om_pres _ _ hf)`. Use `show thetaKO om (γ * g) h f * u (γ * g) = thetaKO om g h f * u g`. Rewrite using `[h1, hu γ hγ g]`. Rewrite using `[GlobalTheory.Core.Rk.IP.up, GlobalTheory.AutomorphicL2Unitary.autMeasure, GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure hX]`.

Simplify using `only [hL.descend_mk]`.
-/
theorem up_eq_setIntegral {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {A W : HSp D} {χA χW : (AE D)ˣ →* Circle}
    {om : GlobalTheory.Core.Rk.IP.WRep A W} (hW : IsWeilDatumO ψ A W χA χW om) {m : Measure (GA D A)} {X : Set (GA D A)}
    (hm : m.IsHaarMeasure) (hX : IsFundamentalDomain (GQ A) X m) {f : WO A W → ℂ} (hf : IsThetaFunO ψ A W f)
    {u : GA D A → ℂ} (hu : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ A) u) (h : GA D W) :
    GlobalTheory.Core.Rk.IP.up om m f u h = ∫ g in X, thetaKO om g h f * u g ∂m := by
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ A) (fun g => thetaKO om g h f * u g) := by
    intro γ hγ g
    have e : ((γ * g, h) : GA D A × GA D W) = (γ, 1) * (g, h) := by simp
    have h1 : thetaKO om (γ * g) h f = thetaKO om g h f := by
      unfold thetaKO
      rw [e, map_mul, Module.End.mul_apply]
      exact hW.om_aut γ hγ 1 (one_mem _) _ (hW.om_pres _ _ hf)
    show thetaKO om (γ * g) h f * u (γ * g) = thetaKO om g h f * u g
    rw [h1, hu γ hγ g]
  rw [GlobalTheory.Core.Rk.IP.up, GlobalTheory.AutomorphicL2Unitary.autMeasure, GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure hX]
  simp only [hL.descend_mk]

/- English proof (translation)
Simplify using `[GlobalTheory.Core.Rk.IP.rcoef, GlobalTheory.Cusp.petersson, GlobalTheory.AutomorphicL2Unitary.pet, GlobalTheory.AutomorphicL2Unitary.descend]`.
-/
theorem rcoef_zero {D : D7} {A : HSp D} (m : Measure (GA D A)) (b : GA D A) : GlobalTheory.Core.Rk.IP.rcoef m 0 0 b = 0 := by
  simp [GlobalTheory.Core.Rk.IP.rcoef, GlobalTheory.Cusp.petersson, GlobalTheory.AutomorphicL2Unitary.pet, GlobalTheory.AutomorphicL2Unitary.descend]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D hD G _ _ Pl0 T A Ks _ _ _ R F hG hP i t h hh s hs y hy hy0`. Take `⟨⟨cA, a, hdef⟩, hpl, hun, hunr, hη, hsig, hrW, hr0, hrV, -, -, -⟩` from `GlobalTheory.T.thetaLiftPair_definite_place_character_data D G Pl0 T A Ks R F hG hP i t`. Take `⟨hlev, hX⟩` from `hG.core.models.νV i t`. Establish `hm : (R.νV i t).IsHaarMeasure` using `hlev.1`. Establish `hW` using `hG.core.thP.ωP i t`.

Take `⟨l, P, hreal⟩` from `GlobalTheory.T.realIntegral_thetaLift_definiteForm_ne_zero D G Pl0 T A Ks R F hG hP i t y hy0 (R.νV i t) hm`. Take `⟨hA0, hfix⟩` from `GlobalTheory.T.linearForm_extV_mem_A0_and_prin_invariant D G Pl0 T A Ks R F hG hP i t cA a hdef y l`. Take `⟨B, c, hB, hHyp⟩` from `GlobalTheory.T.satake_string_gives_simple_pole_hypotheses D G Pl0 T A Ks R F hG hP i t s hs`. Take `⟨hcart, hfock, hsph, hfixΦ⟩` from `GlobalTheory.T.thetaLiftFockVectors_spherical_principalFixed D G Pl0 T A Ks R F hG hP i t P`. Establish `hu0 : (fun g => l (R.extV i t y g)) ≠ 0`.

Introduce `h0`. Take `⟨ν, 𝓕, hν⟩` from `GlobalTheory.Size.exists_isCovolOne (Vc D i) (Wc D i)`. Take `⟨i1, i2, i3, i4, i5, i6, -⟩` from `GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D (Vc D i)`. Establish `: LocallyCompactSpace (GinfC (Vc D i))` using `i6.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Establish `: BorelSpace (GinfC (Vc D i))` using `Subtype.borelSpace _`.

Use `hreal ν 𝓕 hν Measure.haar inferInstance ?_` and prove the remaining obligations. Rewrite using `[h0]`. Simplify using `only [rcoef_zero, mul_zero, integral_zero]`. Establish `hpar` using `GlobalTheory.T.scalarComponent_parameters_contain_string D G Pl0 T A Ks R F hG hP i t h hh s y hy l hu0 B hB`. Establish `hpar' : GlobalTheory.LFun.IsParamFunV (Vc D i) (under (R.Pg ∪ R.Q t)) (fun g => l (R.extV i t y g)) B` using `hun.symm ▸ hpar`.

Establish `hHyp' : GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.Hyp (under (D` using `D) (R.Pg ∪ R.Q t) : Set (HeightOneSpectrum (𝓞 D.host.F))) (Wc D i).rank D.R.t c B (GlobalTheory.LFun.val (F := D.host.F) (chiV R i t)) (GlobalTheory.LFun.val (F := D.host.F) (chiV R i t)) := by`. Rewrite using `[hrW, hun]`. Conclude with `hHyp`. Establish `hF : Form R.θ (Vc D i) cA (R.βV i) (R.Pg ∪ R.Q t) (chiV R i t) (Wc D i).rank D.R.t (fun g => l (R.extV i t y g)) B`. Use `⟨hA0, hfix, ?_, hunr, c, ?_⟩` and prove the remaining obligations.

Conclude with `hpar'`. Conclude with `hHyp'`. Establish `hO : Occ R.ψ R.θ (cart (R.MW i (sg0 D A))) (R.ωP i t) (R.νV i t) (R.βV i) (R.Pg ∪ R.Q t) (fun g => l (R.extV i t y g)) (R.ptP i t P)` using `⟨hcart, hfock, hsph, hfixΦ, hreal⟩`. Establish `hW' : IsWeilDatumO R.ψ (Vc D i) (Wc D i) (chiW R i t) (chiV R i t) (R.ωP i t)` using `hW`. Establish `hr1 : 0 < (Wc D i).rank` using `by rw [hrW]; exact hr0`.

Establish `hr2 : (Vc D i).rank = (Wc D i).rank + D.R.t` using `by rw [hrW]; exact hrV`. Establish `key` using `hD R.ψ R.θ (Vc D i) (Wc D i) D.R.t (chiW R i t) (chiV R i t) (R.ωP i t) cA a (R.βV i) (R.Pg ∪ R.Q t) (R.νV i t) (fun g => l (R.extV i t y g)) B (cart (R.MW i (sg0 D A))) (R.ptP i t P) hdef hsig hr1 hr2 hη hW' hpl hm hF hO`. Assume the negation of the conclusion as `hno`. Use `key fun f hf g => ?_` and prove the remaining obligations. Rewrite using `[up_eq_setIntegral hW hm hX hf (GlobalTheory.AutomorphicL2Unitary.leftInv_of_isAutFun (Submodule.mem_inf.1 hA0).1.1.toIsAutFun)]`.

Assume the negation of the conclusion as `hne`. Conclude with `hno ⟨f, l, g, hf, hne⟩`.
-/
theorem nonVan_of_downNe : ∀ (D : D7) (_ : DownNe D) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, NonVan R i t := by
  intro D hD G _ _ Pl0 T A Ks _ _ _ R F hG hP i t h hh s hs y hy hy0
  obtain ⟨⟨cA, a, hdef⟩, hpl, hun, hunr, hη, hsig, hrW, hr0, hrV, -, -, -⟩ := GlobalTheory.T.thetaLiftPair_definite_place_character_data D G Pl0 T A Ks R F hG hP i t
  obtain ⟨hlev, hX⟩ := hG.core.models.νV i t
  have hm : (R.νV i t).IsHaarMeasure := hlev.1
  have hW := hG.core.thP.ωP i t
  obtain ⟨l, P, hreal⟩ := GlobalTheory.T.realIntegral_thetaLift_definiteForm_ne_zero D G Pl0 T A Ks R F hG hP i t y hy0 (R.νV i t) hm
  obtain ⟨hA0, hfix⟩ := GlobalTheory.T.linearForm_extV_mem_A0_and_prin_invariant D G Pl0 T A Ks R F hG hP i t cA a hdef y l
  obtain ⟨B, c, hB, hHyp⟩ := GlobalTheory.T.satake_string_gives_simple_pole_hypotheses D G Pl0 T A Ks R F hG hP i t s hs
  obtain ⟨hcart, hfock, hsph, hfixΦ⟩ := GlobalTheory.T.thetaLiftFockVectors_spherical_principalFixed D G Pl0 T A Ks R F hG hP i t P
  have hu0 : (fun g => l (R.extV i t y g)) ≠ 0 := by
    intro h0
    obtain ⟨ν, 𝓕, hν⟩ := GlobalTheory.Size.exists_isCovolOne (Vc D i) (Wc D i)
    obtain ⟨i1, i2, i3, i4, i5, i6, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D (Vc D i)
    have : LocallyCompactSpace (GinfC (Vc D i)) := i6.isClosedEmbedding_subtypeVal.locallyCompactSpace
    have : BorelSpace (GinfC (Vc D i)) := Subtype.borelSpace _
    refine hreal ν 𝓕 hν Measure.haar inferInstance ?_
    rw [h0]
    simp only [rcoef_zero, mul_zero, integral_zero]
  have hpar := GlobalTheory.T.scalarComponent_parameters_contain_string D G Pl0 T A Ks R F hG hP i t h hh s y hy l hu0 B hB
  have hpar' : GlobalTheory.LFun.IsParamFunV (Vc D i) (under (R.Pg ∪ R.Q t)) (fun g => l (R.extV i t y g)) B :=
    hun.symm ▸ hpar
  have hHyp' : GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.Hyp (under (D := D) (R.Pg ∪ R.Q t) : Set (HeightOneSpectrum (𝓞 D.host.F))) (Wc D i).rank D.R.t c B
      (GlobalTheory.LFun.val (F := D.host.F) (chiV R i t)) (GlobalTheory.LFun.val (F := D.host.F) (chiV R i t)) := by
    rw [hrW, hun]; exact hHyp
  have hF : Form R.θ (Vc D i) cA (R.βV i) (R.Pg ∪ R.Q t) (chiV R i t) (Wc D i).rank D.R.t (fun g => l (R.extV i t y g)) B := by
    refine ⟨hA0, hfix, ?_, hunr, c, ?_⟩
    · exact hpar'
    · exact hHyp'
  have hO : Occ R.ψ R.θ (cart (R.MW i (sg0 D A))) (R.ωP i t) (R.νV i t) (R.βV i) (R.Pg ∪ R.Q t)
      (fun g => l (R.extV i t y g)) (R.ptP i t P) := ⟨hcart, hfock, hsph, hfixΦ, hreal⟩
  have hW' : IsWeilDatumO R.ψ (Vc D i) (Wc D i) (chiW R i t) (chiV R i t) (R.ωP i t) := hW
  have hr1 : 0 < (Wc D i).rank := by rw [hrW]; exact hr0
  have hr2 : (Vc D i).rank = (Wc D i).rank + D.R.t := by rw [hrW]; exact hrV
  have key := hD R.ψ R.θ (Vc D i) (Wc D i) D.R.t (chiW R i t) (chiV R i t) (R.ωP i t) cA a (R.βV i) (R.Pg ∪ R.Q t)
    (R.νV i t) (fun g => l (R.extV i t y g)) B (cart (R.MW i (sg0 D A))) (R.ptP i t P) hdef hsig hr1 hr2 hη hW' hpl hm hF hO
  by_contra hno
  refine key fun f hf g => ?_
  rw [up_eq_setIntegral hW hm hX hf (GlobalTheory.AutomorphicL2Unitary.leftInv_of_isAutFun (Submodule.mem_inf.1 hA0).1.1.toIsAutFun)]
  by_contra hne
  exact hno ⟨f, l, g, hf, hne⟩

end GlobalTheory.Core.Rk.NonVanAt
