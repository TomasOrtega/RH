import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideReadHeckeOfAdmissibleTwistStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConductorLevelComparisonParamodularPlace
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CellPlacesDisjointOfSeparated
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistCharacterTamelyRamifiedAtPlace
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConductorValuationQComparison
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConductorValuationDeltaComparison
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameLevelValueTrivialAtWildPlace
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
noncomputable section
namespace GlobalTheory.XPara
/- English proof (translation)
Introduce `hPr hL`. Use `(StepW.and (_root_.GlobalTheory.T.conductor_level_le_at_twisted_place_of_twOK hPr hL) (StepW.and (_root_.GlobalTheory.T.cell_places_disjoint_of_admTw hPr hL) (StepW.and (_root_.GlobalTheory.T.twist_character_tamely_ramified_at_place' hPr hL) (StepW.and (_root_.GlobalTheory.T.cond …` and prove the remaining obligations. Take `⟨h1, h2, h3, h4, h5, h6⟩` from `H`. Introduce `u hu`. Take `⟨P', hP', hPu⟩` from `h1 P x l v i b ψ hA j htw hl hok u hu`.

Take `⟨hex, hg, hq, hd⟩` from `h2 P x l v i b ψ hA j htw hl hok P' hP'`. Take `⟨hwq, hwd⟩` from `h6 P x l v i b ψ hA j htw hl hok`. Establish `hT` using `h3 P x l v i b ψ hA j htw hl hok P' hP'`. Establish `hw : ((cell (D` using `Dof x) l.b.Bs.exp b hA j).sp P').w = P' := (cell (D := Dof x) l.b.Bs.exp b hA j).sp_w P' (hP'.elim Or.inl fun h => Or.inr (Or.inl h))`. Rewrite `hT` using `[← hw]`.

Take `⟨ξ, hξc, hξv⟩` from `GlobalTheory.HeckeSplitComp.main _ ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P') _ hT`. Use `⟨(cell (D := Dof x) l.b.Bs.exp b hA j).sp P', ξ, hPu, hξc, ?_⟩` and prove the remaining obligations. Establish `hne : ∀ a : 𝓞 (Dof x).host.E, a ∉ P'.asIdeal → (a : (Dof x).host.E) ≠ 0` using `fun a ha h0 => ha (by rw [show a = 0 from by exact_mod_cast h0]; exact Ideal.zero_mem _)`. Use `GlobalTheory.T.levelByPlaces_parahoric_at_conductorPlace_tameCharacter _ _ _ _ _ _ _ _ _ _ _ _ e P' ξ hP' hex hg hq hd hwq hwd ?_ ?_` and prove the remaining obligations. Introduce `hq' y a ha hy1 hya`.

Rewrite using `[hξv y a (Units.mk0 _ (hne a ha)) rfl hy1 hya, hw]`. Conclude with `(h4 P x l v i b ψ hA j htw hl hok e hS hR P' hq' a _ ha rfl).symm`. Introduce `hd' y a ha hy1 hya`. Rewrite using `[hξv y a (Units.mk0 _ (hne a ha)) rfl hy1 hya, hw]`. Conclude with `(h5 P x l v i b ψ hA j htw hl hok e hS hR P' hd' a _ ha rfl).symm`.
-/
theorem parahoric_shape_transfer_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ e, SideRead i b (T.k v) e → ReadsHecke e ψ (T.psi v) → ParaShape (Dof x) (eta (D := Dof x) (cfOf x) w.I.xi v j) (cell (D := Dof x) l.b.Bs.exp b hA j).J (cx e (cell (D := Dof x) l.b.Bs.exp b hA j).χ) := by
  intro hPr hL
  refine (StepW.and (_root_.GlobalTheory.T.conductor_level_le_at_twisted_place_of_twOK hPr hL) (StepW.and (_root_.GlobalTheory.T.cell_places_disjoint_of_admTw hPr hL) (StepW.and (_root_.GlobalTheory.T.twist_character_tamely_ramified_at_place' hPr hL)
    (StepW.and (_root_.GlobalTheory.T.conductor_valuation_q_le_of_sideRead hPr hL) (StepW.and (_root_.GlobalTheory.T.conductor_valuation_delta_le_of_sideRead hPr hL) (_root_.GlobalTheory.T.tw_ok_value_trivial_at_twisted_place hPr hL)))))).trans
    (StepW.of_all fun K B f T w _ _ H P x l v i b ψ hA j htw hl hok e hS hR => ?_)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := H
  intro u hu
  obtain ⟨P', hP', hPu⟩ := h1 P x l v i b ψ hA j htw hl hok u hu
  obtain ⟨hex, hg, hq, hd⟩ := h2 P x l v i b ψ hA j htw hl hok P' hP'
  obtain ⟨hwq, hwd⟩ := h6 P x l v i b ψ hA j htw hl hok
  have hT := h3 P x l v i b ψ hA j htw hl hok P' hP'
  have hw : ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P').w = P' :=
    (cell (D := Dof x) l.b.Bs.exp b hA j).sp_w P' (hP'.elim Or.inl fun h => Or.inr (Or.inl h))
  rw [← hw] at hT
  obtain ⟨ξ, hξc, hξv⟩ := GlobalTheory.HeckeSplitComp.main _ ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P') _ hT
  refine ⟨(cell (D := Dof x) l.b.Bs.exp b hA j).sp P', ξ, hPu, hξc, ?_⟩
  have hne : ∀ a : 𝓞 (Dof x).host.E, a ∉ P'.asIdeal → (a : (Dof x).host.E) ≠ 0 := fun a ha h0 =>
    ha (by rw [show a = 0 from by exact_mod_cast h0]; exact Ideal.zero_mem _)
  refine GlobalTheory.T.levelByPlaces_parahoric_at_conductorPlace_tameCharacter _ _ _ _ _ _ _ _ _ _ _ _ e P' ξ hP' hex hg hq hd hwq hwd ?_ ?_
  · intro hq' y a ha hy1 hya
    rw [hξv y a (Units.mk0 _ (hne a ha)) rfl hy1 hya, hw]
    exact (h4 P x l v i b ψ hA j htw hl hok e hS hR P' hq' a _ ha rfl).symm
  · intro hd' y a ha hy1 hya
    rw [hξv y a (Units.mk0 _ (hne a ha)) rfl hy1 hya, hw]
    exact (h5 P x l v i b ψ hA j htw hl hok e hS hR P' hd' a _ ha rfl).symm
end GlobalTheory.XPara
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @_root_.GlobalTheory.XPara.parahoric_shape_transfer_alt | exact _root_.GlobalTheory.XPara.parahoric_shape_transfer_alt | (intros; apply _root_.GlobalTheory.XPara.parahoric_shape_transfer_alt <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.paraShape_of_twisted_sideRead_readsHecke : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ e, SideRead i b (T.k v) e → ReadsHecke e ψ (T.psi v) → ParaShape (Dof x) (eta (D := Dof x) (cfOf x) w.I.xi v j) (cell (D := Dof x) l.b.Bs.exp b hA j).J (cx e (cell (D := Dof x) l.b.Bs.exp b hA j).χ) := by
  first | exact @_root_.GlobalTheory.XPara.parahoric_shape_transfer_alt | exact _root_.GlobalTheory.XPara.parahoric_shape_transfer_alt | (intros; apply _root_.GlobalTheory.XPara.parahoric_shape_transfer_alt <;> assumption)
end
end
