import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientSubContinuitySetup

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
open GlobalTheory.NLink.AmbSub

namespace UpperTheory.N

/- English proof (translation)
Take `⟨_, hG2, _, _, _, _, _, _, hCont, _, _, _, _, _, hFont, _, _⟩` from `hS`. Establish `hcx : ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i) (v : Fin D.R.nV → ↥C.LL.1), Continuous fun g => (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x) g).mulV …` using `fun w hw C x v => locC_cont D i _ (rTwO_cont D i (X.r i) hCont x) w hw C v`. Establish `hcr : ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i), IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x)))`. Introduce `w hw C x`. Rewrite using `[locC_rTwO]`.

Conclude with `(hG2 w hw C).2 x`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `_ _ w hw _ C A hA`. Establish `hJ : ∀ x τ, JumpsInV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x))) τ {a | IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) π))) τ a}`. Introduce `x τ`.

Use `jumps_of_multV_eq (O := ↥(OL C.LL)) (fun x => TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x)) (hcx w hw C) (hFont w hw C) x π (hcr w hw C x) (hcr w hw C π) τ (fun a => ?_)` and prove the remaining obligations. Rewrite using `[locC_rTwO, locC_rTwO]`. Conclude with `(hG2 w hw C).1.2.1 τ x π a`. Conclude with `subsum_crys (fun x => TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x)) (hcx w hw C) (hFont w hw C) (hcr w hw C) hJ A hA`. Introduce `w hw C`.

Use `⟨fun x v => hcx w hw C x v, fun _ => ⟨fun v => ?_, fun v => ?_⟩⟩` and prove the remaining obligations. Conclude with `locC_cont D i _ (WpO_cont i (X.ρ i) π hρ) w hw C v`. Conclude with `locC_cont D i _ (GlobalTheory.TwistedDualLoc.continuous_T2O D i (X.ρ i) π hρ) w hw C v`. Introduce `_ w hw _ C`. Conclude with `(hG2 w hw C).1.2.2.2.2.2.1`.
-/
theorem amb_of_setPt {D : D7} (i : D.nd.Loc) (X : KillingConditions.HubData D) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i)
    (hS : SetPt i (X.r i) (X.ρ i) π)
    (hρ : Continuous fun g => ((X.ρ i π g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) :
    EmbeddingTypes.ambSub i (X.r i) π dc ∧ EmbeddingTypes.ambCont i (X.r i) (X.ρ i) π ∧ EmbeddingTypes.ColumnH0Vanishing i (X.ρ i) π dc := by
  obtain ⟨_, hG2, _, _, _, _, _, _, hCont, _, _, _, _, _, hFont, _, _⟩ := hS
  have hcx : ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i) (v : Fin D.R.nV → ↥C.LL.1),
      Continuous fun g => (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x) g).mulVec v :=
    fun w hw C x v => locC_cont D i _ (rTwO_cont D i (X.r i) hCont x) w hw C v
  have hcr : ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i),
      IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x))) := by
    intro w hw C x
    rw [locC_rTwO]
    exact (hG2 w hw C).2 x
  refine ⟨?_, ?_, ?_⟩
  · intro _ _ w hw _ C A hA
    have hJ : ∀ x τ, JumpsInV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x))) τ
        {a | IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) π))) τ a} := by
      intro x τ
      refine jumps_of_multV_eq (O := ↥(OL C.LL)) (fun x => TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x)) (hcx w hw C)
        (hFont w hw C) x π (hcr w hw C x) (hcr w hw C π) τ (fun a => ?_)
      rw [locC_rTwO, locC_rTwO]
      exact (hG2 w hw C).1.2.1 τ x π a
    exact subsum_crys (fun x => TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x)) (hcx w hw C) (hFont w hw C)
      (hcr w hw C) hJ A hA
  · intro w hw C
    refine ⟨fun x v => hcx w hw C x v, fun _ => ⟨fun v => ?_, fun v => ?_⟩⟩
    · exact locC_cont D i _ (WpO_cont i (X.ρ i) π hρ) w hw C v
    · exact locC_cont D i _ (GlobalTheory.TwistedDualLoc.continuous_T2O D i (X.ρ i) π hρ) w hw C v
  · intro _ w hw _ C
    exact (hG2 w hw C).1.2.2.2.2.2.1

end UpperTheory.N

end
