import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecT
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramifiedNonsplitExistsConjInvolutionUniformise
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightContragredientExistsUnique
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDictionaryCmFieldAutomorphicStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertSatakeParametersAgreeUnderDictionaryStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdeleIdentificationNonemptyPresentaStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSatakeParameterInertDatumOfDictionarySpherStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentsAgreeSplitPlaceDictionaryStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicWeightAgreesUnderModularFormDictionaryStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.UnitaryReadTrue

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem host_conj_eq (D : D7) (x : D.host.E) : D.host.conj x = IsCMField.complexConj D.host.E x :=
  D.host.φ₀.injective (by
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem coe_cO (D : D7) (x : 𝓞 D.host.E) :
    ((IsCMField.ringOfIntegersComplexConj D.host.E x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) := by
  rw [IsCMField.coe_ringOfIntegersComplexConj, host_conj_eq]

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_splitPlace_w (D : D7) (w : PlE D.host) (hw : IsSplitPl D.host w) :
    ∃ s : SplitPlace D.host.E, s.w = w := by
  obtain ⟨s, -, hc, -⟩ := GlobalTheory.SplitConjPlace.splitEx_all D w hw
  refine ⟨GlobalTheory.SplitConjPlace.conjSP s, HeightOneSpectrum.ext (Ideal.ext fun x => ?_)⟩
  rw [GlobalTheory.SplitConjPlace.mem_conj_w]
  exact (hc x _ (coe_cO D x)).symm

/- English proof (translation)
Assume the hypotheses and unpack their components. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem not_isSplitAt (D : D7) (w : PlE D.host) (hw : ¬ IsSplitPl D.host w) : ¬ IsSplitAt w := by
  rintro ⟨u, hu, he⟩
  apply hw
  have hu' : u = GlobalTheory.SplitConjPlace.conjPlE w := by
    rcases GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE w u (congrArg HeightOneSpectrum.asIdeal he) with h | h
    · exact absurd h hu
    · exact h
  have hne : GlobalTheory.SplitConjPlace.conjPlE w ≠ w := hu' ▸ hu
  have hle : ¬ w.asIdeal ≤ (GlobalTheory.SplitConjPlace.conjPlE w).asIdeal := fun hle =>
    hne (HeightOneSpectrum.ext (w.isMaximal.eq_of_le (GlobalTheory.SplitConjPlace.conjPlE w).isPrime.ne_top hle)).symm
  obtain ⟨x, hx, hx'⟩ := Set.not_subset.mp hle
  refine ⟨x, hx, fun y hy hyw => hx' ?_⟩
  refine (GlobalTheory.SplitConjPlace.mem_conjPlE w x).2 ?_
  have : y = IsCMField.ringOfIntegersComplexConj D.host.E x := RingOfIntegers.ext (by rw [hy, coe_cO])
  rwa [← this]

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Expand and normalize the polynomial expressions, which then agree.
-/
theorem infOf_eq_infOfWeight {n : ℕ} (lam : DomWeight n) : NG.infOf lam.w = infOfWeight lam := by
  unfold NG.infOf infOfWeight
  congr 1
  funext k
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression.

Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Apply function extensionality and compare values at an arbitrary argument. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem unitaryRead_true : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (A : AUSide D),
    AUTrue hL D T A → UnitaryRead D.nbc (recT T hL) := by
  intro hL D T A hA j h1 h2 π
  obtain ⟨π₀, rfl⟩ := A.surj j h1 h2 π
  obtain ⟨F⟩ := GlobalTheory.T.unitaryFiniteAdeleIdentification_nonempty_presentations D.host.E D.R.nV
  obtain ⟨U, hU⟩ := GlobalTheory.T.exists_dictionary_cm_field_automorphic D.host.E D.R.nV F π₀
  refine ⟨U, hU.1, ?_, ?_, ?_⟩
  · intro w hw σ hσ
    obtain ⟨s, rfl⟩ := exists_splitPlace_w D w hw
    obtain ⟨τ, hτ, ⟨e⟩⟩ := GlobalTheory.T.localComponents_agree_splitPlace_dictionary _ _ F π₀ U hU s σ hσ
    have h := hA j h1 h2 π₀ s τ hτ
    show _ = (T.e s.w).symm _
    have hc : GlobalTheory.LocLanglands.cls τ = GlobalTheory.LocLanglands.cls (ParLaws.toRep σ) := by
      unfold GlobalTheory.LocLanglands.cls
      rw [(GlobalTheory.SmGL.IrrRep.cl_eq_iff (σ := τ) (τ := ParLaws.toRep σ)).2 ⟨e⟩]
    rw [Equiv.eq_symm_apply, h, hc]
  · intro w hw hsph
    let v := GlobalTheory.SplitConjPlace.belowE (D := D) w
    have hv : NG.OverPl w v := rfl
    have hsph0 := (A.sph j h1 h2 π₀ w v hw hv).1 hsph
    obtain ⟨s, ϖ, q, hs, hq⟩ :=
      GlobalTheory.InertPlaceConj.exists_conj_isUnramInv D.host.E w (host_unramified D.host w) (not_isSplitAt D w hw)
    obtain ⟨-, hI⟩ := GlobalTheory.T.inert_satake_parameters_agree_under_dictionary _ _ F π₀ U hU v w hv
    obtain ⟨⟨Dv, hDs, hDϖ⟩, hI2⟩ := hI s ϖ q hs hq
    obtain ⟨α, hα, hsat⟩ := A.sat j h1 h2 π₀ v w hv Dv (GlobalTheory.T.exists_satakeParameter_inertDatum_of_dictionary_spherical _ _ F π₀ U hU v w hv hsph0 Dv)
    obtain ⟨α', hα', hS⟩ := hI2 Dv α hDs hDϖ hα
    refine ⟨α', ⟨s, ϖ, q, hs, hq, hS⟩, ?_⟩
    rw [hsat]
    congr 1
    funext i
    exact (hα' i).symm
  · intro τ
    obtain ⟨b, hb, -⟩ := GlobalTheory.algWt_contragredient _ _ π₀.toAlgWt
    obtain ⟨lam, hl, hhw⟩ := GlobalTheory.T.algebraicWeight_agrees_under_modularForm_dictionary _ _ F π₀ U hU b hb τ
    refine ⟨lam, hl, ?_⟩
    rw [A.wt j h1 h2 π₀ b hb, A.infW j h1 h2 b τ lam.w hhw, infOf_eq_infOfWeight]

end GlobalTheory.UnitaryReadTrue
