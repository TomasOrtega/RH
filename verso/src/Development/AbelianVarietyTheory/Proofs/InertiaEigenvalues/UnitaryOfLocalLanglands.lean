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
The claim follows from `D.host.φ₀.injective (by rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])`.
-/
theorem host_conj_eq (D : D7) (x : D.host.E) : D.host.conj x = IsCMField.complexConj D.host.E x :=
  D.host.φ₀.injective (by
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])

/- English proof (translation)
Rewrite using `[IsCMField.coe_ringOfIntegersComplexConj, host_conj_eq]`.
-/
theorem coe_cO (D : D7) (x : 𝓞 D.host.E) :
    ((IsCMField.ringOfIntegersComplexConj D.host.E x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) := by
  rw [IsCMField.coe_ringOfIntegersComplexConj, host_conj_eq]

/- English proof (translation)
Take `⟨s, -, hc, -⟩` from `GlobalTheory.SplitConjPlace.splitEx_all D w hw`. Use `⟨GlobalTheory.SplitConjPlace.conjSP s, HeightOneSpectrum.ext (Ideal.ext fun x => ?_)⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.SplitConjPlace.mem_conj_w]`. Conclude with `(hc x _ (coe_cO D x)).symm`.
-/
theorem exists_splitPlace_w (D : D7) (w : PlE D.host) (hw : IsSplitPl D.host w) :
    ∃ s : SplitPlace D.host.E, s.w = w := by
  obtain ⟨s, -, hc, -⟩ := GlobalTheory.SplitConjPlace.splitEx_all D w hw
  refine ⟨GlobalTheory.SplitConjPlace.conjSP s, HeightOneSpectrum.ext (Ideal.ext fun x => ?_)⟩
  rw [GlobalTheory.SplitConjPlace.mem_conj_w]
  exact (hc x _ (coe_cO D x)).symm

/- English proof (translation)
Introduce and unpack `⟨u, hu, he⟩`. Apply `hw` to reduce the goal to its premises. Establish `hu' : u = GlobalTheory.SplitConjPlace.conjPlE w`. Break down `GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE w u (congrArg HeightOneSpectrum.asIdeal he) with h | h` into its components or cases. Conclude with `absurd h hu`.

Conclude with `h`. Establish `hne : GlobalTheory.SplitConjPlace.conjPlE w ≠ w` using `hu' ▸ hu`. Establish `hle : ¬ w.asIdeal ≤ (GlobalTheory.SplitConjPlace.conjPlE w).asIdeal` using `fun hle => hne (HeightOneSpectrum.ext (w.isMaximal.eq_of_le (GlobalTheory.SplitConjPlace.conjPlE w).isPrime.ne_top hle)).symm`. Take `⟨x, hx, hx'⟩` from `Set.not_subset.mp hle`. Use `⟨x, hx, fun y hy hyw => hx' ?_⟩` and prove the remaining obligations.

Use `(GlobalTheory.SplitConjPlace.mem_conjPlE w x).2 ?_` and prove the remaining obligations. Establish `: y = IsCMField.ringOfIntegersComplexConj D.host.E x` using `RingOfIntegers.ext (by rw [hy, coe_cO])`. Rewrite using `[← this]` and apply the resulting hypothesis.
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
Unfold `NG.infOf infOfWeight`. Use `congr 1`. Use function extensionality and compare the values at `k`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem infOf_eq_infOfWeight {n : ℕ} (lam : DomWeight n) : NG.infOf lam.w = infOfWeight lam := by
  unfold NG.infOf infOfWeight
  congr 1
  funext k
  ring

/- English proof (translation)
Introduce `hL D T A hA j h1 h2 π`. Take `⟨π₀, rfl⟩` from `A.surj j h1 h2 π`. Take `⟨F⟩` from `GlobalTheory.T.unitaryFiniteAdeleIdentification_nonempty_presentations D.host.E D.R.nV`. Take `⟨U, hU⟩` from `GlobalTheory.T.exists_dictionary_cm_field_automorphic D.host.E D.R.nV F π₀`. Use `⟨U, hU.1, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `w hw σ hσ`. Take `⟨s, rfl⟩` from `exists_splitPlace_w D w hw`. Take `⟨τ, hτ, ⟨e⟩⟩` from `GlobalTheory.T.localComponents_agree_splitPlace_dictionary _ _ F π₀ U hU s σ hσ`. Establish `h` using `hA j h1 h2 π₀ s τ hτ`. Use `show _ = (T.e s.w).symm _`.

Establish `hc : GlobalTheory.LocLanglands.cls τ = GlobalTheory.LocLanglands.cls (ParLaws.toRep σ)`. Unfold `GlobalTheory.LocLanglands.cls`. Rewrite using `[(GlobalTheory.SmGL.IrrRep.cl_eq_iff (σ := τ) (τ := ParLaws.toRep σ)).2 ⟨e⟩]`. Rewrite using `[Equiv.eq_symm_apply, h, hc]`. Introduce `w hw hsph`.

Set `v` to `GlobalTheory.SplitConjPlace.belowE (D := D) w`. Establish `hv : NG.OverPl w v` using `rfl`. Establish `hsph0` using `(A.sph j h1 h2 π₀ w v hw hv).1 hsph`. Take `⟨s, ϖ, q, hs, hq⟩` from `GlobalTheory.InertPlaceConj.exists_conj_isUnramInv D.host.E w (host_unramified D.host w) (not_isSplitAt D w hw)`. Take `⟨-, hI⟩` from `GlobalTheory.T.inert_satake_parameters_agree_under_dictionary _ _ F π₀ U hU v w hv`.

Take `⟨⟨Dv, hDs, hDϖ⟩, hI2⟩` from `hI s ϖ q hs hq`. Take `⟨α, hα, hsat⟩` from `A.sat j h1 h2 π₀ v w hv Dv (GlobalTheory.T.exists_satakeParameter_inertDatum_of_dictionary_spherical _ _ F π₀ U hU v w hv hsph0 Dv)`. Take `⟨α', hα', hS⟩` from `hI2 Dv α hDs hDϖ hα`. Use `⟨α', ⟨s, ϖ, q, hs, hq, hS⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hsat]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `(hα' i).symm`. Introduce `τ`. Take `⟨b, hb, -⟩` from `GlobalTheory.algWt_contragredient _ _ π₀.toAlgWt`.

Take `⟨lam, hl, hhw⟩` from `GlobalTheory.T.algebraicWeight_agrees_under_modularForm_dictionary _ _ F π₀ U hU b hb τ`. Use `⟨lam, hl, ?_⟩` and prove the remaining obligations. Rewrite using `[A.wt j h1 h2 π₀ b hb, A.infW j h1 h2 b τ lam.w hhw, infOf_eq_infOfWeight]`.
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
