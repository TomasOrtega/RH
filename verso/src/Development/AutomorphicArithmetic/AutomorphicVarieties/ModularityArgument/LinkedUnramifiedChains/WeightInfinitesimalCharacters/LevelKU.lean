import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.WeightInfinitesimalCharacters.AdmissibleUnitaryThreePoint
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.FixedAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.FlagPol
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CountRankThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CsdSsOfFull
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.SsCalcP
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.IsoOfFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.WDAway
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.WDAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.JumpsAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocFixed
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.GlobFixed
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatFrob
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormEqOfSamePlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.J

open UpperTheory.V.Af UpperTheory.V.Lev

variable {K Ω : Type} [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {l : ℕ} [Fact l.Prime] {n : ℕ} {ι : Qbar l ≃+* ℂ} {r R : G K Ω →* GL (Fin n) (Qbar l)} {π : CuspSub K n}

/- English proof (translation)
Take `⟨⟨σ, hσ⟩, hi⟩` from `locCompC P K n π w`. Conclude with `satFrob P K Ω l ι n R hc w hw σ B (((satLoc P K n w σ).2 _ π.finPart (hi σ hσ) B).1 hB) fun A h rc hrc => H w hw A h rc hrc σ hσ`.
-/
private theorem frob_of_away (P : Hypotheses₂) (hc : Continuous R)
    (H : ∀ (w : HeightOneSpectrum (𝓞 K)), ((l : ℕ) : 𝓞 K) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (rc : IrrGL (w.adicCompletion K) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → IsWDOf ι R (rc (algNorm σ)))
    (w : HeightOneSpectrum (𝓞 K)) (hw : ((l : ℕ) : 𝓞 K) ∉ w.asIdeal) (B : Multiset ℂˣ) (hB : (CG.mk π).HasSat w B) :
    FrobEig ι R w (algSat n (normV w) B) := by
  obtain ⟨⟨σ, hσ⟩, hi⟩ := locCompC P K n π w
  exact satFrob P K Ω l ι n R hc w hw σ B (((satLoc P K n w σ).2 _ π.finPart (hi σ hσ) B).1 hB)
    fun A h rc hrc => H w hw A h rc hrc σ hσ

/- English proof (translation)
Use `isoOfFrob P K Ω l ι n r R hr hc ha.1 hs ((ha.2.and (eventually_not_mem K l)).mono ?_)` and prove the remaining obligations. Introduce and unpack `w ⟨⟨B, h1, h2⟩, hw⟩`. Conclude with `⟨_, h2, frob_of_away P hc H w hw B h1⟩`.
-/
private theorem iso_of_away (P : Hypotheses₂) (hr : Continuous r) (ha : AttC ι r π) (hc : Continuous R) (hs : IsSSRep R)
    (H : ∀ (w : HeightOneSpectrum (𝓞 K)), ((l : ℕ) : 𝓞 K) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (rc : IrrGL (w.adicCompletion K) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → IsWDOf ι R (rc (algNorm σ))) :
    RepIso r R := by
  refine isoOfFrob P K Ω l ι n r R hr hc ha.1 hs ((ha.2.and (eventually_not_mem K l)).mono ?_)
  rintro w ⟨⟨B, h1, h2⟩, hw⟩
  exact ⟨_, h2, frob_of_away P hc H w hw B h1⟩

/- English proof (translation)
Establish `h2` using `congrArg (Multiset.map fun z : ℂ => ((n : ℂ) - 1) / 2 - z) h`. Simplify using `only [Multiset.map_map, Function.comp_def, sub_sub_cancel, Multiset.map_id'] at h2`. Rewrite using `[← h2, infOf]`. Conclude with `Multiset.map_congr rfl fun i _ => by push_cast; ring`.
-/
private theorem infOf_of_weights {m : Fin n → ℤ} {x : Multiset ℂ}
    (h : (Finset.univ.val.map fun i => -m i).map (fun k : ℤ => (k : ℂ)) = x.map fun z => ((n : ℂ) - 1) / 2 - z) :
    x = infOf m := by
  have h2 := congrArg (Multiset.map fun z : ℂ => ((n : ℂ) - 1) / 2 - z) h
  simp only [Multiset.map_map, Function.comp_def, sub_sub_cancel, Multiset.map_id'] at h2
  rw [← h2, infOf]
  exact Multiset.map_congr rfl fun i _ => by push_cast; ring

end UpperTheory.V.Z.J

open UpperTheory.V.Af UpperTheory.V.Lev UpperTheory.V.Z.J in
/- English proof (translation)
Introduce `P K _ _ _ n hn m _ M hM l _ hl Ω _ _ _ ι r π hL hreg hd ha`. Establish `hC` using `P.ss`. Establish `hF` using `UpperTheory.V.Lev.fixedAll P`. Establish `hpol : GlobalTheory.ContraPair.PolarizedPair π (quadChar K ^ n)` using `⟨fun v => by rw [locInf_pow, quadChar_locInf], by`. Rewrite using `[map_pow, compNorm_quadChar, one_pow]`.

Conclude with `(GlobalTheory.ContraPair.dualIsConjBy_one π).2 hd⟩`. Take `⟨R₁, wt, HT, H₁⟩` from `P.litN.aut.gal K Ω l ι n (by omega) π _ hreg hpol`. Take `⟨R, hc, hs, Haw, Hab⟩` from `hC K Ω l ι n hn π hd (P.litN.aut.coh K n (by omega) π hreg)`. Establish `hiso₁` using `iso_of_away P hL.cont ha H₁.cont H₁.ss H₁.away`. Establish `L₁` using `hL.toLevel.of_iso hiso₁`.

Establish `hiso` using `iso_of_away P hL.cont ha hc hs Haw`. Establish `L` using `hL.toLevel.of_iso hiso`. Use `⟨⟨fun φ => ?_, hd, ?_⟩, fun w hw B hB => (frob_of_away P hc Haw w hw B hB).of_iso hiso.symm'⟩` and prove the remaining obligations. Set `τ : K →+* Qbar l` to `ι.symm.toRingHom.comp φ`. Establish `hφ : ι.toRingHom.comp τ = φ` using `RingHom.ext fun x => ι.apply_symm_apply _`.

Take `⟨w, hw, hτ⟩` from `GlobalTheory.GalFirstClause.existsIsInduced l K Ω τ`. Take `⟨A, hA, χ, κ, h1, h2, h3, -⟩` from `L₁.above w hw`. Take `⟨O, _, _, _, Bw, hj⟩` from `exists_bridge (l := l) hA hw`. Take `⟨τ', hτ'⟩` from `hτ A hA O Bw hj`. Establish `hJ` using `jumpsAbove P K Ω l hl n M hM m R₁ H₁.cont w A hA O Bw hj κ ⟨χ, h1, h2, h3⟩ τ _ ((H₁.above _ _ (UpperTheory.V.Loc.tiedP l) w A hA O Bw hj).jumps τ _ τ' hτ')`.

Establish `hw` using `H₁.weights τ`. Rewrite `hw` using `[hJ, hφ]`. Rewrite using `[← infOf_of_weights hw]`. Conclude with `ParLaws.hasInfChar_infChar (CG.mk π) φ`. Use `globFixed P K n M hM _ π.finPart π.isSmooth_finPart fun w => ?_` and prove the remaining obligations.

Take `⟨⟨σ, hσ⟩, hi⟩` from `locCompC P K n π w`. Use `⟨σ, hi σ hσ, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hw : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal`. Take `⟨A, hA, κ, ⟨χ, h1, h2, h3⟩, hu⟩` from `hL.unl w hw`. Take `⟨O, _, _, _, Bw, hj⟩` from `exists_bridge (l := l) hA hw`.

Take `⟨rc, hrc⟩` from `P.exists_rec hA`. Take `⟨hp, he⟩` from `Hab _ _ (UpperTheory.V.Loc.tiedP l) w A hA O Bw hj`. Conclude with `hF K Ω l ι n M hM m R hc w A hA O Bw hj κ ⟨χ, h1, h2.of_iso hiso, h3⟩ hp rc hrc σ (fun ⟨μ, hμ⟩ => he σ hσ rc hrc (Or.inl ((ssCalc K Ω A w hA).1 n _ μ hμ))) (Or.inr (Or.inl hu))`. Take `⟨A, hA, χ, h1, h2⟩` from `L.away w hw`. Take `⟨rc, hrc⟩` from `P.exists_rec hA`.

Conclude with `locFixed P K Ω n M hM w A hA rc hrc σ (wdAway P K Ω l ι n M hM R hc w hw A hA χ h1 h2 _ (Haw w hw A hA rc hrc σ hσ))`.
-/
theorem UpperTheory.V.Z.J.levelKU :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Z.J.LevelKU := by
  intro P K _ _ _ n hn m _ M hM l _ hl Ω _ _ _ ι r π hL hreg hd ha
  have hC := P.ss
  have hF := UpperTheory.V.Lev.fixedAll P
  have hpol : GlobalTheory.ContraPair.PolarizedPair π (quadChar K ^ n) :=
    ⟨fun v => by rw [locInf_pow, quadChar_locInf], by
      rw [map_pow, compNorm_quadChar, one_pow]; exact (GlobalTheory.ContraPair.dualIsConjBy_one π).2 hd⟩
  obtain ⟨R₁, wt, HT, H₁⟩ := P.litN.aut.gal K Ω l ι n (by omega) π _ hreg hpol
  obtain ⟨R, hc, hs, Haw, Hab⟩ := hC K Ω l ι n hn π hd (P.litN.aut.coh K n (by omega) π hreg)
  have hiso₁ := iso_of_away P hL.cont ha H₁.cont H₁.ss H₁.away
  have L₁ := hL.toLevel.of_iso hiso₁
  have hiso := iso_of_away P hL.cont ha hc hs Haw
  have L := hL.toLevel.of_iso hiso
  refine ⟨⟨fun φ => ?_, hd, ?_⟩, fun w hw B hB => (frob_of_away P hc Haw w hw B hB).of_iso hiso.symm'⟩
  · let τ : K →+* Qbar l := ι.symm.toRingHom.comp φ
    have hφ : ι.toRingHom.comp τ = φ := RingHom.ext fun x => ι.apply_symm_apply _
    obtain ⟨w, hw, hτ⟩ := GlobalTheory.GalFirstClause.existsIsInduced l K Ω τ
    obtain ⟨A, hA, χ, κ, h1, h2, h3, -⟩ := L₁.above w hw
    obtain ⟨O, _, _, _, Bw, hj⟩ := exists_bridge (l := l) hA hw
    obtain ⟨τ', hτ'⟩ := hτ A hA O Bw hj
    have hJ := jumpsAbove P K Ω l hl n M hM m R₁ H₁.cont w A hA O Bw hj κ ⟨χ, h1, h2, h3⟩ τ _
      ((H₁.above _ _ (UpperTheory.V.Loc.tiedP l) w A hA O Bw hj).jumps τ _ τ' hτ')
    have hw := H₁.weights τ
    rw [hJ, hφ] at hw
    rw [← infOf_of_weights hw]
    exact ParLaws.hasInfChar_infChar (CG.mk π) φ
  · refine globFixed P K n M hM _ π.finPart π.isSmooth_finPart fun w => ?_
    obtain ⟨⟨σ, hσ⟩, hi⟩ := locCompC P K n π w
    refine ⟨σ, hi σ hσ, ?_⟩
    by_cases hw : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal
    · obtain ⟨A, hA, κ, ⟨χ, h1, h2, h3⟩, hu⟩ := hL.unl w hw
      obtain ⟨O, _, _, _, Bw, hj⟩ := exists_bridge (l := l) hA hw
      obtain ⟨rc, hrc⟩ := P.exists_rec hA
      obtain ⟨hp, he⟩ := Hab _ _ (UpperTheory.V.Loc.tiedP l) w A hA O Bw hj
      exact hF K Ω l ι n M hM m R hc w A hA O Bw hj κ ⟨χ, h1, h2.of_iso hiso, h3⟩ hp rc hrc σ
        (fun ⟨μ, hμ⟩ => he σ hσ rc hrc (Or.inl ((ssCalc K Ω A w hA).1 n _ μ hμ))) (Or.inr (Or.inl hu))
    · obtain ⟨A, hA, χ, h1, h2⟩ := L.away w hw
      obtain ⟨rc, hrc⟩ := P.exists_rec hA
      exact locFixed P K Ω n M hM w A hA rc hrc σ
        (wdAway P K Ω l ι n M hM R hc w hw A hA χ h1 h2 _ (Haw w hw A hA rc hrc σ hσ))

end
