import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.MonoOdd
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

namespace UpperTheory.V.Lev

open UpperTheory.V.Af

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

/- English proof (translation)
Introduce `h` and use `by obtain ⟨a, b, e⟩ : IsCoprime ((l : ℕ) : 𝓞 F) (M : 𝓞 F) := Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hM) exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (e ▸ w.asIdeal.add_mem (w.asIdeal.mul_mem_left a hw) (w.asIdeal.mul_mem_left b h)))`.
-/
private theorem not_mem_of_not_dvd {F : Type} [Field F] [NumberField F] {M : ℕ} {w : HeightOneSpectrum (𝓞 F)}
    (hw : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) (hM : ¬ l ∣ M) : (M : 𝓞 F) ∉ w.asIdeal := fun h => by
  obtain ⟨a, b, e⟩ : IsCoprime ((l : ℕ) : 𝓞 F) (M : 𝓞 F) :=
    Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hM)
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (e ▸ w.asIdeal.add_mem (w.asIdeal.mul_mem_left a hw) (w.asIdeal.mul_mem_left b h)))

/- English proof (translation)
Take `⟨a, ha, ε, -, H⟩` from `hrc`. Establish `hu : (rc (algNorm σ)).unr`. Take `⟨k, b, e⟩` from `WD.exists_rep (rc (algNorm σ))`. Rewrite `h0`, `hI`, the goal using `[← e]`. Rewrite using `[WD.unr_mk]`.

Use `⟨(WD.monodromyZero_ofWeilDeligneRepClass_iff b).1 h0, fun s => ?_⟩` and prove the remaining obligations. Establish `h1` using `LinearMap.aeval_self_charpoly (b.ρ (ineIncl h s))`. Establish `h2` using `hI s`. Rewrite `h2` using `[WD.charPol_mk]`. Rewrite `h1` using `[h2, map_pow, map_sub, aeval_X, map_one]`.

Establish `hs : Module.End.IsSemisimple (b.ρ (ineIncl h s) - algebraMap ℂ (Module.End ℂ (Fin k → ℂ)) 1)` using `Module.End.isSemisimple_sub_algebraMap_iff.2 (b.semisimple _)`. Rewrite `hs` using `[map_one]`. Conclude with `sub_eq_zero.1 (Module.End.eq_zero_of_isNilpotent_isSemisimple ⟨_, h1⟩ hs)`. Take `⟨v, hv0, hv⟩` from `UpperTheory.hasFixed_of_algNorm_fixed_ne_bot F w n σ _ le_rfl ((H.sph _).2 hu)`. Conclude with `(Submodule.ne_bot_iff _).2 ⟨v, fun g => by simpa using hv g.1 g.2, hv0⟩`.
-/
private theorem sph_of {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {n : ℕ}
    {w : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω} {h : IsPlaceOver A w}
    {rc : IrrGL (w.adicCompletion F) → WD h} (hrc : IsRec h rc) (σ : SmIrr (GL (Fin n) (w.adicCompletion F)))
    (h0 : (rc (algNorm σ)).mono0) (d : ℕ)
    (hI : ∀ s : ↥(Ine (F := F) A), (rc (algNorm σ)).charPol (ineIncl h s) = (X - 1) ^ d) : GlobalTheory.SmGL.IsSpherical σ.ρ := by
  obtain ⟨a, ha, ε, -, H⟩ := hrc
  have hu : (rc (algNorm σ)).unr := by
    obtain ⟨k, b, e⟩ := WD.exists_rep (rc (algNorm σ))
    rw [← e] at h0 hI ⊢
    rw [WD.unr_mk]
    refine ⟨(WD.monodromyZero_ofWeilDeligneRepClass_iff b).1 h0, fun s => ?_⟩
    have h1 := LinearMap.aeval_self_charpoly (b.ρ (ineIncl h s))
    have h2 := hI s
    rw [WD.charPol_mk] at h2
    rw [h2, map_pow, map_sub, aeval_X, map_one] at h1
    have hs : Module.End.IsSemisimple (b.ρ (ineIncl h s) - algebraMap ℂ (Module.End ℂ (Fin k → ℂ)) 1) :=
      Module.End.isSemisimple_sub_algebraMap_iff.2 (b.semisimple _)
    rw [map_one] at hs
    exact sub_eq_zero.1 (Module.End.eq_zero_of_isNilpotent_isSemisimple ⟨_, h1⟩ hs)
  obtain ⟨v, hv0, hv⟩ := UpperTheory.hasFixed_of_algNorm_fixed_ne_bot F w n σ _ le_rfl ((H.sph _).2 hu)
  exact (Submodule.ne_bot_iff _).2 ⟨v, fun g => by simpa using hv g.1 g.2, hv0⟩

def LevelKO : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ), 2 ≤ n → ∀ (m : Fin n → ℤ), StrictAnti m → ∀ M : ℕ, 1 ≤ M →
    ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ)
      (r : G K Ω →* GL (Fin n) (Qbar l)) (π : CuspSub K n), Level l M m r → Odd n → (CG.mk π).IsRegAlg →
      GlobalTheory.ContraPair.DualIsConj π → AttC ι r π →
      π ∈ SigK K m M ∧ ∀ w : HeightOneSpectrum (𝓞 K), (l : 𝓞 K) ∉ w.asIdeal → ∀ B, (CG.mk π).HasSat w B →
        FrobEig ι r w (algSat n (normV w) B)

end UpperTheory.V.Lev

open UpperTheory.V.Af UpperTheory.V.Lev in
/- English proof (translation)
Introduce `P hC hO hF K _ _ _ n hn m _ M hM l _ hl Ω _ _ _ ι r π hL hodd hreg hd ha`. Establish `hpol : GlobalTheory.ContraPair.PolarizedPair π (quadChar K ^ n)` using `⟨fun v => by rw [locInf_pow, quadChar_locInf], by`. Rewrite using `[map_pow, compNorm_quadChar, one_pow]`. Conclude with `(GlobalTheory.ContraPair.dualIsConjBy_one π).2 hd⟩`. Take `⟨R₁, wt, HT, H₁⟩` from `P.litN.aut.gal K Ω l ι n (by omega) π _ hreg hpol`.

Take `⟨R, hc, hs, Haw, Hab⟩` from `hC K Ω l ι n hn π hd (P.litN.aut.coh K n (by omega) π hreg)`. Establish `hiso₁` using `iso_of_away P hL.cont ha H₁.cont H₁.ss H₁.away`. Establish `L₁` using `hL.of_iso hiso₁`. Establish `hiso` using `iso_of_away P hL.cont ha hc hs Haw`. Establish `L` using `hL.of_iso hiso`.

Use `⟨⟨fun φ => ?_, hd, ?_⟩, fun w hw B hB => (frob_of_away P hc Haw w hw B hB).of_iso hiso.symm'⟩` and prove the remaining obligations. Set `τ : K →+* Qbar l` to `ι.symm.toRingHom.comp φ`. Establish `hφ : ι.toRingHom.comp τ = φ` using `RingHom.ext fun x => ι.apply_symm_apply _`. Take `⟨w, hw, hτ⟩` from `GlobalTheory.GalFirstClause.existsIsInduced l K Ω τ`. Take `⟨A, hA, χ, κ, h1, h2, h3, -⟩` from `L₁.above w hw`.

Take `⟨O, _, _, _, Bw, hj⟩` from `exists_bridge (l := l) hA hw`. Take `⟨τ', hτ'⟩` from `hτ A hA O Bw hj`. Establish `hJ` using `jumpsAbove P K Ω l hl n M hM m R₁ H₁.cont w A hA O Bw hj κ ⟨χ, h1, h2, h3⟩ τ _ ((H₁.above _ _ (UpperTheory.V.Loc.tiedP l) w A hA O Bw hj).jumps τ _ τ' hτ')`. Establish `hw` using `H₁.weights τ`. Rewrite `hw` using `[hJ, hφ]`.

Rewrite using `[← infOf_of_weights hw]`. Conclude with `ParLaws.hasInfChar_infChar (CG.mk π) φ`. Use `globFixed P K n M hM _ π.finPart π.isSmooth_finPart fun w => ?_` and prove the remaining obligations. Take `⟨⟨σ, hσ⟩, hi⟩` from `locCompC P K n π w`. Use `⟨σ, hi σ hσ, ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hw : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal`. Take `⟨A, hA, χ, κ, h1, h2, h3, h4⟩` from `hL.above w hw`. Take `⟨O, _, _, _, Bw, hj⟩` from `exists_bridge (l := l) hA hw`. Take `⟨rc, hrc⟩` from `P.exists_rec hA`. Take `⟨hp, he⟩` from `Hab _ _ (UpperTheory.V.Loc.tiedP l) w A hA O Bw hj`.

Establish `hS` using `fun hor => hF K Ω l ι n M hM m R hc w A hA O Bw hj κ ⟨χ, h1, h2.of_iso hiso, h3⟩ hp rc hrc σ (fun ⟨μ, hμ⟩ => he σ hσ rc hrc (Or.inl ((ssCalc K Ω A w hA).1 n _ μ hμ))) hor`. Break down `h4 with h4 | h4` into its components or cases. Conclude with `hS (Or.inr (Or.inl h4))`. Distinguish the cases in `hlM : l ∣ M`. Conclude with `hS (Or.inl hlM)`.

Use `hS (Or.inr (Or.inr fun _ => ?_))` and prove the remaining obligations. Take `⟨μ, m1, m2, -⟩` from `flagPol K Ω l ι n M hM m R hc w A hA O Bw hj κ ⟨χ, h1, h2.of_iso hiso, h3⟩ hp`. Establish `e` using `he σ hσ rc hrc (Or.inl ((ssCalc K Ω A w hA).1 n _ μ m1))`. Use `sph_of hrc σ (hO K n hodd l Ω ι r π hL.cont hreg hd ha w A hA h4 σ hσ rc hrc) n fun s => ?_` and prove the remaining obligations. Rewrite using `[← e, m1]`.

Simplify using `[fun i => m2 i s (UpperTheory.inertia_fixes_roots_of_unity_prime_to_residue_char K Ω w A hA M (not_mem_of_not_dvd hw hlM) s s.2)]`. Take `⟨A, hA, χ, h1, h2⟩` from `L.away w hw`. Take `⟨rc, hrc⟩` from `P.exists_rec hA`. Conclude with `locFixed P K Ω n M hM w A hA rc hrc σ (wdAway P K Ω l ι n M hM R hc w hw A hA χ h1 h2 _ (Haw w hw A hA rc hrc σ hσ))`.
-/
theorem UpperTheory.V.Lev.levelKO :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Lev.CsdSs → UpperTheory.V.Lev.MonoOdd → UpperTheory.V.Lev.FixedSs → UpperTheory.V.Lev.LevelKO := by
  intro P hC hO hF K _ _ _ n hn m _ M hM l _ hl Ω _ _ _ ι r π hL hodd hreg hd ha
  have hpol : GlobalTheory.ContraPair.PolarizedPair π (quadChar K ^ n) :=
    ⟨fun v => by rw [locInf_pow, quadChar_locInf], by
      rw [map_pow, compNorm_quadChar, one_pow]; exact (GlobalTheory.ContraPair.dualIsConjBy_one π).2 hd⟩
  obtain ⟨R₁, wt, HT, H₁⟩ := P.litN.aut.gal K Ω l ι n (by omega) π _ hreg hpol
  obtain ⟨R, hc, hs, Haw, Hab⟩ := hC K Ω l ι n hn π hd (P.litN.aut.coh K n (by omega) π hreg)
  have hiso₁ := iso_of_away P hL.cont ha H₁.cont H₁.ss H₁.away
  have L₁ := hL.of_iso hiso₁
  have hiso := iso_of_away P hL.cont ha hc hs Haw
  have L := hL.of_iso hiso
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
    · obtain ⟨A, hA, χ, κ, h1, h2, h3, h4⟩ := hL.above w hw
      obtain ⟨O, _, _, _, Bw, hj⟩ := exists_bridge (l := l) hA hw
      obtain ⟨rc, hrc⟩ := P.exists_rec hA
      obtain ⟨hp, he⟩ := Hab _ _ (UpperTheory.V.Loc.tiedP l) w A hA O Bw hj
      have hS := fun hor => hF K Ω l ι n M hM m R hc w A hA O Bw hj κ ⟨χ, h1, h2.of_iso hiso, h3⟩ hp rc hrc σ
        (fun ⟨μ, hμ⟩ => he σ hσ rc hrc (Or.inl ((ssCalc K Ω A w hA).1 n _ μ hμ))) hor
      rcases h4 with h4 | h4
      · exact hS (Or.inr (Or.inl h4))
      · by_cases hlM : l ∣ M
        · exact hS (Or.inl hlM)
        refine hS (Or.inr (Or.inr fun _ => ?_))
        obtain ⟨μ, m1, m2, -⟩ := flagPol K Ω l ι n M hM m R hc w A hA O Bw hj κ ⟨χ, h1, h2.of_iso hiso, h3⟩ hp
        have e := he σ hσ rc hrc (Or.inl ((ssCalc K Ω A w hA).1 n _ μ m1))
        refine sph_of hrc σ (hO K n hodd l Ω ι r π hL.cont hreg hd ha w A hA h4 σ hσ rc hrc) n fun s => ?_
        rw [← e, m1]
        simp [fun i => m2 i s (UpperTheory.inertia_fixes_roots_of_unity_prime_to_residue_char K Ω w A hA M (not_mem_of_not_dvd hw hlM) s s.2)]
    · obtain ⟨A, hA, χ, h1, h2⟩ := L.away w hw
      obtain ⟨rc, hrc⟩ := P.exists_rec hA
      exact locFixed P K Ω n M hM w A hA rc hrc σ
        (wdAway P K Ω l ι n M hM R hc w hw A hA χ h1 h2 _ (Haw w hw A hA rc hrc σ hσ))

end
