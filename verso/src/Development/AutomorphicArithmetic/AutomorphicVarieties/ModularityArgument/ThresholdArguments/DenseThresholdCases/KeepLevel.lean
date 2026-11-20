import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.OddAOfUnl
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLocCompC
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WinConv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DualOfWeights
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TJumpsAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TGlobFixed
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevFixed
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocFixed
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TWDAway
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSatFrobT
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSatLoc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.GaloisRepExistsTotallyRealGL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.ExtraV
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExistsRec

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open private infOf_of_weights not_mem_of_not_dvd from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.LevelKO
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Lev UpperTheory.V.Z.Win
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Keep
/- English proof (translation)
Take `⟨HT, hwt, hC⟩` from `compatT (_root_.UpperTheory.Gal.SV.rowOf' P.litN.aut.gal) K Ω l ι n (by omega) r π hL.cont hreg hpol ha`. Establish `hw' : ∀ w : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∉ w.asIdeal ∨ Unl1 r w ∨ PotUnl r w` using `fun w => (em _).elim (fun e => Or.inr (hU w e)) Or.inl`. Use `⟨fun φ => ?_, ?_, fun w hw B hB => ?_⟩` and prove the remaining obligations. Set `τ : K →+* Qbar l` to `ι.symm.toRingHom.comp φ`. Establish `hφ : ι.toRingHom.comp τ = φ` using `RingHom.ext fun x => ι.apply_symm_apply _`.

Take `⟨w, hw, hτ⟩` from `GlobalTheory.GalFirstClause.existsIsInduced l K Ω τ`. Take `⟨A, hA, κ, hκ⟩` from `hL.above w hw`. Take `⟨O, _, _, _, Bw, hj⟩` from `exists_bridge (l := l) hA hw`. Take `⟨τ', hτ'⟩` from `hτ A hA O Bw hj`. Take `⟨⟨σ, hσ⟩, -⟩` from `_root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P K n π w`.

Take `⟨rc, hrc⟩` from `P.exists_reciprocity_dense hA`. Establish `g` using `guard_of plainRec hreg ha hW (hw' w) (_root_.UpperTheory.V.Z.Desc.W.isRecT_of_isRecT P hrc) hσ`. Establish `hJ` using `_root_.UpperTheory.V.Af.jumps_above_of_printed_results P K Ω l hl n M hM m r hL.cont w A hA O Bw hj κ hκ τ _ (((hC w σ hσ).2 g.1 A hA O Bw hj).2 τ _ τ' hτ')`. Establish `hw` using `hwt τ`. Rewrite `hw` using `[hJ, hφ]`.

Rewrite using `[← infOf_of_weights hw]`. Conclude with `ParLaws.hasInfChar_infChar (CG.mk π) φ`. Use `_root_.UpperTheory.V.Af.globFixed_alt P K n M hM _ π.finPart π.isSmooth_finPart fun w => ?_` and prove the remaining obligations. Take `⟨⟨σ, hσ⟩, hi⟩` from `_root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P K n π w`. Use `⟨σ, hi σ hσ, ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hw : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal`. Take `⟨A, hA, κ, hκ⟩` from `hL.above w hw`. Take `⟨O, _, _, _, Bw, hj⟩` from `exists_bridge (l := l) hA hw`. Take `⟨rc, hrc⟩` from `P.exists_reciprocity_dense hA`. Establish `g` using `guard_of plainRec hreg ha hW (hw' w) (_root_.UpperTheory.V.Z.Desc.W.isRecT_of_isRecT P hrc) hσ`.

Take `⟨hp, he⟩` from `((hC w σ hσ).1 A hA rc (_root_.UpperTheory.V.Z.Desc.W.isRecT_of_isRecT P hrc)).2 O Bw hj g.2`. Use `_root_.UpperTheory.V.Lev.fixedSs_of_prints P K Ω l ι n M hM m r hL.cont w A hA O Bw hj κ hκ hp rc hrc σ (fun _ s => by rw [he]) ?_` and prove the remaining obligations. Distinguish the cases in `hlM : l ∣ M`. Conclude with `Or.inl hlM`. Use `Or.inr (Or.inr fun _ => ?_)` and prove the remaining obligations.

Take `⟨μ, m1, m2, -⟩` from `flagPol K Ω l ι n M hM m r hL.cont w A hA O Bw hj κ hκ hp`. Use `sphV (_root_.UpperTheory.V.Z.Win.toV' hrc) σ g.2.2 n fun s => ?_` and prove the remaining obligations. Rewrite using `[← he, m1]`. Simplify using `only [fun i => m2 i s (UpperTheory.inertia_fixes_roots_of_unity_prime_to_residue_char K Ω w A hA M (not_mem_of_not_dvd hw hlM) s s.2), Units.val_one, C_1, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Take `⟨A, hA, χ, h1, h2⟩` from `hL.away w hw`.

Take `⟨rc, hrc⟩` from `P.exists_reciprocity_dense hA`. Establish `g` using `guard_of plainRec hreg ha hW (hw' w) (_root_.UpperTheory.V.Z.Desc.W.isRecT_of_isRecT P hrc) hσ`. Conclude with `_root_.UpperTheory.V.Z.Win.T2.local_fixed_vectors_statement P K Ω n M hM w A hA rc hrc σ (_root_.UpperTheory.V.Af.weil_deligne_away_of_printed_results P K Ω l ι n M hM r hL.cont w hw A hA χ h1 h2 _ ((((hC w σ hσ).1 A hA rc (_root_.UpperTheory.V.Z.Desc.W.isRecT_of_isRecT P hrc)).1 …`. Take `⟨⟨σ, hσ⟩, hi⟩` from `_root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P K n π w`. Conclude with `_root_.UpperTheory.V.Z.Desc.W.satFrobT_alt P K Ω l ι n r hL.cont w hw σ B (((_root_.UpperTheory.V.Af.satake_local_of_printed_results P K n w σ).2 _ π.finPart (hi σ hσ) B).1 hB) fun A h rc hrc => ((hC w σ hσ).1 A h rc hrc).1 hw`.
-/
theorem levelCore_alt (P : _root_.UpperTheory.V.Af.Hypotheses') (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ) (hn : 2 ≤ n) (m : Fin n → ℤ)
    (M : ℕ) (hM : 1 ≤ M) (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ)
    (r : G K Ω →* GL (Fin n) (Qbar l)) (π : CuspSub K n) (hL : LevelF l M m r)
    (hU : ∀ w : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∈ w.asIdeal → Unl1 r w ∨ PotUnl r w) (hW : WitA ι r)
    (hreg : (CG.mk π).IsRegAlg) (hpol : ∃ χ, GlobalTheory.ContraPair.PolarizedPair π χ) (ha : AttC ι r π) :
    (∀ τ, π.HasInfChar τ (infOf m)) ∧ HasFixed π.finPart (KLev K n M) ∧
      ∀ w : HeightOneSpectrum (𝓞 K), (l : 𝓞 K) ∉ w.asIdeal → ∀ B, (CG.mk π).HasSat w B → FrobEig ι r w (algSat n (normV w) B) := by
  obtain ⟨HT, hwt, hC⟩ := compatT (_root_.UpperTheory.Gal.SV.rowOf' P.litN.aut.gal) K Ω l ι n (by omega) r π hL.cont hreg hpol ha
  have hw' : ∀ w : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∉ w.asIdeal ∨ Unl1 r w ∨ PotUnl r w := fun w =>
    (em _).elim (fun e => Or.inr (hU w e)) Or.inl
  refine ⟨fun φ => ?_, ?_, fun w hw B hB => ?_⟩
  · let τ : K →+* Qbar l := ι.symm.toRingHom.comp φ
    have hφ : ι.toRingHom.comp τ = φ := RingHom.ext fun x => ι.apply_symm_apply _
    obtain ⟨w, hw, hτ⟩ := GlobalTheory.GalFirstClause.existsIsInduced l K Ω τ
    obtain ⟨A, hA, κ, hκ⟩ := hL.above w hw
    obtain ⟨O, _, _, _, Bw, hj⟩ := exists_bridge (l := l) hA hw
    obtain ⟨τ', hτ'⟩ := hτ A hA O Bw hj
    obtain ⟨⟨σ, hσ⟩, -⟩ := _root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P K n π w
    obtain ⟨rc, hrc⟩ := P.exists_reciprocity_dense hA
    have g := guard_of plainRec hreg ha hW (hw' w) (_root_.UpperTheory.V.Z.Desc.W.isRecT_of_isRecT P hrc) hσ
    have hJ := _root_.UpperTheory.V.Af.jumps_above_of_printed_results P K Ω l hl n M hM m r hL.cont w A hA O Bw hj κ hκ τ _
      (((hC w σ hσ).2 g.1 A hA O Bw hj).2 τ _ τ' hτ')
    have hw := hwt τ
    rw [hJ, hφ] at hw
    rw [← infOf_of_weights hw]
    exact ParLaws.hasInfChar_infChar (CG.mk π) φ
  · refine _root_.UpperTheory.V.Af.globFixed_alt P K n M hM _ π.finPart π.isSmooth_finPart fun w => ?_
    obtain ⟨⟨σ, hσ⟩, hi⟩ := _root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P K n π w
    refine ⟨σ, hi σ hσ, ?_⟩
    by_cases hw : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal
    · obtain ⟨A, hA, κ, hκ⟩ := hL.above w hw
      obtain ⟨O, _, _, _, Bw, hj⟩ := exists_bridge (l := l) hA hw
      obtain ⟨rc, hrc⟩ := P.exists_reciprocity_dense hA
      have g := guard_of plainRec hreg ha hW (hw' w) (_root_.UpperTheory.V.Z.Desc.W.isRecT_of_isRecT P hrc) hσ
      obtain ⟨hp, he⟩ := ((hC w σ hσ).1 A hA rc (_root_.UpperTheory.V.Z.Desc.W.isRecT_of_isRecT P hrc)).2 O Bw hj g.2
      refine _root_.UpperTheory.V.Lev.fixedSs_of_prints P K Ω l ι n M hM m r hL.cont w A hA O Bw hj κ hκ hp rc hrc σ (fun _ s => by rw [he]) ?_
      by_cases hlM : l ∣ M
      · exact Or.inl hlM
      refine Or.inr (Or.inr fun _ => ?_)
      obtain ⟨μ, m1, m2, -⟩ := flagPol K Ω l ι n M hM m r hL.cont w A hA O Bw hj κ hκ hp
      refine sphV (_root_.UpperTheory.V.Z.Win.toV' hrc) σ g.2.2 n fun s => ?_
      rw [← he, m1]
      simp only [fun i => m2 i s (UpperTheory.inertia_fixes_roots_of_unity_prime_to_residue_char K Ω w A hA M (not_mem_of_not_dvd hw hlM) s s.2), Units.val_one, C_1,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    · obtain ⟨A, hA, χ, h1, h2⟩ := hL.away w hw
      obtain ⟨rc, hrc⟩ := P.exists_reciprocity_dense hA
      have g := guard_of plainRec hreg ha hW (hw' w) (_root_.UpperTheory.V.Z.Desc.W.isRecT_of_isRecT P hrc) hσ
      exact _root_.UpperTheory.V.Z.Win.T2.local_fixed_vectors_statement P K Ω n M hM w A hA rc hrc σ
        (_root_.UpperTheory.V.Af.weil_deligne_away_of_printed_results P K Ω l ι n M hM r hL.cont w hw A hA χ h1 h2 _
          ((((hC w σ hσ).1 A hA rc (_root_.UpperTheory.V.Z.Desc.W.isRecT_of_isRecT P hrc)).1 hw).isWDOf g.2))
  · obtain ⟨⟨σ, hσ⟩, hi⟩ := _root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P K n π w
    exact _root_.UpperTheory.V.Z.Desc.W.satFrobT_alt P K Ω l ι n r hL.cont w hw σ B (((_root_.UpperTheory.V.Af.satake_local_of_printed_results P K n w σ).2 _ π.finPart (hi σ hσ) B).1 hB)
      fun A h rc hrc => ((hC w σ hσ).1 A h rc hrc).1 hw
/- English proof (translation)
Introduce `K _ _ _ _ n hn m _ M hM l _ hl Ω _ _ _ ι r π hL hs hW hreg hpol ha`. Establish `h` using `_root_.UpperTheory.V.Keep.levelCore_alt P K n hn m M hM l hl Ω ι r π hL (fun w hw => hs.elim (fun a => Or.inr (a.2 w hw)) fun hg => by`. Take `⟨A, hA, κ, hκ⟩` from `hL.above w hw`. Establish `hu` using `unlGap K Ω l n M hM m r w hw A hA κ hκ hg`. Take `⟨χ, -, h2, -⟩` from `hκ`.

Conclude with `Or.inl (A4.unlOfOne K Ω l n r w A hA κ h2 hu)) hW hreg hpol ha`. Conclude with `⟨⟨h.1, hpol, h.2.1⟩, h.2.2⟩`.
-/
theorem levelPA_alt (P : _root_.UpperTheory.V.Af.Hypotheses') : LevelPA := by
  intro K _ _ _ _ n hn m _ M hM l _ hl Ω _ _ _ ι r π hL hs hW hreg hpol ha
  have h := _root_.UpperTheory.V.Keep.levelCore_alt P K n hn m M hM l hl Ω ι r π hL (fun w hw => hs.elim (fun a => Or.inr (a.2 w hw)) fun hg => by
    obtain ⟨A, hA, κ, hκ⟩ := hL.above w hw
    have hu := unlGap K Ω l n M hM m r w hw A hA κ hκ hg
    obtain ⟨χ, -, h2, -⟩ := hκ
    exact Or.inl (A4.unlOfOne K Ω l n r w A hA κ h2 hu)) hW hreg hpol ha
  exact ⟨⟨h.1, hpol, h.2.1⟩, h.2.2⟩
section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {n : ℕ}
variable [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {r : G F Ω →* GL (Fin n) (Qbar l)}
end
/- English proof (translation)
Introduce `K _ _ _ n hn m _ M hM l _ hl Ω _ _ _ ι r π hL hU hW hreg hd ha`. Establish `hpol : GlobalTheory.ContraPair.PolarizedPair π (quadChar K ^ n)` using `⟨fun v => by rw [locInf_pow, quadChar_locInf], by`. Rewrite using `[map_pow, compNorm_quadChar, one_pow]`. Conclude with `(GlobalTheory.ContraPair.dualIsConjBy_one π).2 hd⟩`. Establish `h` using `_root_.UpperTheory.V.Keep.levelCore_alt P K n hn m M hM l hl Ω ι r π (LevelF.of_level hL) hU hW hreg ⟨_, hpol⟩ ha`.

Conclude with `⟨⟨h.1, hd, h.2.1⟩, h.2.2⟩`.
-/
theorem levelKA_alt (P : _root_.UpperTheory.V.Af.Hypotheses') : LevelKA := by
  intro K _ _ _ n hn m _ M hM l _ hl Ω _ _ _ ι r π hL hU hW hreg hd ha
  have hpol : GlobalTheory.ContraPair.PolarizedPair π (quadChar K ^ n) :=
    ⟨fun v => by rw [locInf_pow, quadChar_locInf], by
      rw [map_pow, compNorm_quadChar, one_pow]; exact (GlobalTheory.ContraPair.dualIsConjBy_one π).2 hd⟩
  have h := _root_.UpperTheory.V.Keep.levelCore_alt P K n hn m M hM l hl Ω ι r π (LevelF.of_level hL) hU hW hreg ⟨_, hpol⟩ ha
  exact ⟨⟨h.1, hd, h.2.1⟩, h.2.2⟩
end UpperTheory.V.Keep
end
end
