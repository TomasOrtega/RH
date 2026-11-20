import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.InePolCoeffZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocParOfCharUnrIff
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EventuallyUnr
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.MainNotions.N Formalism.L2.Host Module
open GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.CuspRep GlobalTheory.LocLanglands GlobalTheory.HeightCounting GlobalTheory.SmGL GlobalTheory.SatakeFlip GlobalTheory.LocGL
open GlobalTheory.Mem.Chr hiding HChar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.GalS
section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}
end
section
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
variable {N A}
end
/- English proof (translation)
Use `haveI := host_isCMField D.host`. Use `set χ' := (CGu.equivChar D.host.E (C.e 1 π)).1 with hχ'`. Use `set χ := (S.e1 π).1 with hχ`. Establish `hloc : ∀ v, T.e v (D.naut.locG π v) = _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar χ') (D.nd.plOm.2 v)` using `fun v => by`. Rewrite using `[C.loc, hχ', CGu.ofChar_equivChar]`.

Both sides reduce to the same expression. Establish `unr' : ∀ v, D.naut.unr (D.naut.locG π v) ↔ χ'.UnrAt v` using `fun v => by`. Rewrite using `[T.unr, hloc v]`. Conclude with `_root_.GlobalTheory.RankOneComp.locParT_ofChar_unr_iff_unrAt hL χ' _`. Establish `hchar : χ' = χ`.

Rewrite using `[← mul_inv_eq_one]`. Apply `GlobalTheory.HeckeSplitRow.eq_one_of_split D.host` to reduce the goal to its premises. Use `filter_upwards [D.naut.locG_unr_ae π] with v hv _`. Establish `u1` using `(S.unr_iff π v).1 hv`. Establish `u2` using `(unr' v).1 hv`.

Use `⟨fun x hx => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_inv, u1 x hx, u2 x hx, inv_one, mul_one]`. Establish `hf` using `S.frob π v u1`. Establish `hf' : D.naut.frobEig (D.naut.locG π v) = {(((χ'.val v)⁻¹ : ℂˣ) : ℂ)}`. Rewrite using `[T.frobEig _ _ hv, hloc v]`.

Conclude with `_root_.GlobalTheory.RankOneComp.frobEig_locParT_ofChar_of_unrAt hL χ' _ u2`. Rewrite `hf` using `[hf', Multiset.singleton_inj, Units.val_inj, inv_inj]`. Rewrite using `[Formalism.L2.Host.HChar.val_mul, Formalism.L2.Host.HChar.val_inv, hf, mul_inv_cancel]`. Rewrite using `[tm_iff T, hloc, hchar, _root_.GlobalTheory.CuspRep.ParLaws.local_parameter_of_hecke_character_eq_reciprocity]`. Apply the tactic sequence `first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w)); obtain ⟨a, ha, ε, H⟩ := hOpn) | obtain ⟨a, ha, ε, -, H⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w)`.

Rewrite using `[H.one]`. Use `GlobalTheory.SerSys.LabDepth.tame_of_isTameWD ((PositivityTheory.LocalParametersCuspidal.DZC.tame_lpOfChar_iff _ _).2 fun σ hσ => ?_)` and prove the remaining obligations. Conclude with `GlobalTheory.MuTameQS.isTame_loc ht _ ((GlobalTheory.MuTameQS.val_lt_one_iff w _).2 (PositivityTheory.LocalParametersCuspidal.DZC.wild_to_unitsOne a ha σ hσ))`.
-/
theorem tm_rankOne_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut} (C : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T)
    {C₀ : CharFrame D} (S : CharSide D C₀) (π : D.naut.CG 1) (w : PlE D.host) (ht : (S.e1 π).1.TameAt w) :
    Tm D.nd D.naut (D.naut.locG π w) := by
  haveI := host_isCMField D.host
  set χ' := (CGu.equivChar D.host.E (C.e 1 π)).1 with hχ'
  set χ := (S.e1 π).1 with hχ
  have hloc : ∀ v, T.e v (D.naut.locG π v) = _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.ofChar χ') (D.nd.plOm.2 v) := fun v => by
    rw [C.loc, hχ', CGu.ofChar_equivChar]; rfl
  have unr' : ∀ v, D.naut.unr (D.naut.locG π v) ↔ χ'.UnrAt v := fun v => by
    rw [T.unr, hloc v]; exact _root_.GlobalTheory.RankOneComp.locParT_ofChar_unr_iff_unrAt hL χ' _
  have hchar : χ' = χ := by
    rw [← mul_inv_eq_one]
    apply GlobalTheory.HeckeSplitRow.eq_one_of_split D.host
    filter_upwards [D.naut.locG_unr_ae π] with v hv _
    have u1 := (S.unr_iff π v).1 hv
    have u2 := (unr' v).1 hv
    refine ⟨fun x hx => ?_, ?_⟩
    · rw [Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_inv, u1 x hx, u2 x hx, inv_one, mul_one]
    · have hf := S.frob π v u1
      have hf' : D.naut.frobEig (D.naut.locG π v) = {(((χ'.val v)⁻¹ : ℂˣ) : ℂ)} := by
        rw [T.frobEig _ _ hv, hloc v]; exact _root_.GlobalTheory.RankOneComp.frobEig_locParT_ofChar_of_unrAt hL χ' _ u2
      rw [hf', Multiset.singleton_inj, Units.val_inj, inv_inj] at hf
      rw [Formalism.L2.Host.HChar.val_mul, Formalism.L2.Host.HChar.val_inv, hf, mul_inv_cancel]
  rw [tm_iff T, hloc, hchar, _root_.GlobalTheory.CuspRep.ParLaws.local_parameter_of_hecke_character_eq_reciprocity]
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w)); obtain ⟨a, ha, ε, H⟩ := hOpn) | obtain ⟨a, ha, ε, -, H⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w)
  rw [H.one]
  refine GlobalTheory.SerSys.LabDepth.tame_of_isTameWD ((PositivityTheory.LocalParametersCuspidal.DZC.tame_lpOfChar_iff _ _).2 fun σ hσ => ?_)
  exact GlobalTheory.MuTameQS.isTame_loc ht _ ((GlobalTheory.MuTameQS.val_lt_one_iff w _).2 (PositivityTheory.LocalParametersCuspidal.DZC.wild_to_unitsOne a ha σ hσ))
end UpperTheory.GalS
end
end
