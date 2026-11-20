import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.LocAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.HintTranslate
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.ImportsAlt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PLocOk

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

/- English proof (translation)
Use `⟨fun w => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hw : w ∈ Z`. Use `⟨ho w, hle w, fun k hk => ?_⟩` and prove the remaining obligations. Establish `h : GlobalTheory.BCT.thL n w = MonoidHom.id _`. Unfold `GlobalTheory.BCT.thL`.

Rewrite using `[if_pos (hZ w hw)]`. Rewrite using `[h]`. Conclude with `hk`. Rewrite using `[hoff w hw]`. Conclude with `PositivityTheory.Rg.BcB.F.LocOk.lev_K n w`.

Use `filter_upwards [Z.finite_toSet.compl_mem_cofinite] with w hw`. Conclude with `hoff w hw`.
-/
private theorem levelFam_of {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (Z : Finset (Pl E))
    (K : ∀ w : Pl E, Subgroup (GLw n w)) (hZ : ∀ w ∈ Z, IsSplitAt w) (ho : ∀ w, IsOpen (K w : Set (GLw n w)))
    (hle : ∀ w, K w ≤ GlobalTheory.LFun.KGL w n) (hoff : ∀ w ∉ Z, K w = GlobalTheory.LFun.KGL w n) :
    IsLevelFam (GlobalTheory.BCT.thL n) (fun w : Pl E => GlobalTheory.LFun.KGL w n) K := by
  refine ⟨fun w => ?_, ?_⟩
  · by_cases hw : w ∈ Z
    · refine ⟨ho w, hle w, fun k hk => ?_⟩
      have h : GlobalTheory.BCT.thL n w = MonoidHom.id _ := by
        unfold GlobalTheory.BCT.thL
        rw [if_pos (hZ w hw)]
      rw [h]
      exact hk
    · rw [hoff w hw]
      exact PositivityTheory.Rg.BcB.F.LocOk.lev_K n w
  · filter_upwards [Z.finite_toSet.compl_mem_cofinite] with w hw
    exact hoff w hw

/- English proof (translation)
Introduce `E _ _ _ a b S Z L hS`. Establish `hZ : ∀ w ∈ Z, IsSplitAt w` using `fun w hw => (hS w hw).2`. Establish `h₁` using `levelFam_of Z L.L₁ hZ L.open₁ L.le₁ fun w hw => (L.off w hw).1`. Establish `h₂` using `levelFam_of Z L.L₂ hZ L.open₂ L.le₂ fun w hw => (L.off w hw).2`. Establish `hH : ∀ w, IsHecke ((L.L₁ w).prod (L.L₂ w)) (L.ln w)` using `fun w => (locAlg E a b Z L w).1`.

Establish `hI : ∀ w ∉ Z, L.ln w = (K2 a b w : Set _).indicator 1` using `fun w hw => (locAlg E a b Z L w).2.2.1 hw`. Establish `hK : ∀ w ∉ Z, (L.L₁ w).prod (L.L₂ w) = K2 a b w`. Introduce `w hw`. Rewrite using `[(L.off w hw).1, (L.off w hw).2]`. Use `⟨fun w _ => hH w, ⟨L.L₁, L.L₂, h₁, h₂, hH, ?_⟩, fun φ hφ => ⟨fun w hw => ?_, fun T e => ⟨L.L₁, L.L₂, h₁, h₂, fun w => ?_, ?_⟩⟩⟩` and prove the remaining obligations.

Use `filter_upwards [Z.finite_toSet.compl_mem_cofinite] with w hw`. Conclude with `hI w hw`. Establish `h` using `PositivityTheory.Rg.BcB.F.LocOk.prod_open_le (h₁.1 w) (h₂.1 w)`. Conclude with `⟨_, h.1, h.2, hφ w hw⟩`. Distinguish the cases in `hw : w ∈ Z`.

Establish `h : intersection_update_fsHerm_neg_one Z T φ e w = φ w` using `if_pos hw`. Rewrite using `[h]`. Conclude with `hφ w hw`. Distinguish the cases in `hT : w ∈ T`. Establish `h : intersection_update_fsHerm_neg_one Z T φ e w = fn2 a b w (e w)`.

Unfold `intersection_update_fsHerm_neg_one`. Rewrite using `[if_neg hw, if_pos hT]`. Rewrite using `[h]`. Use `show GlobalTheory.BCT.IsHecke ((L.L₁ w).prod (L.L₂ w)) _`. Rewrite using `[hK w hw]`.

Conclude with `UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.exHecke2 E a b w (e w)`. Establish `h : intersection_update_fsHerm_neg_one Z T φ e w = L.ln w`. Unfold `intersection_update_fsHerm_neg_one`. Rewrite using `[if_neg hw, if_neg hT, hI w hw]`. Rewrite using `[h]`.

Conclude with `hH w`. Use `filter_upwards [(Z ∪ T).finite_toSet.compl_mem_cofinite] with w hw`. Establish `hw' : w ∉ Z ∧ w ∉ T` using `by simpa using hw`. Unfold `intersection_update_fsHerm_neg_one`. Rewrite using `[if_neg hw'.1, if_neg hw'.2]`.
-/
theorem positionTest : PositionTest := by
  intro E _ _ _ a b S Z L hS
  have hZ : ∀ w ∈ Z, IsSplitAt w := fun w hw => (hS w hw).2
  have h₁ := levelFam_of Z L.L₁ hZ L.open₁ L.le₁ fun w hw => (L.off w hw).1
  have h₂ := levelFam_of Z L.L₂ hZ L.open₂ L.le₂ fun w hw => (L.off w hw).2
  have hH : ∀ w, IsHecke ((L.L₁ w).prod (L.L₂ w)) (L.ln w) := fun w => (locAlg E a b Z L w).1
  have hI : ∀ w ∉ Z, L.ln w = (K2 a b w : Set _).indicator 1 := fun w hw => (locAlg E a b Z L w).2.2.1 hw
  have hK : ∀ w ∉ Z, (L.L₁ w).prod (L.L₂ w) = K2 a b w := by
    intro w hw
    rw [(L.off w hw).1, (L.off w hw).2]
  refine ⟨fun w _ => hH w, ⟨L.L₁, L.L₂, h₁, h₂, hH, ?_⟩, fun φ hφ => ⟨fun w hw => ?_, fun T e =>
    ⟨L.L₁, L.L₂, h₁, h₂, fun w => ?_, ?_⟩⟩⟩
  · filter_upwards [Z.finite_toSet.compl_mem_cofinite] with w hw
    exact hI w hw
  · have h := PositivityTheory.Rg.BcB.F.LocOk.prod_open_le (h₁.1 w) (h₂.1 w)
    exact ⟨_, h.1, h.2, hφ w hw⟩
  · by_cases hw : w ∈ Z
    · have h : intersection_update_fsHerm_neg_one Z T φ e w = φ w := if_pos hw
      rw [h]
      exact hφ w hw
    · by_cases hT : w ∈ T
      · have h : intersection_update_fsHerm_neg_one Z T φ e w = fn2 a b w (e w) := by
          unfold intersection_update_fsHerm_neg_one
          rw [if_neg hw, if_pos hT]
        rw [h]
        show GlobalTheory.BCT.IsHecke ((L.L₁ w).prod (L.L₂ w)) _
        rw [hK w hw]
        exact UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.exHecke2 E a b w (e w)
      · have h : intersection_update_fsHerm_neg_one Z T φ e w = L.ln w := by
          unfold intersection_update_fsHerm_neg_one
          rw [if_neg hw, if_neg hT, hI w hw]
        rw [h]
        exact hH w
  · filter_upwards [(Z ∪ T).finite_toSet.compl_mem_cofinite] with w hw
    have hw' : w ∉ Z ∧ w ∉ T := by simpa using hw
    unfold intersection_update_fsHerm_neg_one
    rw [if_neg hw'.1, if_neg hw'.2]

end UpperTheory.Zero.ConvolutionTheory.EB
