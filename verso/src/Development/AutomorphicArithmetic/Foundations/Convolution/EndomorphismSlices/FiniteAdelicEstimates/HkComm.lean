import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.LocAlg
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.PositionTest
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.EntEmpty
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.SphComm2
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.HintTranslate

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

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

/- English proof (translation)
Unfold `intersection_update_fsHerm_neg_one`. Rewrite using `[if_neg hw]`. Use `split_ifs`. Conclude with `UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.exHecke2 E a b w (e w)`. Conclude with `UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.exHecke2 E a b w .one`.
-/
private theorem position_sph (Z T : Finset (Pl E)) (L : Lv a b Z) (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1)))
    (w : Pl E) (hw : w ∉ Z) : IsHecke (K2 a b w) (intersection_update_fsHerm_neg_one Z T L.ln e w) := by
  unfold intersection_update_fsHerm_neg_one
  rw [if_neg hw]
  split_ifs
  · exact UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.exHecke2 E a b w (e w)
  · exact UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.exHecke2 E a b w .one

/- English proof (translation)
Unfold `intersection_update_fsHerm_neg_one`. Rewrite using `[if_pos hw]`.
-/
private theorem position_Z (Z T : Finset (Pl E)) (L : Lv a b Z) (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1)))
    (w : Pl E) (hw : w ∈ Z) : intersection_update_fsHerm_neg_one Z T L.ln e w = L.ln w := by
  unfold intersection_update_fsHerm_neg_one
  rw [if_pos hw]

/- English proof (translation)
Distinguish the cases in `hw : w ∈ Z`. Rewrite using `[position_Z Z T L e w hw, position_Z Z T' L e' w hw]`. Conclude with `UpperTheory.Zero.ConvolutionTheory.EB.sphComm2 E a b w _ _ (position_sph Z T L e w hw) (position_sph Z T' L e' w hw)`.
-/
private theorem position_comm (Z T T' : Finset (Pl E)) (L : Lv a b Z) (e e' : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (w : Pl E) :
    PositivityTheory.Rg.BcN.F2.mconv (intersection_update_fsHerm_neg_one Z T L.ln e w) (intersection_update_fsHerm_neg_one Z T' L.ln e' w) =
      PositivityTheory.Rg.BcN.F2.mconv (intersection_update_fsHerm_neg_one Z T' L.ln e' w) (intersection_update_fsHerm_neg_one Z T L.ln e w) := by
  by_cases hw : w ∈ Z
  · rw [position_Z Z T L e w hw, position_Z Z T' L e' w hw]
  · exact UpperTheory.Zero.ConvolutionTheory.EB.sphComm2 E a b w _ _ (position_sph Z T L e w hw) (position_sph Z T' L e' w hw)

/- English proof (translation)
Establish `hl` using `UpperTheory.Zero.ConvolutionTheory.EB.locAlg E a b Z L w`. Distinguish the cases in `hw : w ∈ Z`. Rewrite using `[position_Z Z T L e w hw, position_Z Z T' L e' w hw, hl.2.1]`. Conclude with `UpperTheory.Zero.ConvolutionTheory.EB.sphComm2 E a b w _ _ (position_sph Z T L e w hw) ((hl.2.2.2.2 _ (position_sph Z T' L e' w hw)).2.2)`.
-/
private theorem position_comm_star (Z T T' : Finset (Pl E)) (L : Lv a b Z) (e e' : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (w : Pl E) :
    PositivityTheory.Rg.BcN.F2.mconv (intersection_update_fsHerm_neg_one Z T L.ln e w) (lfStar (intersection_update_fsHerm_neg_one Z T' L.ln e' w)) =
      PositivityTheory.Rg.BcN.F2.mconv (lfStar (intersection_update_fsHerm_neg_one Z T' L.ln e' w)) (intersection_update_fsHerm_neg_one Z T L.ln e w) := by
  have hl := UpperTheory.Zero.ConvolutionTheory.EB.locAlg E a b Z L w
  by_cases hw : w ∈ Z
  · rw [position_Z Z T L e w hw, position_Z Z T' L e' w hw, hl.2.1]
  · exact UpperTheory.Zero.ConvolutionTheory.EB.sphComm2 E a b w _ _ (position_sph Z T L e w hw)
      ((hl.2.2.2.2 _ (position_sph Z T' L e' w hw)).2.2)

/- English proof (translation)
Introduce `E _ _ _ a b l₁ l₂ D A S Z L hS hZ T T' e₁ e₂ e₁' e₂'`. Establish `hst` using `UpperTheory.Zero.ConvolutionTheory.EB.positionTest E a b S Z L hZ`. Establish `ht : ∀ (T : Finset (Pl E)) (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))), IsTestP (intersection_update_fsHerm_neg_one Z T L.ln e)` using `fun T e => (hst.2.2 L.ln hst.1).2 T e`. Establish `hf` using `(UpperTheory.Zero.ConvolutionTheory.EB.ffAlg E a b l₁ l₂ D A S hS).2`. Establish `h1` using `hf _ _ (ht T e₁) (ht T e₂)`.

Establish `h2` using `hf _ _ (ht T' e₁') (ht T' e₂')`. Establish `hstar` using `h2.2.1`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show mulF A.ν (A.ff S _ _) (A.ff S _ _) = mulF A.ν (A.ff S _ _) (A.ff S _ _)`. Rewrite using `[h1.2.2.2.2 _ _ (ht T' e₁') (ht T' e₂'), h2.2.2.2.2 _ _ (ht T e₁) (ht T e₂)]`.

Simplify using `only [position_comm Z T T' L e₁ e₁', position_comm Z T T' L e₂ e₂']`. Use `show mulF A.ν (A.ff S _ _) (adjF (A.ff S _ _)) = mulF A.ν (adjF (A.ff S _ _)) (A.ff S _ _)`. Rewrite using `[hstar]`. Establish `hs` using `hf _ _ h2.2.2.1 h2.2.2.2.1`. Rewrite using `[h1.2.2.2.2 _ _ h2.2.2.1 h2.2.2.2.1, hs.2.2.2.2 _ _ (ht T e₁) (ht T e₂)]`.

Simplify using `only [position_comm_star Z T T' L e₁ e₁', position_comm_star Z T T' L e₂ e₂']`.
-/
theorem _root_.UpperTheory.Zero.ConvolutionTheory.EB.hkComm :
    UpperTheory.Zero.ConvolutionTheory.EB.HkComm := by
  intro E _ _ _ a b l₁ l₂ D A S Z L hS hZ T T' e₁ e₂ e₁' e₂'
  have hst := UpperTheory.Zero.ConvolutionTheory.EB.positionTest E a b S Z L hZ
  have ht : ∀ (T : Finset (Pl E)) (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))), IsTestP (intersection_update_fsHerm_neg_one Z T L.ln e) :=
    fun T e => (hst.2.2 L.ln hst.1).2 T e
  have hf := (UpperTheory.Zero.ConvolutionTheory.EB.ffAlg E a b l₁ l₂ D A S hS).2
  have h1 := hf _ _ (ht T e₁) (ht T e₂)
  have h2 := hf _ _ (ht T' e₁') (ht T' e₂')
  have hstar := h2.2.1
  refine ⟨?_, ?_⟩
  · show mulF A.ν (A.ff S _ _) (A.ff S _ _) = mulF A.ν (A.ff S _ _) (A.ff S _ _)
    rw [h1.2.2.2.2 _ _ (ht T' e₁') (ht T' e₂'), h2.2.2.2.2 _ _ (ht T e₁) (ht T e₂)]
    simp only [position_comm Z T T' L e₁ e₁', position_comm Z T T' L e₂ e₂']
  · show mulF A.ν (A.ff S _ _) (adjF (A.ff S _ _)) = mulF A.ν (adjF (A.ff S _ _)) (A.ff S _ _)
    rw [hstar]
    have hs := hf _ _ h2.2.2.1 h2.2.2.2.1
    rw [h1.2.2.2.2 _ _ h2.2.2.1 h2.2.2.2.1, hs.2.2.2.2 _ _ (ht T e₁) (ht T e₂)]
    simp only [position_comm_star Z T T' L e₁ e₁', position_comm_star Z T T' L e₂ e₂']

end UpperTheory.Zero.ConvolutionTheory.EB
