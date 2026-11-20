import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.ChainSc
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.DoubleSumFinprodFactor
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PFinConv

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2
open UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `E _ _ _ a b κ _ P _ L L' hL hL'`. Use `⟨fun X Y => ?_, FinConv.isTestFunction_mulConvolution hL.2 hL'.2⟩` and prove the remaining obligations. Establish `hoff : IsTestP (fun w => mconv (L.ent P X X w) (L'.ent P Y Y w))` using `FinConv.isTestFunction_mulConvolution (hL.1 X X) (hL'.1 Y Y)`. Use `Fm.isTestFunction_linearCombination (J := Option (Σ i : P, κ i)) (fun j => j.elim (fun w => mconv (L.ent P X X w) (L'.ent P Y Y w)) fun q w => mconv (L.ent P X (Function.update X q.1 q.2) w) (L'.ent P (Function.update X q.1 q.2) Y w)) (fun j => ?_) _ (fun w => ?_) ?_` and prove the remaining obligations. Consider the cases of `j with`.

Consider the case `none => exact hoff`. Consider the case `some q => exact FinConv.isTestFunction_mulConvolution (hL.1 _ _) (hL'.1 _ _)`. Distinguish the cases in `hw : w ∈ P`. Conclude with `⟨κ w, inferInstance, fun z => some ⟨⟨w, hw⟩, z⟩, fun _ => 1, by simp [LM.mul, LM.ent, hw]⟩`. Conclude with `⟨Unit, inferInstance, fun _ => none, fun _ => 1, by simp [LM.mul, LM.ent, hw]⟩`.

Conclude with `Fm.cof_off P hoff fun w hw => by simp [LM.mul, LM.ent, hw]`.
-/
theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.tmul_pf :
    TMul := by
  intro E _ _ _ a b κ _ P _ L L' hL hL'
  refine ⟨fun X Y => ?_, FinConv.isTestFunction_mulConvolution hL.2 hL'.2⟩
  have hoff : IsTestP (fun w => mconv (L.ent P X X w) (L'.ent P Y Y w)) :=
    FinConv.isTestFunction_mulConvolution (hL.1 X X) (hL'.1 Y Y)
  refine Fm.isTestFunction_linearCombination (J := Option (Σ i : P, κ i))
    (fun j => j.elim (fun w => mconv (L.ent P X X w) (L'.ent P Y Y w))
      fun q w => mconv (L.ent P X (Function.update X q.1 q.2) w) (L'.ent P (Function.update X q.1 q.2) Y w))
    (fun j => ?_) _ (fun w => ?_) ?_
  · cases j with
    | none => exact hoff
    | some q => exact FinConv.isTestFunction_mulConvolution (hL.1 _ _) (hL'.1 _ _)
  · by_cases hw : w ∈ P
    · exact ⟨κ w, inferInstance, fun z => some ⟨⟨w, hw⟩, z⟩, fun _ => 1, by simp [LM.mul, LM.ent, hw]⟩
    · exact ⟨Unit, inferInstance, fun _ => none, fun _ => 1, by simp [LM.mul, LM.ent, hw]⟩
  · exact Fm.cof_off P hoff fun w hw => by simp [LM.mul, LM.ent, hw]

end
