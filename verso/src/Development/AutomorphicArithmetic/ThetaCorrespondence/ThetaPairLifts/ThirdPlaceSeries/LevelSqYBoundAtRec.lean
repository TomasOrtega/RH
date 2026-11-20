import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeafLevelSquareBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BigOn
/- English proof (translation)
Use `⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ⟨0, fun c _ _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun x hx i p _ _ r O hO => ?_⟩⟩⟩` and prove the remaining obligations. Take `⟨st, td⟩` from `hO.1.depth`. Use `letI := hostAlg (Fm.D x i)`. Establish `g1 : O.g1 = (Fm.D x i).host.g 0` using `td.jets_eq_fact`. Establish `g2 : O.g2 = (Fm.D x i).host.g 1` using `td.g2_eq`.

Establish `f1 : O.f = ((Fm.D x i).R.f : ℝ)` using `td.f_eq`. Establish `k1 : O.k = ((Fm.D x i).R.k : ℝ)` using `td.k_eq`. Establish `hrec : (R2 p).grp_record`. Take `⟨plg, iso, -, h2, h3, h4⟩` from `p.grpRecPin`. Conclude with `⟨p.R.eG.trans p.cG, plg, iso, h2, h3, h4⟩`.

Establish `yb : ∀ {large₂ : SizeData₂ (Fm.D x i)} {Pm : ParameterChoice' (Fm.D x i) large₂}, ParamsT (Fm.D x i) large₂ Pm → LeafYBound (onOf (R2 p) (F2 p) c (supArgs (R2 p)))` using `fun {_ Pm} _ => leafYBound (F := F2 p) c (supArgs (R2 p)) Pm`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `leafLevelSq (F := F2 p) c (supArgs (R2 p)) hrec` as an intermediate fact. Unfold `LeafLevelSq`. Rewrite using `[g1, g2]`.

Conclude with `this`. Use `yb (Fm.parT x hx i)` as an intermediate fact. Unfold `LeafYBound OnObj.y`. Rewrite using `[g1, g2, f1, k1]`. Conclude with `this`.
-/
theorem levelSq_yBound_atRec_alt :
    _root_.GlobalTheory.BigOn.ForallRecordObjects fun Fm x _ i p _ O => LeafLevelSq O (Res (R2 p)) (Fm.D x i).R.f ∧ LeafYBound O := by
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ =>
    ⟨0, fun c _ _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun x hx i p _ _ r O hO => ?_⟩⟩⟩
  obtain ⟨st, td⟩ := hO.1.depth
  letI := hostAlg (Fm.D x i)
  have g1 : O.g1 = (Fm.D x i).host.g 0 := td.jets_eq_fact
  have g2 : O.g2 = (Fm.D x i).host.g 1 := td.g2_eq
  have f1 : O.f = ((Fm.D x i).R.f : ℝ) := td.f_eq
  have k1 : O.k = ((Fm.D x i).R.k : ℝ) := td.k_eq
  have hrec : (R2 p).grp_record := by
    obtain ⟨plg, iso, -, h2, h3, h4⟩ := p.grpRecPin
    exact ⟨p.R.eG.trans p.cG, plg, iso, h2, h3, h4⟩
  have yb : ∀ {large₂ : SizeData₂ (Fm.D x i)} {Pm : ParameterChoice' (Fm.D x i) large₂}, ParamsT (Fm.D x i) large₂ Pm →
      LeafYBound (onOf (R2 p) (F2 p) c (supArgs (R2 p))) := fun {_ Pm} _ =>
    leafYBound (F := F2 p) c (supArgs (R2 p)) Pm
  refine ⟨?_, ?_⟩
  · have := leafLevelSq (F := F2 p) c (supArgs (R2 p)) hrec
    unfold LeafLevelSq
    rw [g1, g2]
    exact this
  · have := yb (Fm.parT x hx i)
    unfold LeafYBound OnObj.y
    rw [g1, g2, f1, k1]
    exact this
end GlobalTheory.BigOn
end
end
