import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthDecSumLatticeSelfDual
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittDecompositionCoreProjMulCoreEqOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Core.Rk.SumSplit

/- English proof (translation)
Introduce `D S A B o LA LB v y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Use `⟨GlobalTheory.SeeSaw.SplitLat.rat_mulVec_mem_latV o.qA (fun x hx => ?_) _ hy, GlobalTheory.SeeSaw.SplitLat.rat_mulVec_mem_latV o.qB (fun x hx => ?_) _ hy⟩` and prove the remaining obligations. Take `⟨x₁, hx₁, x₂, -, rfl⟩` from `(GlobalTheory.Core.Rk.SumBox.mem_sumLatO o LA LB x).1 hx`.

Rewrite using `[GlobalTheory.Core.Rk.SumBox.qA_split]`. Conclude with `hx₁`. Take `⟨x₁, -, x₂, hx₂, rfl⟩` from `(GlobalTheory.Core.Rk.SumBox.mem_sumLatO o LA LB x).1 hx`. Rewrite using `[GlobalTheory.Core.Rk.SumBox.qB_split]`. Conclude with `hx₂`.

Introduce and unpack `⟨hA, hB⟩`. Establish `e : y = o.jA *ᵥ (o.pA *ᵥ y) + o.jB *ᵥ (o.pB *ᵥ y)`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, o.sum_eq_one, Matrix.one_mulVec]`. Rewrite using `[e]`. Conclude with `add_mem (GlobalTheory.SeeSaw.SplitLat.rat_mulVec_mem_latV o.iA (fun x hx => GlobalTheory.Core.Rk.SumBox.iA_mem_sumLatO o LB hx) _ hA) (GlobalTheory.SeeSaw.SplitLat.rat_mulVec_mem_latV o.iB (fun x hx => GlobalTheory.Core.Rk.SumBox.iB_mem_sumLatO o LA hx) _ hB)`.
-/
theorem orthAt_sumLatO : ∀ (D : D7) (S A B : HSp D) (o : OrthDec S A B) (LA : Lat A) (LB : Lat B) (v : Pl D),
    OrthAt o (GlobalTheory.Core.Rk.SumBox.sumLatO o LA LB) LA LB v := by
  intro D S A B o LA LB v y
  constructor
  · intro hy
    refine ⟨GlobalTheory.SeeSaw.SplitLat.rat_mulVec_mem_latV o.qA (fun x hx => ?_) _ hy,
      GlobalTheory.SeeSaw.SplitLat.rat_mulVec_mem_latV o.qB (fun x hx => ?_) _ hy⟩
    · obtain ⟨x₁, hx₁, x₂, -, rfl⟩ := (GlobalTheory.Core.Rk.SumBox.mem_sumLatO o LA LB x).1 hx
      rw [GlobalTheory.Core.Rk.SumBox.qA_split]; exact hx₁
    · obtain ⟨x₁, -, x₂, hx₂, rfl⟩ := (GlobalTheory.Core.Rk.SumBox.mem_sumLatO o LA LB x).1 hx
      rw [GlobalTheory.Core.Rk.SumBox.qB_split]; exact hx₂
  · rintro ⟨hA, hB⟩
    have e : y = o.jA *ᵥ (o.pA *ᵥ y) + o.jB *ᵥ (o.pB *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, o.sum_eq_one, Matrix.one_mulVec]
    rw [e]
    exact add_mem
      (GlobalTheory.SeeSaw.SplitLat.rat_mulVec_mem_latV o.iA
        (fun x hx => GlobalTheory.Core.Rk.SumBox.iA_mem_sumLatO o LB hx) _ hA)
      (GlobalTheory.SeeSaw.SplitLat.rat_mulVec_mem_latV o.iB
        (fun x hx => GlobalTheory.Core.Rk.SumBox.iB_mem_sumLatO o LA hx) _ hB)

end GlobalTheory.Core.Rk.SumSplit
end
