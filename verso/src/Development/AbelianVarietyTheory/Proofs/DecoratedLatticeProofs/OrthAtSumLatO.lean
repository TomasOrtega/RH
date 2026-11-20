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
Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
