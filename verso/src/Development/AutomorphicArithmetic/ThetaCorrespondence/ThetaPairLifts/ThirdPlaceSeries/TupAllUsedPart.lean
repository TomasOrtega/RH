import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowOfCovolumeOntoGrid
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SummandFunctionalBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtOf

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc
namespace GlobalTheory.Fc.FourBoundsAtBundles
/- English proof (translation)
Introduce `t`. Break down `b.pt.charW.tup.mu_used t with h | ⟨w, hw⟩` into its components or cases. Use `left`. Substitute `h` using the available equality. Conclude with `b.P.tied.div.tup.mu0`.

Use `right`. Use `⟨D.plEq.symm w, ?_⟩` and prove the remaining obligations. Establish `e1` using `b.pt.tupAt (D.plEq.symm w)`. Rewrite `e1` using `[Equiv.apply_symm_apply]`. Establish `e2` using `b.pt.tupTie (D.what₂.muAt (D.plEq.symm w)) (Or.inr ⟨_, rfl⟩)`.

Rewrite `e2` using `[e1, hw]`. Conclude with `e2`.
-/
theorem tupAllUsed_part_alt {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c) : Formalism.L2.DIV.TupAllUsed b.P := by
  intro t
  rcases b.pt.charW.tup.mu_used t with h | ⟨w, hw⟩
  · left
    subst h
    exact b.P.tied.div.tup.mu0
  · right
    refine ⟨D.plEq.symm w, ?_⟩
    have e1 := b.pt.tupAt (D.plEq.symm w)
    rw [Equiv.apply_symm_apply] at e1
    have e2 := b.pt.tupTie (D.what₂.muAt (D.plEq.symm w)) (Or.inr ⟨_, rfl⟩)
    rw [e1, hw] at e2
    exact e2
/- English proof (translation)
The claim follows from `Formalism.L2.DIV.DivRows3G.toRows (_root_.GlobalTheory.Fc.FourBoundsAtBundles.tupAllUsed_part_alt b) ⟨h.sharpRR, h.baseRR, h.divisionRows_rationalLift, h.thTheta, ⟨h.num.Ij, h.num.jw, h.num.etaJ⟩, h.colsBk⟩`.
-/
theorem p_div_of_div3g {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c) (h : GlobalTheory.Cp.DivRows3G b.P) : _root_.GlobalTheory.Fc.Ind.DivisorPointSummands D O c b :=
  Formalism.L2.DIV.DivRows3G.toRows (_root_.GlobalTheory.Fc.FourBoundsAtBundles.tupAllUsed_part_alt b)
    ⟨h.sharpRR, h.baseRR, h.divisionRows_rationalLift, h.thTheta, ⟨h.num.Ij, h.num.jw, h.num.etaJ⟩, h.colsBk⟩
end GlobalTheory.Fc.FourBoundsAtBundles
namespace GlobalTheory.Fc.FourBoundsAtBundles
end GlobalTheory.Fc.FourBoundsAtBundles
end
