import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepBeforeLastEqSSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleFreeLevelLeCompact
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTupleFreeRelationStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CarriesLatticeCompletionOfEachPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeClosed
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

noncomputable section
namespace GlobalTheory.PenLev

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.

Introduce a local definition for the expression. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem tuple_free_level_moves : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : QJ a t), J.Reads → ∀ g ∈ GlobalTheory.PenLev.U0 a j hj, GlobalTheory.FinPl.Moves _ g (a.g.x j).L (a.g.x j).L (GlobalTheory.PenBridge.plF J) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ g hg
  have hch : ∀ i, Nonempty ((J.E i).Ch j) := fun i => by
    obtain ⟨y, -⟩ := (J.E i).cos_all 0 (zero_mem _)
    rw [GlobalTheory.PenBridge.step_before_last_eq_s_succ J hj i]
    exact ⟨y⟩
  let α : J.Ch j := fun i => (hch i).some
  rw [← GlobalTheory.T.true_geometry_tuple_free_relation W hW u a ha hTr j hj t J hJ α, mem_relax_iff] at hg
  obtain ⟨-, -, hK⟩ := hg
  have hsd : IsSelfDualC ((I.rec7 l Z).sp.X j) (a.g.x j).L :=
    (ha.x j (by have h2 : (I.rec7 l Z).R.m = B.R.m := rfl; omega)).sd
  have hP : GlobalTheory.PenBridge.plF J = (· ∈ Finset.univ.image fun i => (J.G i).q.v) := by
    funext p
    simp [GlobalTheory.PenBridge.plF]
  rw [hP]
  refine GlobalTheory.FinPl.MovesPl.moves_of_places _ _ _ _ _ fun v hv => ?_
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
  refine GlobalTheory.LevProd.SamePlace.moves_of_mem_KO (J.G i).q (GlobalTheory.PenBridge.frJ J j i (GlobalTheory.PenBridge.step_before_last_eq_s_succ J hj i)) hsd
    (GlobalTheory.PenBridge.intIn_frJ J j i _) ?_
  have h1 := hK i
  rw [GlobalTheory.PenBridge.rd, MonoidHom.pi_apply, GlobalTheory.PenBridge.rdAt_apply] at h1
  exact (GlobalTheory.PenBridge.toSum0_mem_KO_iff _).1 h1

end GlobalTheory.PenLev
end
