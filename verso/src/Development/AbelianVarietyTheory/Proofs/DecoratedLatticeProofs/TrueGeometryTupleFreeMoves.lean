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
Introduce `B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ g hg`. Establish `hch : ∀ i, Nonempty ((J.E i).Ch j)` using `fun i => by`. Take `⟨y, -⟩` from `(J.E i).cos_all 0 (zero_mem _)`. Rewrite using `[GlobalTheory.PenBridge.step_before_last_eq_s_succ J hj i]`. Conclude with `⟨y⟩`.

Set `α : J.Ch j` to `fun i => (hch i).some`. Rewrite `hg` using `[← GlobalTheory.T.true_geometry_tuple_free_relation W hW u a ha hTr j hj t J hJ α, mem_relax_iff]`. Take `⟨-, -, hK⟩` from `hg`. Establish `hsd : IsSelfDualC ((I.rec7 l Z).sp.X j) (a.g.x j).L` using `(ha.x j (by have h2 : (I.rec7 l Z).R.m = B.R.m := rfl; omega)).sd`. Establish `hP : GlobalTheory.PenBridge.plF J = (· ∈ Finset.univ.image fun i => (J.G i).q.v)`.

Use function extensionality and compare the values at `p`. Simplify using `[GlobalTheory.PenBridge.plF]`. Rewrite using `[hP]`. Use `GlobalTheory.FinPl.MovesPl.moves_of_places _ _ _ _ _ fun v hv => ?_` and prove the remaining obligations. Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 hv`.

Use `GlobalTheory.LevProd.SamePlace.moves_of_mem_KO (J.G i).q (GlobalTheory.PenBridge.frJ J j i (GlobalTheory.PenBridge.step_before_last_eq_s_succ J hj i)) hsd (GlobalTheory.PenBridge.intIn_frJ J j i _) ?_` and prove the remaining obligations. Establish `h1` using `hK i`. Rewrite `h1` using `[GlobalTheory.PenBridge.rd, MonoidHom.pi_apply, GlobalTheory.PenBridge.rdAt_apply]`. Conclude with `(GlobalTheory.PenBridge.toSum0_mem_KO_iff _).1 h1`.
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
