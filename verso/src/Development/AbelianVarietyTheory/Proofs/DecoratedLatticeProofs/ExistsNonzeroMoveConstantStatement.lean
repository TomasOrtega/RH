import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNonzeroMoveConstant
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AdForm.VacBase.vacuum_reads_base` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FExistsNonzeroMoveConstant.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.exists_nonzero_move_constant : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (w : World I l Z) (u : B.Word) (A : ColDat I l Z u (w.C.herm.base.Ch u)) ψ θ, A.Is (w.C.forms u) ψ θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m), ∃ c₀ : ℂ, c₀ ≠ 0 ∧ A.MoveAt θ i hi c₀ 1 1 := by
  first | exact @GlobalTheory.AdForm.VacBase.vacuum_reads_base | exact GlobalTheory.AdForm.VacBase.vacuum_reads_base | (intros; apply GlobalTheory.AdForm.VacBase.vacuum_reads_base <;> assumption)
