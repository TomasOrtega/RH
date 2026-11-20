import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLastStepIntertwinerChain
import Formalism.LocalToGlobal.IndefiniteReal.LinksW
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Twist.LastStepExists.exists_lastStep_intertwiner` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsLastStepIntertwinerChain.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_lastStep_intertwiner_chain : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.IsChainW → R.ex_ItX := by
  first | exact @GlobalTheory.Twist.LastStepExists.exists_lastStep_intertwiner | exact GlobalTheory.Twist.LastStepExists.exists_lastStep_intertwiner | (intros; apply GlobalTheory.Twist.LastStepExists.exists_lastStep_intertwiner <;> assumption)
