import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestKTypeSmoothVectorsIsKStable
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SmoothLowKStable.isKStableOn_lowKSub_inf_sm` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FLowestKTypeSmoothVectorsIsKStable.lean&line=94#L94)
-/
theorem _root_.GlobalTheory.T.lowestKType_smoothVectors_isKStable : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau), IsKStableOn (M.ε τ) (M.σ τ) (lowKSub (M.ε τ) (M.lam τ) (M.σ τ) ⊓ M.sm τ) := by
  first | exact @GlobalTheory.SmoothLowKStable.isKStableOn_lowKSub_inf_sm | exact GlobalTheory.SmoothLowKStable.isKStableOn_lowKSub_inf_sm | (intros; apply GlobalTheory.SmoothLowKStable.isKStableOn_lowKSub_inf_sm <;> assumption)
