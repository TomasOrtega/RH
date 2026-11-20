import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspidalIsometryTransportHermitian
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mem.Isom.isCuspFun_tr` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FIsCuspidalIsometryTransportHermitian.lean&line=119#L119)
-/
theorem _root_.GlobalTheory.T.isCuspidal_isometryTransport_hermitian : ∀ (D : D7) (V V' : HSp D) (I : GlobalTheory.Mem.Isom.IsoMat V V') (φ : GA D V → ℂ), IsCuspFun V φ → IsCuspFun V' (I.tr φ) := by
  first | exact @GlobalTheory.Mem.Isom.isCuspFun_tr | exact GlobalTheory.Mem.Isom.isCuspFun_tr | (intros; apply GlobalTheory.Mem.Isom.isCuspFun_tr <;> assumption)
