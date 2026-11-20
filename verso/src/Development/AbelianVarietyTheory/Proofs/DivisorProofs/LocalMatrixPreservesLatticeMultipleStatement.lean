import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixPreservesLatticeMultiple
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocKLeLocU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexConjNeZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SphLineComm.Bound.nsmul_mulVec_mem_latHat` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLocalMatrixPreservesLatticeMultiple.lean&line=193#L193)
-/
theorem _root_.GlobalTheory.T.local_matrix_preserves_lattice_multiple : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (W : Spc F E d) (v : Pl F)
    (M : Matrix (Fin d) (Fin d) (AE F E)), W.L.IsLattice E → At (evFin F v) M →
    ∃ n : ℕ, n ≠ 0 ∧ ∀ z ∈ latHat W, n • (M *ᵥ z) ∈ latHat W := by
  first | exact @GlobalTheory.SphLineComm.Bound.nsmul_mulVec_mem_latHat | exact GlobalTheory.SphLineComm.Bound.nsmul_mulVec_mem_latHat | (intros; apply GlobalTheory.SphLineComm.Bound.nsmul_mulVec_mem_latHat <;> assumption)
