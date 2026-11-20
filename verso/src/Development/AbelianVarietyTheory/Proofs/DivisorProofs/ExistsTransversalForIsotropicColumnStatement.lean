import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransversalForIsotropicColumn
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsTransversalForIsotropicColumn.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.exists_transversal_for_isotropic_column : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E), ∃ T, GlobalTheory.EisCT.IsTransv σ J x T := by
  first | exact @GlobalTheory.EisCT.exists_isTransv | exact GlobalTheory.EisCT.exists_isTransv | (intros; apply GlobalTheory.EisCT.exists_isTransv <;> assumption)
