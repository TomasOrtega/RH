import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalPointModelEval
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocPt

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FinComm.exists_At_locPt_eq` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsLocalPointModelEval.lean&line=35#L35)
-/
theorem _root_.GlobalTheory.T.exists_local_point_model_eval : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (v : Pl F)
    (p : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)),
    ∃ w : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) w ∧ GlobalTheory.FinComm.locPt v (M.co.e w) = p := by
  first | exact @GlobalTheory.FinComm.exists_At_locPt_eq | exact GlobalTheory.FinComm.exists_At_locPt_eq | (intros; apply GlobalTheory.FinComm.exists_At_locPt_eq <;> assumption)
