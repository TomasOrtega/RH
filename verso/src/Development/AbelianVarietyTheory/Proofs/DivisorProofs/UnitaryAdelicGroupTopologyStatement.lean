import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnitaryAdelicGroupTopology.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.unitary_adelic_group_topology : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E), IsTopologicalGroup (UA σ J) ∧ LocallyCompactSpace (UA σ J) ∧
      SecondCountableTopology (UA σ J) ∧ T2Space (UA σ J) := by
  first | exact @GlobalTheory.UnitaryAdelicTop.lcsc_UA | exact GlobalTheory.UnitaryAdelicTop.lcsc_UA | (intros; apply GlobalTheory.UnitaryAdelicTop.lcsc_UA <;> assumption)
