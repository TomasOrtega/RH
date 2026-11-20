import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarUnitaryRightInvariant
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLineStab
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open GlobalTheory.IwasawaKAvgInt
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ArchPartUnimod.haar_map_mul_right` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHaarUnitaryRightInvariant.lean&line=152#L152)
-/
theorem _root_.GlobalTheory.T.haar_unitary_right_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    ∀ μ : Measure (UAtSub σ X (evI F)), μ.IsHaarMeasure → ∀ g : UAtSub σ X (evI F), μ.map (· * g) = μ := by
  first | exact @GlobalTheory.ArchPartUnimod.haar_map_mul_right | exact GlobalTheory.ArchPartUnimod.haar_map_mul_right | (intros; apply GlobalTheory.ArchPartUnimod.haar_map_mul_right <;> assumption)
