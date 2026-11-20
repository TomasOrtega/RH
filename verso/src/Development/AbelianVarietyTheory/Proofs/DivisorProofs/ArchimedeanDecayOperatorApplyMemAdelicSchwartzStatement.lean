import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanDecayOperatorApplyMemAdelicSchwartz
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordAppend
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FArchimedeanDecayOperatorApplyMemAdelicSchwartz.lean&line=109#L109)
-/
theorem _root_.GlobalTheory.T.archimedeanDecayOperatorApply_mem_adelicSchwartz : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (o : Op F κ), ∀ f ∈ schA F κ, app F o f ∈ schA F κ := by
  first | exact @GlobalTheory.ArchDecay.SchAStab.app_mem_schA | exact GlobalTheory.ArchDecay.SchAStab.app_mem_schA | (intros; apply GlobalTheory.ArchDecay.SchAStab.app_mem_schA <;> assumption)
