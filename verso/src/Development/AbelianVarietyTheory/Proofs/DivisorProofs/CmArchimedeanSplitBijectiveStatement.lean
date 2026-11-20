import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmArchimedeanSplitBijective
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombineApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchPartFinIncl
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ArchFinSplit.splitHom_bijective` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCmArchimedeanSplitBijective.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.cm_archimedean_split_bijective : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (τ : ∀ w : InfinitePlace F, EmbOver E w), IsCMExt F E σ → Function.Bijective (GlobalTheory.ArchFinSplit.splitHom τ) := by
  first | exact @GlobalTheory.ArchFinSplit.splitHom_bijective | exact GlobalTheory.ArchFinSplit.splitHom_bijective | (intros; apply GlobalTheory.ArchFinSplit.splitHom_bijective <;> assumption)
