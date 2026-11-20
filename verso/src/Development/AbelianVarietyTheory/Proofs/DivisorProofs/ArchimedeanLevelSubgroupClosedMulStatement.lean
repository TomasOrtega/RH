import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanLevelSubgroupClosedMul
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemFinPt
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.kInf_one_mul_commute_finPt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FArchimedeanLevelSubgroupClosedMul.lean&line=45#L45)
-/
theorem _root_.GlobalTheory.T.archimedean_level_subgroup_closed_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w), (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J) ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W τ ∧ (∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W τ, ∀ k' ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W τ, k * k' ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W τ) ∧ ∀ l ∈ GlobalTheory.ThKAdm.FinPt σ W, ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W τ, l * k = k * l := by
  first | exact @GlobalTheory.kInf_one_mul_commute_finPt | exact GlobalTheory.kInf_one_mul_commute_finPt | (intros; apply GlobalTheory.kInf_one_mul_commute_finPt <;> assumption)
