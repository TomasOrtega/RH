import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictionPreservesAdelicSchwartz
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixExtendByZeroAdd
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.AdaptEv
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRestrictionPreservesAdelicSchwartz.lean&line=55#L55)
-/
theorem _root_.GlobalTheory.T.restriction_preserves_adelic_schwartz : ∀ (F : Type) [Field F] [NumberField F] {κ ι κ₁ : Type} [Fintype κ] [Fintype ι] [Fintype κ₁] (eq : κ ≃ ι ⊕ κ₁),
    ∀ Φ ∈ schA F κ, restrL eq Φ ∈ schA F κ₁ := by
  first | exact @GlobalTheory.ThK.AdaptEv.restrL_mem_schA | exact GlobalTheory.ThK.AdaptEv.restrL_mem_schA | (intros; apply GlobalTheory.ThK.AdaptEv.restrL_mem_schA <;> assumption)
