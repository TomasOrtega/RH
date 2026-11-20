import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleConjFunctional
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAdmissibleConjFunctional.lean&line=43#L43)
-/
theorem _root_.GlobalTheory.T.admissible_conj_functional : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ l ∈ (adeleClass F).adm κ, ∀ l' : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ, (∀ Φ, l' Φ = starRingEnd ℂ (l (fun x => starRingEnd ℂ (Φ x)))) → l' ∈ (adeleClass F).adm κ := by
  first | exact @GlobalTheory.AdmConj.conj_mem_adm | exact GlobalTheory.AdmConj.conj_mem_adm | (intros; apply GlobalTheory.AdmConj.conj_mem_adm <;> assumption)
