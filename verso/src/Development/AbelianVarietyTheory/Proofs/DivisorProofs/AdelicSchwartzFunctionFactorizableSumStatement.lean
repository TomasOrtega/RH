import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFunctionFactorizableSum
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply

open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.DblEval
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SBRestrProd.sb_eq_sum_restrProd` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAdelicSchwartzFunctionFactorizableSum.lean&line=256#L256)
-/
theorem _root_.GlobalTheory.T.adelic_schwartz_function_factorizable_sum : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (a : (κ → Af F) → ℂ), a ∈ SB (κ → Af F) → ∃ (m : ℕ) (φ : Fin m → ∀ v : Pl F, (κ → Fv F v) → ℂ), (∀ j v, φ j v ∈ SB (κ → Fv F v)) ∧ (∀ j, ∀ᶠ v in cofinite, φ j v = stdInd F κ v) ∧ ∀ x, a x = ∑ j, ∏ᶠ v, φ j v fun i => evalV F v (x i) := by
  first | exact @GlobalTheory.SBRestrProd.sb_eq_sum_restrProd | exact GlobalTheory.SBRestrProd.sb_eq_sum_restrProd | (intros; apply GlobalTheory.SBRestrProd.sb_eq_sum_restrProd <;> assumption)
