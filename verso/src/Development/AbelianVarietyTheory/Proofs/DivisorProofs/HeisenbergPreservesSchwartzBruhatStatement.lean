import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergPreservesSchwartzBruhat
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisFin
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.FinHeis
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FinHeis.heisFin_mem_SB` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHeisenbergPreservesSchwartzBruhat.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.heisenberg_preserves_schwartz_bruhat : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), Continuous ψ → ∀ (a b : κ → Af F), ∀ g ∈ SB (κ → Af F), heisFin F ψ a b g ∈ SB (κ → Af F) := by
  first | exact @GlobalTheory.FinHeis.heisFin_mem_SB | exact GlobalTheory.FinHeis.heisFin_mem_SB | (intros; apply GlobalTheory.FinHeis.heisFin_mem_SB <;> assumption)
