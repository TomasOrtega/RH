import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergFiniteAdelicIrreducible
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisFin
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.FinHeis
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FinSchrIrred.schrodinger_irreducible` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHeisenbergFiniteAdelicIrreducible.lean&line=140#L140)
-/
theorem _root_.GlobalTheory.T.heisenberg_finite_adelic_irreducible : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), Continuous ψ → (∀ v : HeightOneSpectrum (𝓞 F), ∃ t : Fv F v, psiLoc ψ v t ≠ 1) → ∀ N : Submodule ℂ ((κ → Af F) → ℂ), N ≤ SB (κ → Af F) → (∀ (a b : κ → Af F), ∀ g ∈ N, heisFin F ψ a b g ∈ N) → N = ⊥ ∨ N = SB (κ → Af F) := by
  first | exact @GlobalTheory.FinSchrIrred.schrodinger_irreducible | exact GlobalTheory.FinSchrIrred.schrodinger_irreducible | (intros; apply GlobalTheory.FinSchrIrred.schrodinger_irreducible <;> assumption)
