import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleOfFiniteLengthSubquotients
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FAdmissibleOfFiniteLengthSubquotients.lean&line=150#L150)
-/
theorem _root_.GlobalTheory.T.admissible_of_finite_length_subquotients : ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), IsSmooth ρ → HasFiniteLength ρ → (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W), IsSubquotient σ ρ → σ.IsIrreducible → IsAdmissible σ) → IsAdmissible ρ := by
  first | exact @GlobalTheory.CompanionTheory.AdmFL.isAdmissible_of_hasFiniteLength | exact GlobalTheory.CompanionTheory.AdmFL.isAdmissible_of_hasFiniteLength | (intros; apply GlobalTheory.CompanionTheory.AdmFL.isAdmissible_of_hasFiniteLength <;> assumption)
