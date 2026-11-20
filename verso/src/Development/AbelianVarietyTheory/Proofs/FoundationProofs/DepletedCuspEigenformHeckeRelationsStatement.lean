import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepletedCuspEigenformHeckeRelations
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EisM.hecke_relations` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FDepletedCuspEigenformHeckeRelations.lean&line=254#L254)
-/
theorem _root_.GlobalTheory.T.depletedCuspEigenform_heckeRelations : ∀ (k N : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ), 1 ≤ k → 0 < N → Prim k N χ g → (∀ m n : ℕ, m.Coprime n → g (m * n) = g m * g n) ∧ (∀ p r : ℕ, p.Prime → ¬ p ∣ N → g (p ^ (r + 2)) = g p * g (p ^ (r + 1)) - χ p * (p : ℂ) ^ (k - 1) * g (p ^ r)) ∧ ∀ m n : ℕ, 0 < m → 0 < n → g m * g n = ∑ δ ∈ (Nat.gcd m n).divisors, χ δ * (δ : ℂ) ^ (k - 1) * g (m * n / δ ^ 2) := by
  first | exact @GlobalTheory.EisM.hecke_relations | exact GlobalTheory.EisM.hecke_relations | (intros; apply GlobalTheory.EisM.hecke_relations <;> assumption)
