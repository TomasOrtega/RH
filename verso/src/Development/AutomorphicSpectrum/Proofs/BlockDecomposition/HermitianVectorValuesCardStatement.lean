import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianVectorValuesCard
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.UnrDens.Sphere.count` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FHermitianVectorValuesCard.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.hermitian_vector_values_card : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module E V] (B : HermSp E τ V), Nat.card V = q ^ (2 * m) → (∀ c : E, τ c = c → c ≠ 0 → (Nat.card {v : V // B.h v v = c} : ℝ) = (q : ℝ) ^ (2 * m) / q * (1 - ((ε : ℝ) / q) ^ m)) ∧ (Nat.card {v : V // B.h v v = 0} : ℝ) = (q : ℝ) ^ (2 * m) / q * (1 + ((q : ℝ) - 1) * ((ε : ℝ) / q) ^ m) := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.Sphere.count | exact GlobalTheory.CompanionTheory.UnrDens.Sphere.count | (intros; apply GlobalTheory.CompanionTheory.UnrDens.Sphere.count <;> assumption)
