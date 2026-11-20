import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NoetherianIdealIntegralOrSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FNoetherianIdealIntegralOrSplit.lean&line=102#L102)
-/
theorem _root_.GlobalTheory.T.noetherian_ideal_integral_or_split : ∀ {X : Scheme.{0}} [IsNoetherian X] (J : X.IdealSheafData), J ≠ ⊤ → IsIntegral J.subscheme ∨ ∃ J₁ J₂ : X.IdealSheafData, J < J₁ ∧ J < J₂ ∧ ∀ (U : X.affineOpens) (a b : Γ(X, U)), a ∈ J₁.ideal U → b ∈ J₂.ideal U → a * b ∈ J.ideal U := by
  first | exact @GlobalTheory.CompanionTheory.GE.Dich.isIntegral_or_exists_mul_mem | exact GlobalTheory.CompanionTheory.GE.Dich.isIntegral_or_exists_mul_mem | (intros; apply GlobalTheory.CompanionTheory.GE.Dich.isIntegral_or_exists_mul_mem <;> assumption)
