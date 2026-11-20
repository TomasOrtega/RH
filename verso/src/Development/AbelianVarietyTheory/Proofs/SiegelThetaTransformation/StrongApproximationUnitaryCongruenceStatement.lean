import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.StrongApproximationUnitaryCongruence
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSiegelThetaTransformation%2FStrongApproximationUnitaryCongruence.lean&line=282#L282)
-/
theorem _root_.GlobalTheory.T.strong_approximation_unitary_congruence : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (𝔪 : Ideal (𝓞 E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (conjI 𝔪) → ∀ (A : GL (Fin r) E) (N : ℕ), ∃ ga : GL (Fin r) E, IsUn X ga ∧ ∃ s : 𝓞 E, IsCoprime (Ideal.span {s}) 𝔪 ∧ ∀ i j, ∃ b ∈ 𝔪 ^ N, (s : E) * ((ga : Matrix (Fin r) (Fin r) E) i j - (A : Matrix (Fin r) (Fin r) E) i j) = (b : E) := by
  first | exact @GlobalTheory.UnApprox.weak_approx | exact GlobalTheory.UnApprox.weak_approx | (intros; apply GlobalTheory.UnApprox.weak_approx <;> assumption)
