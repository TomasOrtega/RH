import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCmFieldGeneratorAtPrimesDividing
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
Apply `GlobalTheory.Dict.exists_generator_at_primes_dividing` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSiegelThetaTransformation%2FExistsCmFieldGeneratorAtPrimesDividing.lean&line=41#L41)
-/
theorem _root_.GlobalTheory.T.exists_cmField_generator_at_primes_dividing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔍 : Ideal (𝓞 E)) (M : ℕ), 𝔍 ≠ ⊥ → 0 < M → ∃ (α : 𝓞 E) (𝔞 : Ideal (𝓞 E)), α ≠ 0 ∧ Ideal.span {α} = 𝔍 * 𝔞 ∧ IsCoprime 𝔞 (Ideal.span {(M : 𝓞 E)}) := by
  first | exact @GlobalTheory.Dict.exists_generator_at_primes_dividing | exact GlobalTheory.Dict.exists_generator_at_primes_dividing | (intros; apply GlobalTheory.Dict.exists_generator_at_primes_dividing <;> assumption)
