import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSquareAbsNormConjInvariantMovedPrimesIdeal
import Formalism.LocalToGlobal.ProjectiveLattices.ThClass
open NumberField IsDedekindDomain Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SquareNorm.isSquare_absNorm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FIsSquareAbsNormConjInvariantMovedPrimesIdeal.lean&line=53#L53)
-/
theorem _root_.GlobalTheory.T.isSquare_absNorm_conjInvariant_movedPrimes_ideal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (𝔡 : Ideal (𝓞 E)), 𝔡 ≠ ⊥ → 𝔡.map (H.bar : 𝓞 E →+* 𝓞 E) = 𝔡 → (∀ P : Ideal (𝓞 E), P.IsPrime → 𝔡 ≤ P → P.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ P) → IsSquare (Ideal.absNorm 𝔡) := by
  first | exact @GlobalTheory.SquareNorm.isSquare_absNorm | exact GlobalTheory.SquareNorm.isSquare_absNorm | (intros; apply GlobalTheory.SquareNorm.isSquare_absNorm <;> assumption)
