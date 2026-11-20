import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TorusFieldComplexRootsNormEqOneCompact
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CxRootsInjective
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll GlobalTheory.TrEll.RealTorus
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TrEll.realTorus_norm_cxRoots` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FTorusFieldComplexRootsNormEqOneCompact.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.torusFieldComplexRoots_norm_eq_one_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (w : InfinitePlace F) (τ : EmbOver E w), Function.Bijective (PsiAll P τ) → CompactSpace (Tor P w.Completion) → ∀ i, ‖cxRoots τ.1 P i‖ = 1 := by
  first | exact @GlobalTheory.TrEll.realTorus_norm_cxRoots | exact GlobalTheory.TrEll.realTorus_norm_cxRoots | (intros; apply GlobalTheory.TrEll.realTorus_norm_cxRoots <;> assumption)
