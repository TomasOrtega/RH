import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsQRootPolyOfFixedGeometricStabilizerTau
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.K5.Span.span` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsQRootPolyOfFixedGeometricStabilizerTau.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.exists_qRoot_poly_of_fixed_geometric_stabilizer_tau : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo p Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ (N : ℕ) (z : Ω), (∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g z = z) →
  ∃ c : ℕ → Ω, (∀ j, ∀ g ∈ Ggeo p Ω, g (c j) = c j) ∧ z = ∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j := by
  first | exact @GlobalTheory.K5.Span.span | exact GlobalTheory.K5.Span.span | (intros; apply GlobalTheory.K5.Span.span <;> assumption)
