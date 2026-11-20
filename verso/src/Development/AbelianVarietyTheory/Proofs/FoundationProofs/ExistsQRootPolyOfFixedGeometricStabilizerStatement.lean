import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsQRootPolyOfFixedGeometricStabilizer
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.K5.span_fixed_ggeo_stab` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsQRootPolyOfFixedGeometricStabilizer.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.exists_qRoot_poly_of_fixed_geometric_stabilizer : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (N : ℕ) (y : Ω), (∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g y = y) →
  ∃ c : ℕ → Ω, (∀ j, ∀ g ∈ Ggeo p Ω, g (c j) = c j) ∧
    y = ∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j := by
  first | exact @GlobalTheory.K5.span_fixed_ggeo_stab | exact GlobalTheory.K5.span_fixed_ggeo_stab | (intros; apply GlobalTheory.K5.span_fixed_ggeo_stab <;> assumption)
