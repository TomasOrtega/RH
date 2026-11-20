import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricH1ZetaSubOneKills
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.K5.TateGeo.h1_killed_by_zeta_sub_one_geo` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FGeometricH1ZetaSubOneKills.lean&line=124#L124)
-/
theorem _root_.GlobalTheory.T.geometric_h1_zeta_sub_one_kills : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (k j : ℕ), 1 ≤ j → ∀ c : Gal p Ω → Ω, IntegralLocallyConstCochainModPow k (Ggeo p Ω ⊓ ⨅ n, Gn T n) c →
  (∀ g ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, ∀ h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, Cong p k (c (g * h)) (c g + g (c h))) →
  Cob1 k (Ggeo p Ω ⊓ ⨅ n, Gn T n) (fun g => (T.ζ j - 1) * c g) := by
  first | exact @GlobalTheory.K5.TateGeo.h1_killed_by_zeta_sub_one_geo | exact GlobalTheory.K5.TateGeo.h1_killed_by_zeta_sub_one_geo | (intros; apply GlobalTheory.K5.TateGeo.h1_killed_by_zeta_sub_one_geo <;> assumption)
