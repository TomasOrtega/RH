import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerModEqOrthogonalRangeShearAddNsmul
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivOfIsometryApply
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FKerModEqOrthogonalRangeShearAddNsmul.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.ker_mod_eq_orthogonal_range_shear_add_nsmul : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X]
    (y : D.La →ₗ[𝓞 E] X) (n : ℕ), 0 < n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    (∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) → ∀ t : Z →ₗ[𝓞 E] D.La, (∀ z : Z, t z - z ∈ perp D Z') →
    (∀ z z' : Z, D.EF (t z) (t z') = 0) → (∀ (z : Z) (a : D.La), (∃ e, y a = n • e) → (n : ℤ) ∣ D.EF (t z) a) →
    ∀ a, (∃ e, y a = n • e) ↔ ∃ b ∈ perp D (LinearMap.range t), ∃ e, a = b + n • e := by
  first | exact @GlobalTheory.LowFilt.ker_mod_eq_perp_range_add | exact GlobalTheory.LowFilt.ker_mod_eq_perp_range_add | (intros; apply GlobalTheory.LowFilt.ker_mod_eq_perp_range_add <;> assumption)
