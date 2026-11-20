import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

/- English proof (translation)
Introduce and unpack `Z s V hV ⟨N, i, hi, rfl⟩`. Establish `hc : IsClosedImmersion V.ι`. Apply `IsClosedImmersion.of_isPreimmersion` to reduce the goal to its premises. Simplify using `using hV`. Conclude with `⟨N, V.ι ≫ i, inferInstance, by simp⟩`.
-/
theorem UpperTheory.Cb.isProjOver_restrict_clopen :
    ∀ (Z : Scheme.{0}) (s : Z ⟶ Sp ℂ) (V : Z.Opens), IsClosed (V : Set Z) → IsProjOver s → IsProjOver (V.ι ≫ s) := by
  rintro Z s V hV ⟨N, i, hi, rfl⟩
  have hc : IsClosedImmersion V.ι := by
    apply IsClosedImmersion.of_isPreimmersion
    simpa using hV
  exact ⟨N, V.ι ≫ i, inferInstance, by simp⟩
