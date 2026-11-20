import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

/- English proof (translation)
Introduce `Z Y s s' c h d _ hc`. Substitute `h` using the available equality. Establish `h0 : SmoothOfRelativeDimension 0 c` using `(Etale.iff_smoothOfRelativeDimension_zero c).1 hc`. Establish `h1 : SmoothOfRelativeDimension (0 + d) (c ≫ s)` using `smoothOfRelativeDimension_comp 0 d c s`. Rewrite `h1` using `[Nat.zero_add]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.Cb.smoothOfRelativeDimension_comp_etale :
    ∀ (Z Y : Scheme.{0}) (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) (c : Y ⟶ Z), c ≫ s = s' → ∀ (d : ℕ) [SmoothOfRelativeDimension d s], Etale c → SmoothOfRelativeDimension d s' := by
  intro Z Y s s' c h d _ hc
  subst h
  have h0 : SmoothOfRelativeDimension 0 c := (Etale.iff_smoothOfRelativeDimension_zero c).1 hc
  have h1 : SmoothOfRelativeDimension (0 + d) (c ≫ s) := smoothOfRelativeDimension_comp 0 d c s
  rwa [Nat.zero_add] at h1
