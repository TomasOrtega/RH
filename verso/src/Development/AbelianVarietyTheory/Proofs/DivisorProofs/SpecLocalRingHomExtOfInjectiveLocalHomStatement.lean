import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecLocalRingHomExtOfInjectiveLocalHom
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSpecLocalRingHomExtOfInjectiveLocalHom.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.spec_localRing_hom_ext_of_injective_localHom : ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (φ : R →+* R'), IsLocalHom φ → Function.Injective φ → ∀ (Y : Scheme.{0}) (x y : Sp R ⟶ Y), spMap φ ≫ x = spMap φ ≫ y → x = y := by
  first | exact @GlobalTheory.spec_local_hom_ext_of_injective | exact GlobalTheory.spec_local_hom_ext_of_injective | (intros; apply GlobalTheory.spec_local_hom_ext_of_injective <;> assumption)
