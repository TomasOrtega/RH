import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormEqZeroOfVanishingOnPairs
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpen
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR Opposite KaehlerDifferential
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FOneFormEqZeroOfVanishingOnPairs.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.oneForm_eq_zero_of_vanishing_on_pairs : ∀ {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X) (s' : X' ⟶ Sp R') (W : X'.affineOpens) (ω : Ω[(OAff s').obj (op W)⁄R']), (∀ (p : Pair φ) (hp : p.1.1 ≤ W), p1 (OAff s') (homOfLE hp).op ω = 0) → ω = 0 := by
  first | exact @GlobalTheory.CechDR.form_eq_zero_of_pair | exact GlobalTheory.CechDR.form_eq_zero_of_pair | (intros; apply GlobalTheory.CechDR.form_eq_zero_of_pair <;> assumption)
