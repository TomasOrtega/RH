import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemipositiveOfIsometric
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSemipositiveOfIsometric.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.semipositive_of_isometric : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (L M : GlobalTheory.HermLB p) (D : ℕ), L.Isometric M → L.SemiPos D → M.SemiPos D := by
  first | exact @GlobalTheory.HermLB.Isometric.semiPos | exact GlobalTheory.HermLB.Isometric.semiPos | (intros; apply GlobalTheory.HermLB.Isometric.semiPos <;> assumption)
