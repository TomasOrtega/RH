import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonemptyNormalOpenArithmeticVariety
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsNonemptyNormalOpenArithmeticVariety.lean&line=69#L69)
-/
theorem _root_.GlobalTheory.T.exists_nonempty_normal_open_arithmeticVariety : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∃ Ω : X.Opens, (Ω : Set X).Nonempty ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Ω.toScheme := by
  first | exact @GlobalTheory.NormalOpen.exists_normal_opens | exact GlobalTheory.NormalOpen.exists_normal_opens | (intros; apply GlobalTheory.NormalOpen.exists_normal_opens <;> assumption)
