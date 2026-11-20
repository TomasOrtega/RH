import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPowIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ArInt.nefFib_pow_iff` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FNefFibPowIff.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.nefFib_pow_iff' : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsProjOver p → ∀ (L : HermLB p) (m : ℕ), 0 < m → (ArInt.NefFib (L.pow m) ↔ ArInt.NefFib L) := by
  first | exact @GlobalTheory.ArInt.nefFib_pow_iff | exact GlobalTheory.ArInt.nefFib_pow_iff | (intros; apply GlobalTheory.ArInt.nefFib_pow_iff <;> assumption)
