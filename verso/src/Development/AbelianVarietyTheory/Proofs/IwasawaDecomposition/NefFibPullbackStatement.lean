import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FNefFibPullback.lean&line=132#L132)
-/
theorem _root_.GlobalTheory.T.nefFib_pullback : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p), ArInt.NefFib L → ArInt.NefFib (L.pull π hπ) := by
  first | exact @GlobalTheory.ArInt.nefFib_pull | exact GlobalTheory.ArInt.nefFib_pull | (intros; apply GlobalTheory.ArInt.nefFib_pull <;> assumption)
