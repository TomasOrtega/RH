import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefHermitianBundlePullback
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VertForm
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNefHermitianBundlePullback.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.nef_hermitian_bundle_pullback : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p) (l : ℕ), l.Prime → NefOver L l → NefOver (L.pull π hπ) l := by
  first | exact @GlobalTheory.VertForm.nefOver_pull | exact GlobalTheory.VertForm.nefOver_pull | (intros; apply GlobalTheory.VertForm.nefOver_pull <;> assumption)
