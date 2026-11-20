import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeExtensionCompleteToDvr
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.AbDatum GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.ConjSeq GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt
open GlobalTheory.Cris (dp0)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLatticeExtensionCompleteToDvr.lean&line=368#L368)
-/
theorem _root_.GlobalTheory.T.lattice_extension_complete_to_dvr : ∀ (X T : Scheme.{0}) (f₀ : T ⟶ X) (O : Type) [CommRing O] (A B A' B' : X.Modules) (α : O →+* End A) (β : O →+* End B) (α' : O →+* End A') (β' : O →+* End B') (r a b a' b' : ℕ), IsVB A a → IsVB B b → IsVB A' a' → IsVB B' b' → ∀ d₀ : DatumOn α β α' β' r f₀, HasLatticesComplete d₀ → HasLatticesDvr d₀ := by
  first | exact @GlobalTheory.BadPt.Descent.hasLatticesDvr_of_complete | exact GlobalTheory.BadPt.Descent.hasLatticesDvr_of_complete | (intros; apply GlobalTheory.BadPt.Descent.hasLatticesDvr_of_complete <;> assumption)
