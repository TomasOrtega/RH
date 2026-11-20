import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LbIsoOfDisjointCover
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsLineBundleExtension
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FLbIsoOfDisjointCover.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.lbIso_of_lbIso_on_disjoint_cover : ∀ (Y : Scheme.{0}) (A : Type) (W : A → Y.Opens), (∀ a b y, y ∈ W a → y ∈ W b → a = b) → (∀ y, ∃ a, y ∈ W a) → ∀ (P Q : LB Y), P.IsLB → Q.IsLB → (∀ a, LBIso (P.pull (W a).ι) (Q.pull (W a).ι)) → LBIso P Q := by
  first | exact @GlobalTheory.DisjointCoverLB.lbIso_of_disjoint_cover | exact GlobalTheory.DisjointCoverLB.lbIso_of_disjoint_cover | (intros; apply GlobalTheory.DisjointCoverLB.lbIso_of_disjoint_cover <;> assumption)
