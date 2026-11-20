import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonLineBundleCohomologyProjBaseChangeIf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSubsingletonLineBundleCohomologyProjBaseChangeIf.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.subsingleton_lineBundleCohomology_projBaseChange_iff : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → IsProjOver q → ∀ M : LB Y, M.IsLB → ∀ n : ℕ, (Subsingleton (coh (twist (GlobalTheory.structureModule X) (M.pull π)) n) ↔ Subsingleton (coh (twist (GlobalTheory.structureModule Y) M) n)) := by
  first | exact @GlobalTheory.CohFieldChange.subsingleton_coh_pull_iff_of_isProjOver | exact GlobalTheory.CohFieldChange.subsingleton_coh_pull_iff_of_isProjOver | (intros; apply GlobalTheory.CohFieldChange.subsingleton_coh_pull_iff_of_isProjOver <;> assumption)
