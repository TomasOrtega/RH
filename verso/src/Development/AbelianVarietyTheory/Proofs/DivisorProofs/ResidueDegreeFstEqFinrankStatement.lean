import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeFstEqFinrank
import Mathlib
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FieldTensorDegree.residueDegree_fst_eq_finrank` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FResidueDegreeFstEqFinrank.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.residue_degree_fst_eq_finrank : ∀ {X Y S : Scheme.{0}} (f : X ⟶ S) (g : Y ⟶ S) (t : ↑(Limits.pullback f g)), IsField (Scheme.Pullback.Triplet.ofPoint t).tensor → (Limits.pullback.fst f g).residueDegree t = @Module.finrank (X.residueField (Scheme.Pullback.Triplet.ofPoint t).x) (Scheme.Pullback.Triplet.ofPoint t).tensor _ _ (Scheme.Pullback.Triplet.ofPoint t).tensorInl.hom.toModule := by
  first | exact @GlobalTheory.FieldTensorDegree.residueDegree_fst_eq_finrank | exact GlobalTheory.FieldTensorDegree.residueDegree_fst_eq_finrank | (intros; apply GlobalTheory.FieldTensorDegree.residueDegree_fst_eq_finrank <;> assumption)
