import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCompOpenImmersionOfQuasiFinite
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsFiniteCompOpenImmersionOfQuasiFinite.lean&line=136#L136)
-/
theorem _root_.GlobalTheory.T.exists_finite_comp_openImmersion_of_quasiFinite : ∀ (U X : Scheme.{0}) (f : U ⟶ X), IsNoetherian X → IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → LocallyQuasiFinite f → ∃ (T : Scheme.{0}) (q : T ⟶ X) (j : U ⟶ T), IsFinite q ∧ IsOpenImmersion j ∧ j ≫ q = f := by
  first | exact @GlobalTheory.ZMTFin.exists_finite_openImmersion | exact GlobalTheory.ZMTFin.exists_finite_openImmersion | (intros; apply GlobalTheory.ZMTFin.exists_finite_openImmersion <;> assumption)
