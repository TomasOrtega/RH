import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryInfinitePointEqListProdPlaceParts
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DefU.infU_eq_list_prod_embU` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FDefiniteUnitaryInfinitePointEqListProdPlaceParts.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.definiteUnitaryInfinitePoint_eq_list_prod_placeParts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (x : UA E n), x ∈ infU E n → ∃ y : InfinitePlace E → UA E n, (∀ v, y v ∈ embU n v.embedding) ∧ (∀ v, cEmb v.embedding (y v) = cEmb v.embedding x) ∧ (Finset.univ.toList.map y).prod = x := by
  first | exact @GlobalTheory.DefU.infU_eq_list_prod_embU | exact GlobalTheory.DefU.infU_eq_list_prod_embU | (intros; apply GlobalTheory.DefU.infU_eq_list_prod_embU <;> assumption)
