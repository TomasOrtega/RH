import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DisjointFinsetSupOfSupIndepSup
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FDisjointFinsetSupOfSupIndepSup.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.disjoint_finset_sup_of_supIndep_sup' : ∀ (R V ι : Type) [Ring R] [AddCommGroup V] [Module R V] (F : Finset ι) (G B : ι → Submodule R V), F.SupIndep (fun i => G i ⊔ B i) → (∀ i ∈ F, Disjoint (G i) (B i)) → Disjoint (F.sup G) (F.sup B) := by
  first | exact @GlobalTheory.disjoint_finset_sup_of_supIndep_sup | exact GlobalTheory.disjoint_finset_sup_of_supIndep_sup | (intros; apply GlobalTheory.disjoint_finset_sup_of_supIndep_sup <;> assumption)
