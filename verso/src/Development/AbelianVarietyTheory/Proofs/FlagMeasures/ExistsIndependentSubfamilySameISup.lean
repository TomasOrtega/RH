import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelOfIsCuspOf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecompositionStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

/- English proof (translation)
Introduce `ι M _ _ N h F`. Use `Finset.induction_on F ?_ ?_` and prove the remaining obligations. Conclude with `⟨∅, Finset.Subset.refl _, rfl, by simp⟩`. Introduce `i F hi ih`. Take `⟨J, hJF, hJsup, huniq⟩` from `ih`.

Establish `hiJ : i ∉ J` using `fun hh => hi (hJF hh)`. Break down `h i J with hd | hle` into its components or cases. Use `⟨insert i J, Finset.insert_subset_insert _ hJF, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.iSup_insert, Finset.iSup_insert, hJsup]`. Introduce `f f' hf hf' hsum`.

Rewrite `hsum` using `[Finset.sum_insert hiJ, Finset.sum_insert hiJ]`. Establish `hdiff : f i - f' i = ∑ j ∈ J, f' j - ∑ j ∈ J, f j`. Rewrite using `[sub_eq_sub_iff_add_eq_add, hsum, add_comm]`. Establish `hmem : f i - f' i ∈ N i ⊓ ⨆ j ∈ J, N j`. Use `⟨Submodule.sub_mem _ (hf i (Finset.mem_insert_self _ _)) (hf' i (Finset.mem_insert_self _ _)), ?_⟩` and prove the remaining obligations.

Rewrite using `[hdiff]`. Conclude with `Submodule.sub_mem _ (Submodule.sum_mem_biSup fun j hj => hf' j (Finset.mem_insert_of_mem hj)) (Submodule.sum_mem_biSup fun j hj => hf j (Finset.mem_insert_of_mem hj))`. Rewrite `hmem` using `[hd.eq_bot, Submodule.mem_bot, sub_eq_zero]`. Rewrite `hsum` using `[hmem]`. Establish `hJs : ∑ j ∈ J, f j = ∑ j ∈ J, f' j` using `add_left_cancel hsum`.

Introduce `j hj`. Break down `Finset.mem_insert.mp hj with rfl | hj` into its components or cases. Conclude with `hmem`. Conclude with `huniq f f' (fun k hk => hf k (Finset.mem_insert_of_mem hk)) (fun k hk => hf' k (Finset.mem_insert_of_mem hk)) hJs j hj`. Use `⟨J, hJF.trans (Finset.subset_insert _ _), ?_, huniq⟩` and prove the remaining obligations.

Rewrite using `[Finset.iSup_insert, ← hJsup]`. Conclude with `(sup_eq_right.mpr hle).symm`.
-/
theorem indep_subfamily_of_disjoint_or_le : ∀ (ι M : Type) [AddCommGroup M] [Module ℂ M] (N : ι → Submodule ℂ M), (∀ i (J : Finset ι), Disjoint (N i) (⨆ j ∈ J, N j) ∨ N i ≤ ⨆ j ∈ J, N j) → ∀ F : Finset ι, ∃ J ⊆ F, (⨆ j ∈ J, N j) = (⨆ j ∈ F, N j) ∧ ∀ f f' : ι → M, (∀ j ∈ J, f j ∈ N j) → (∀ j ∈ J, f' j ∈ N j) → ∑ j ∈ J, f j = ∑ j ∈ J, f' j → ∀ j ∈ J, f j = f' j := by
  intro ι M _ _ N h F
  classical
  refine Finset.induction_on F ?_ ?_
  · exact ⟨∅, Finset.Subset.refl _, rfl, by simp⟩
  · intro i F hi ih
    obtain ⟨J, hJF, hJsup, huniq⟩ := ih
    have hiJ : i ∉ J := fun hh => hi (hJF hh)
    rcases h i J with hd | hle
    · refine ⟨insert i J, Finset.insert_subset_insert _ hJF, ?_, ?_⟩
      · rw [Finset.iSup_insert, Finset.iSup_insert, hJsup]
      · intro f f' hf hf' hsum
        rw [Finset.sum_insert hiJ, Finset.sum_insert hiJ] at hsum
        have hdiff : f i - f' i = ∑ j ∈ J, f' j - ∑ j ∈ J, f j := by
          rw [sub_eq_sub_iff_add_eq_add, hsum, add_comm]
        have hmem : f i - f' i ∈ N i ⊓ ⨆ j ∈ J, N j := by
          refine ⟨Submodule.sub_mem _ (hf i (Finset.mem_insert_self _ _))
            (hf' i (Finset.mem_insert_self _ _)), ?_⟩
          rw [hdiff]
          exact Submodule.sub_mem _
            (Submodule.sum_mem_biSup fun j hj => hf' j (Finset.mem_insert_of_mem hj))
            (Submodule.sum_mem_biSup fun j hj => hf j (Finset.mem_insert_of_mem hj))
        rw [hd.eq_bot, Submodule.mem_bot, sub_eq_zero] at hmem
        rw [hmem] at hsum
        have hJs : ∑ j ∈ J, f j = ∑ j ∈ J, f' j := add_left_cancel hsum
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hmem
        · exact huniq f f' (fun k hk => hf k (Finset.mem_insert_of_mem hk))
            (fun k hk => hf' k (Finset.mem_insert_of_mem hk)) hJs j hj
    · refine ⟨J, hJF.trans (Finset.subset_insert _ _), ?_, huniq⟩
      rw [Finset.iSup_insert, ← hJsup]
      exact (sup_eq_right.mpr hle).symm

end GlobalTheory
