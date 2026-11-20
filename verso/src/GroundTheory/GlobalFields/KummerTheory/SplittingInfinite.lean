import Mathlib
import GroundTheory.GlobalFields.SemilocalAlgebras.Infinite
import GroundTheory.GlobalFields.KummerTheory.Splitting

noncomputable section

namespace GroundTheory.Global

open NumberField Module
open scoped NumberField.LiesOver TensorProduct

namespace InfinitePlace

variable {K : Type*} [Field K] (L : Type*) [Field L] [Algebra K L]

def SplitsCompletely (v : NumberField.InfinitePlace K) : Prop :=
  ∀ w : NumberField.InfinitePlace L, w.LiesOver v → w.IsUnramified K

variable {L} (v : NumberField.InfinitePlace K)

/- English proof (translation)
Use `⟨fun h ↦ h.finrank_eq_one v, fun h ↦ ?_⟩` and prove the remaining obligations. Break down `w.isUnramified_or_isRamified K with hu | hr` into its components or cases. Conclude with `hu`. Conclude with `absurd (h.symm.trans (hr.finrank_eq_two v)) (by norm_num)`.
-/
theorem isUnramified_iff_finrank_eq_one (w : NumberField.InfinitePlace L) [w.LiesOver v] :
    w.IsUnramified K ↔ finrank v.Completion w.Completion = 1 := by
  refine ⟨fun h ↦ h.finrank_eq_one v, fun h ↦ ?_⟩
  rcases w.isUnramified_or_isRamified K with hu | hr
  · exact hu
  · exact absurd (h.symm.trans (hr.finrank_eq_two v)) (by norm_num)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h w ↦ (isUnramified_iff_finrank_eq_one v w.1).1 (h w.1 w.2), fun h w hw ↦ have := hw; (isUnramified_iff_finrank_eq_one v w).2 (h ⟨w, hw⟩)⟩`.
-/
theorem splitsCompletely_iff_forall_finrank :
    SplitsCompletely L v ↔
      ∀ w : v.placesOver L, finrank v.Completion (w : NumberField.InfinitePlace L).Completion = 1 :=
  ⟨fun h w ↦ (isUnramified_iff_finrank_eq_one v w.1).1 (h w.1 w.2),
    fun h w hw ↦ have := hw; (isUnramified_iff_finrank_eq_one v w).2 (h ⟨w, hw⟩)⟩

variable [NumberField K] [NumberField L]

/- English proof (translation)
Rewrite using `[splitsCompletely_iff_forall_finrank, ← isFiniteSplit_pi_iff]`. Conclude with `⟨fun h ↦ .of_algEquiv (tensorPiEquiv (L := L) v).symm, fun h ↦ .of_algEquiv (tensorPiEquiv (L := L) v)⟩`.
-/
theorem splitsCompletely_iff_isFiniteSplit :
    SplitsCompletely L v ↔ Algebra.IsFiniteSplit v.Completion (v.Completion ⊗[K] L) := by
  rw [splitsCompletely_iff_forall_finrank, ← isFiniteSplit_pi_iff]
  exact ⟨fun h ↦ .of_algEquiv (tensorPiEquiv (L := L) v).symm,
    fun h ↦ .of_algEquiv (tensorPiEquiv (L := L) v)⟩

variable (L) in

/- English proof (translation)
Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_nonempty_iff]`. Use `sum_finrank_completion (L := L) v` as an intermediate fact. Rewrite `this` using `[Finset.univ_eq_empty, Finset.sum_empty]`. Conclude with `(Module.finrank_pos (R := K) (M := L)).ne this`.
-/
theorem nonempty_placesOver : Nonempty (v.placesOver L) := by
  classical
  by_contra h
  rw [not_nonempty_iff] at h
  have := sum_finrank_completion (L := L) v
  rw [Finset.univ_eq_empty, Finset.sum_empty] at this
  exact (Module.finrank_pos (R := K) (M := L)).ne this

end InfinitePlace

end GroundTheory.Global
