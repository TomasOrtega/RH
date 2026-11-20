import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.Interleave

open Zc.Comb

universe u

namespace GlobalTheory.CompanionTheory.Comb

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `nil => exact List.Perm.refl _`. Consider the case `left _ ih => exact ih.cons _`. Consider the case `right _ ih => exact (ih.cons _).trans List.perm_middle.symm`.
-/
theorem interleave_perm_append {T : Type u} {u v w : List T} (h : Interleave u v w) :
    w.Perm (u ++ v) := by
  induction h with
  | nil => exact List.Perm.refl _
  | left _ ih => exact ih.cons _
  | right _ ih => exact (ih.cons _).trans List.perm_middle.symm

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `nil => exact List.Perm.refl _`. Consider the case `cons _ hi ih`. Rewrite using `[List.flatten_cons]`. Conclude with `(interleave_perm_append hi).trans (ih.append_left _)`.
-/
theorem shuffle_perm_flatten {T : Type u} (us : List (List T)) (w : List T)
    (h : Shuffle us w) : w.Perm us.flatten := by
  induction h with
  | nil => exact List.Perm.refl _
  | cons _ hi ih =>
    rw [List.flatten_cons]
    exact (interleave_perm_append hi).trans (ih.append_left _)

end GlobalTheory.CompanionTheory.Comb
