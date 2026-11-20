import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsGaloisExtendingAlgHom

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17 in
/- English proof (translation)
Introduce `n A c`. Unfold `Formalism.MainNotions.LocalTheoryWindows.ro Formalism.MainNotions.LocalTheoryWindows.thickLv`. Conclude with `(Finset.card_filter_le _ _).trans (Finset.card_range _).le`.
-/
theorem ro_le_arc_len : ∀ {n : ℕ} (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (c : ZMod n),
    Formalism.MainNotions.LocalTheoryWindows.ro A.ty A.len c ≤ A.len c := by
  intro n A c
  unfold Formalism.MainNotions.LocalTheoryWindows.ro Formalism.MainNotions.LocalTheoryWindows.thickLv
  exact (Finset.card_filter_le _ _).trans (Finset.card_range _).le

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17 in
/- English proof (translation)
Introduce `n _ b w S η up size h c`. Unfold `arcOf`. Simplify using `only`. Use `Nat.sInf_le ?_` and prove the remaining obligations. Rewrite using `[Set.mem_ofPred_eq]`.

Conclude with `⟨le_rfl, fun ht => h ⟨_, ht⟩⟩`.
-/
theorem arc_len_le_one_of_no_thick : ∀ {n : ℕ} [NeZero n] (b w S η : ℕ) (up : ZMod n → Bool) (size : ZMod n → ℕ)
    (h : ¬ ∃ i, Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i) (c : ZMod n),
    (arcOf b w S η up size).len c ≤ 1 := by
  intro n _ b w S η up size h c
  unfold arcOf
  dsimp only
  refine Nat.sInf_le ?_
  rw [Set.mem_ofPred_eq]
  exact ⟨le_rfl, fun ht => h ⟨_, ht⟩⟩

end Formalism.MainNotions.N.Ln17
