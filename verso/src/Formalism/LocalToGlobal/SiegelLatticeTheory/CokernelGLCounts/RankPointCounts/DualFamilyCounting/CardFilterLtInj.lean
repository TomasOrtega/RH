import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IsGlueDataPre
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsTotPosCongr
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsPrescFamily

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Break down `lt_or_gt_of_ne hne with h | h` into its components or cases. Establish `: (P.filter (· < i)).card < (P.filter (· < k)).card`. Apply `Finset.card_lt_card` to reduce the goal to its premises. Use `⟨fun x hx => ?_, fun hsub => ?_⟩` and prove the remaining obligations.

Simplify using `only [Finset.mem_filter] at hx ⊢`. Conclude with `⟨hx.1, hx.2.trans h⟩`. Use `hsub (Finset.mem_filter.2 ⟨hi, h⟩)` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers.

Establish `: (P.filter (· < k)).card < (P.filter (· < i)).card`. Apply `Finset.card_lt_card` to reduce the goal to its premises. Use `⟨fun x hx => ?_, fun hsub => ?_⟩` and prove the remaining obligations. Simplify using `only [Finset.mem_filter] at hx ⊢`. Conclude with `⟨hx.1, hx.2.trans h⟩`.

Use `hsub (Finset.mem_filter.2 ⟨hk, h⟩)` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers.
-/
theorem card_filter_lt_inj {n : ℕ} (P : Finset (Fin n)) {i k : Fin n} (hi : i ∈ P) (hk : k ∈ P)
    (e : (P.filter (· < i)).card = (P.filter (· < k)).card) : i = k := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have : (P.filter (· < i)).card < (P.filter (· < k)).card := by
      apply Finset.card_lt_card
      refine ⟨fun x hx => ?_, fun hsub => ?_⟩
      · simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.trans h⟩
      · have := hsub (Finset.mem_filter.2 ⟨hi, h⟩)
        simp at this
    omega
  · have : (P.filter (· < k)).card < (P.filter (· < i)).card := by
      apply Finset.card_lt_card
      refine ⟨fun x hx => ?_, fun hsub => ?_⟩
      · simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.trans h⟩
      · have := hsub (Finset.mem_filter.2 ⟨hk, h⟩)
        simp at this
    omega

/- English proof (translation)
The claim follows from `Finset.card_lt_card (Finset.filter_ssubset.2 ⟨i, hi, lt_irrefl i⟩)`.
-/
theorem card_filter_lt_lt {n : ℕ} (P : Finset (Fin n)) {i : Fin n} (hi : i ∈ P) :
    (P.filter (· < i)).card < P.card :=
  Finset.card_lt_card (Finset.filter_ssubset.2 ⟨i, hi, lt_irrefl i⟩)

end Formalism.L2.SG.Pf.GluingBases
