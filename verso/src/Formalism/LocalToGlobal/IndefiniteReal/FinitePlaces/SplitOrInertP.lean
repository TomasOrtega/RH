import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SplitInt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SbHalfHalfInd

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Polynomial
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.Datum

set_option maxHeartbeats 800000 in
/- English proof (translation)
Introduce `v ε hε`. Distinguish the cases in `h : ∃ e : AE D, IsSplitIdem D e ∧ e * algebraMap (AF D.host.F) (AE D) ε ≠ 0`. Use `left`. Take `⟨e, ⟨h1, h2, w, ε', hpl, hs⟩, hne⟩` from `h`. Rewrite `hs` using `[placeIdem_eq hpl]`.

Express the relevant statement in the definitionally equal form `e + cA D e = phiE w 1 at hs`. Rewrite `hne` using `[placeIdem_eq hε]`. Express the relevant statement in the definitionally equal form `e * phiE v 1 ≠ 0 at hne`. Establish `heps : e * phiE w 1 = e` using `by rw [← hs, mul_add, h1, h2, add_zero]`. Establish `hwv : w = v`.

Assume the negation of the conclusion as `hwv`. Apply `hne` to reduce the goal to its premises. Rewrite using `[← heps, mul_assoc, phiE_orth hwv, mul_zero]`. Substitute `hwv` using the available equality. Take `⟨s, ι, hss, hι⟩` from `split_emb h1 h2 hs`.

Use `⟨plOf ι, ?_, plOf_split ι s hss hι⟩` and prove the remaining obligations. Establish `hle : w.asIdeal ≤ (belowPl (plOf ι)).asIdeal` using `fun f hf => algebraMap_mem_valIdeal ι hf`. Conclude with `(w.isMaximal.eq_of_le (belowPl (plOf ι)).isPrime.ne_top hle).symm`. Use `right`. Introduce `e he`.

Assume the negation of the conclusion as `hne`. Conclude with `h ⟨e, he, hne⟩`.
-/
theorem splitOrInert (D : D7) : LevelGroupLemmas.SplitOrInert D := by
  intro v ε hε
  by_cases h : ∃ e : AE D, IsSplitIdem D e ∧ e * algebraMap (AF D.host.F) (AE D) ε ≠ 0
  · left
    obtain ⟨e, ⟨h1, h2, w, ε', hpl, hs⟩, hne⟩ := h
    rw [placeIdem_eq hpl] at hs
    change e + cA D e = phiE w 1 at hs
    rw [placeIdem_eq hε] at hne
    change e * phiE v 1 ≠ 0 at hne
    have heps : e * phiE w 1 = e := by rw [← hs, mul_add, h1, h2, add_zero]
    have hwv : w = v := by
      by_contra hwv
      apply hne
      rw [← heps, mul_assoc, phiE_orth hwv, mul_zero]
    subst hwv
    obtain ⟨s, ι, hss, hι⟩ := split_emb h1 h2 hs
    refine ⟨plOf ι, ?_, plOf_split ι s hss hι⟩
    have hle : w.asIdeal ≤ (belowPl (plOf ι)).asIdeal := fun f hf => algebraMap_mem_valIdeal ι hf
    exact (w.isMaximal.eq_of_le (belowPl (plOf ι)).isPrime.ne_top hle).symm
  · right
    intro e he
    by_contra hne
    exact h ⟨e, he, hne⟩

end Formalism.IndefR.Fin

end
