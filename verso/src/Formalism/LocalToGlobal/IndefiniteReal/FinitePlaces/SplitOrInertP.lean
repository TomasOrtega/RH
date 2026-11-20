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
Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Express the relevant assertion in an equivalent form by its definition.

Rewrite the indicated hypotheses using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Substitute using the available equality. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. A detailed English derivation is pending.
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
