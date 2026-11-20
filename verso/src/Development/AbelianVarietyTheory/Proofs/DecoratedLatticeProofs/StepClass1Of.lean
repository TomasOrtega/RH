import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CorankOneIsEquivalenceOnRow
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.One

/- English proof (translation)
Introduce `D X Y u hc νL νB ng`. Take `⟨hR, hS, hT⟩` from `h D X Y u u hc`. Establish `hsub : ∀ t ∈ (Y.tO u u).genSet, t ∈ (Y.tO u u).nzSet` using `fun t ht => ht.1`. Introduce `t ht t' ht'`. Rewrite `ht`, `ht'` using `[genT_ngSet]`.

Express the relevant statement in the definitionally equal form `t ∈ (Y.tO u u).genSet at ht`. Express the relevant statement in the definitionally equal form `t' ∈ (Y.tO u u).genSet at ht'`. Establish `es : (genT (scT (Y.tO u u))).s0 t t' = 1 ↔ (Y.tO u u).s0 t t' = 1`. Simplify using `only [genT, scT, and_true]`. Distinguish the cases in `hc : (Y.tO u u).s0 t t' = 1`.

Simplify using `[hc]`. Simplify using `[hc]`. Use `show ((scT (Y.tO u u)).rowOf t = (scT (Y.tO u u)).rowOf t' ∧ (genT (scT (Y.tO u u))).s0 t t' = 1) ↔ cls1 Y u t = cls1 Y u t'`. Rewrite using `[es]`. Express the relevant statement in the definitionally equal form `((Y.tO u u).rowOf t = (Y.tO u u).rowOf t' ∧ (Y.tO u u).s0 t t' = 1) ↔ cls1 Y u t = cls1 Y u t'`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hr, h1⟩`. Establish `b1` using `hS t (hsub t ht) t' (hsub t' ht') hr h1`. Use extensionality with `x`. Simplify using `only [cls1, Set.mem_setOf_eq]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hx, hrx, hx1⟩`. Conclude with `⟨hx, hrx.trans hr, hT t' (hsub t' ht') t (hsub t ht) x (hsub x hx) hr.symm hrx.symm b1 hx1⟩`. Introduce and unpack `⟨hx, hrx, hx1⟩`. Conclude with `⟨hx, hrx.trans hr.symm, hT t (hsub t ht) t' (hsub t' ht') x (hsub x hx) hr hrx.symm h1 hx1⟩`.

Introduce `hc`. Establish `hm : t' ∈ cls1 Y u t'` using `⟨ht', rfl, hR t' (hsub t' ht')⟩`. Rewrite `hm` using `[← hc]`. Conclude with `⟨hm.2.1.symm, hm.2.2⟩`.
-/
theorem stepClass1_of (h : CorankOneIsEquivalenceOnRow) : StepClass1 := by
  intro D X Y u hc νL νB ng
  obtain ⟨hR, hS, hT⟩ := h D X Y u u hc
  have hsub : ∀ t ∈ (Y.tO u u).genSet, t ∈ (Y.tO u u).nzSet := fun t ht => ht.1
  intro t ht t' ht'
  rw [genT_ngSet] at ht ht'
  change t ∈ (Y.tO u u).genSet at ht
  change t' ∈ (Y.tO u u).genSet at ht'
  have es : (genT (scT (Y.tO u u))).s0 t t' = 1 ↔ (Y.tO u u).s0 t t' = 1 := by
    simp only [genT, scT, and_true]
    by_cases hc : (Y.tO u u).s0 t t' = 1
    · simp [hc]
    · simp [hc]
  show ((scT (Y.tO u u)).rowOf t = (scT (Y.tO u u)).rowOf t' ∧ (genT (scT (Y.tO u u))).s0 t t' = 1) ↔
    cls1 Y u t = cls1 Y u t'
  rw [es]
  change ((Y.tO u u).rowOf t = (Y.tO u u).rowOf t' ∧ (Y.tO u u).s0 t t' = 1) ↔ cls1 Y u t = cls1 Y u t'
  constructor
  · rintro ⟨hr, h1⟩
    have b1 := hS t (hsub t ht) t' (hsub t' ht') hr h1
    ext x
    simp only [cls1, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hx, hrx, hx1⟩
      exact ⟨hx, hrx.trans hr, hT t' (hsub t' ht') t (hsub t ht) x (hsub x hx) hr.symm hrx.symm b1 hx1⟩
    · rintro ⟨hx, hrx, hx1⟩
      exact ⟨hx, hrx.trans hr.symm, hT t (hsub t ht) t' (hsub t' ht') x (hsub x hx) hr hrx.symm h1 hx1⟩
  · intro hc
    have hm : t' ∈ cls1 Y u t' := ⟨ht', rfl, hR t' (hsub t' ht')⟩
    rw [← hc] at hm
    exact ⟨hm.2.1.symm, hm.2.2⟩

end GlobalTheory.Core.One
