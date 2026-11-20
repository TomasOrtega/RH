import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CorankOneIsEquivalenceOnRow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CorankOneOfSameFlagDoubleCoset
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.One

/- English proof (translation)
Introduce `hE D X Y u hT`. Take `⟨hrefl0, hsym, htr⟩` from `hE D X Y u u hT`. Establish `hnz : ∀ t : TauC Y u u, t ∈ (Y.tO u u).genSet → t ∈ (Y.tO u u).nzSet` using `fun t ht => ht.1`. Establish `hG : ∀ t : TauC Y u u, t ∈ (Y.tO u u).genSet → t.G ≠ 0`. Introduce `t ht h0`.

Establish `h1 : (Y.tO u u).G t ≠ 0` using `ht.1`. Apply `h1` to reduce the goal to its premises. Use `show Gt t = 0`. Simplify using `[Gt, h0]`. Establish `hrefl : ∀ t : TauC Y u u, t ∈ (Y.tO u u).genSet → t ∈ cls1 Y u t` using `fun t ht => ⟨ht, rfl, hrefl0 t (hnz t ht)⟩`.

Establish `hrow : ∀ t t' : TauC Y u u, t' ∈ cls1 Y u t → (Y.tO u u).rowOf t' = (Y.tO u u).rowOf t` using `fun t t' h => h.2.1`. Establish `hsub : ∀ t ∈ (Y.tO u u).genSet, ∀ t' ∈ (Y.tO u u).genSet, (Y.tO u u).rowOf t = (Y.tO u u).rowOf t' → (Y.tO u u).s0 t t' = 1 → cls1 Y u t' ⊆ cls1 Y u t`. Introduce `t ht t' ht' hr hs x hx`. Take `⟨hxg, hxr, hxs⟩` from `hx`. Conclude with `⟨hxg, hxr.trans hr.symm, htr t (hnz t ht) t' (hnz t' ht') x (hnz x hxg) hr hxr.symm hs hxs⟩`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `t`. Simplify using `[setQ, Formalism.FourierDecayAlt.PB.Terms.genSet]`. Introduce `t ht t' ht' hn`. Prove the components needed by the constructor for the conclusion.

Introduce `he`. Establish `: t' ∈ cls1 Y u t` using `he ▸ hrefl t' ht'`. Conclude with `(hrow t t' this).symm`. Introduce `hr`. Establish `hs` using `GlobalTheory.Core.OneCoset.corankOne_of_same_flagDoubleCoset D X Y u u t t' (hG t ht) hr hn`.

Establish `hs'` using `hsym t (hnz t ht) t' (hnz t' ht') hr hs`. Conclude with `Set.Subset.antisymm (hsub t' ht' t ht hr.symm hs') (hsub t ht t' ht' hr hs)`. Introduce `t ht t' ht' he`. Establish `: t' ∈ cls1 Y u t` using `he ▸ hrefl t' ht'`. Conclude with `(hrow t t' this).symm`.
-/
theorem famGen1 : CorankOneIsEquivalenceOnRow → FamGen1 := by
  intro hE D X Y u hT
  obtain ⟨hrefl0, hsym, htr⟩ := hE D X Y u u hT
  have hnz : ∀ t : TauC Y u u, t ∈ (Y.tO u u).genSet → t ∈ (Y.tO u u).nzSet := fun t ht => ht.1
  have hG : ∀ t : TauC Y u u, t ∈ (Y.tO u u).genSet → t.G ≠ 0 := by
    intro t ht h0
    have h1 : (Y.tO u u).G t ≠ 0 := ht.1
    apply h1
    show Gt t = 0
    simp [Gt, h0]
  have hrefl : ∀ t : TauC Y u u, t ∈ (Y.tO u u).genSet → t ∈ cls1 Y u t :=
    fun t ht => ⟨ht, rfl, hrefl0 t (hnz t ht)⟩
  have hrow : ∀ t t' : TauC Y u u, t' ∈ cls1 Y u t → (Y.tO u u).rowOf t' = (Y.tO u u).rowOf t :=
    fun t t' h => h.2.1
  have hsub : ∀ t ∈ (Y.tO u u).genSet, ∀ t' ∈ (Y.tO u u).genSet,
      (Y.tO u u).rowOf t = (Y.tO u u).rowOf t' → (Y.tO u u).s0 t t' = 1 →
      cls1 Y u t' ⊆ cls1 Y u t := by
    intro t ht t' ht' hr hs x hx
    obtain ⟨hxg, hxr, hxs⟩ := hx
    exact ⟨hxg, hxr.trans hr.symm, htr t (hnz t ht) t' (hnz t' ht') x (hnz x hxg) hr hxr.symm hs hxs⟩
  refine ⟨?_, ?_, ?_⟩
  · ext t
    simp [setQ, Formalism.FourierDecayAlt.PB.Terms.genSet]
  · intro t ht t' ht' hn
    constructor
    · intro he
      have : t' ∈ cls1 Y u t := he ▸ hrefl t' ht'
      exact (hrow t t' this).symm
    · intro hr
      have hs := GlobalTheory.Core.OneCoset.corankOne_of_same_flagDoubleCoset D X Y u u t t' (hG t ht) hr hn
      have hs' := hsym t (hnz t ht) t' (hnz t' ht') hr hs
      exact Set.Subset.antisymm (hsub t' ht' t ht hr.symm hs') (hsub t ht t' ht' hr hs)
  · intro t ht t' ht' he
    have : t' ∈ cls1 Y u t := he ▸ hrefl t' ht'
    exact (hrow t t' this).symm

/- English proof (translation)
The claim follows from `famGen1`.
-/
example : CorankOneIsEquivalenceOnRow → FamGen1 := famGen1

end GlobalTheory.Core.One
