import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsAdjoinTrdegAdd
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open Algebra Cardinal Set

noncomputable section

/- English proof (translation)
Use `(algebraMap R L).domain_nontrivial` as an intermediate fact. Set `v : κ → adjoin R u` to `fun i => ⟨w i, subset_adjoin (hwu ⟨i, rfl⟩)⟩`. Establish `hv : AlgebraicIndependent R v` using `AlgebraicIndependent.of_comp (adjoin R u).val hw`. Establish `heq : (adjoin R (range v)).map (adjoin R u).val = adjoin R (range w)`. Rewrite using `[AlgHom.map_adjoin, ← range_comp]`.

Both sides reduce to the same expression. Set `e` to `((adjoin R (range v)).equivMapOfInjective (adjoin R u).val Subtype.val_injective).trans (Subalgebra.equivOfEq _ _ heq)`. Establish `hval : Algebra.IsAlgebraic (adjoin R (range v)) (adjoin R u)`. Use `⟨fun a => ?_⟩` and prove the remaining obligations. Establish `h0 : IsAlgebraic (adjoin R u) (a : L)` using `isAlgebraic_algebraMap a`.

Establish `h1 : IsAlgebraic (adjoin R (range w)) ((adjoin R u).val a)` using `h0.adjoin_of_forall_isAlgebraic fun y hy => halg y hy.1`. Conclude with `(isAlgebraic_ringHom_iff_of_comp_eq e (adjoin R u).val Subtype.val_injective (by ext; rfl)).mp h1`. Conclude with `((isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic.mpr ⟨hv, hval⟩).cardinalMk_eq_trdeg).symm`.
-/
theorem AdjoinTrdegAdd.trdeg_adjoin_eq_of_family {R L κ : Type} [CommRing R] [CommRing L] [IsDomain L]
    [Algebra R L] (u : Set L) (w : κ → L) (hwu : range w ⊆ u) (hw : AlgebraicIndependent R w)
    (halg : ∀ a ∈ u, IsAlgebraic (adjoin R (range w)) a) :
    trdeg R (adjoin R u) = #κ := by
  have := (algebraMap R L).domain_nontrivial
  let v : κ → adjoin R u := fun i => ⟨w i, subset_adjoin (hwu ⟨i, rfl⟩)⟩
  have hv : AlgebraicIndependent R v := AlgebraicIndependent.of_comp (adjoin R u).val hw
  have heq : (adjoin R (range v)).map (adjoin R u).val = adjoin R (range w) := by
    rw [AlgHom.map_adjoin, ← range_comp]
    rfl
  let e := ((adjoin R (range v)).equivMapOfInjective (adjoin R u).val Subtype.val_injective).trans
    (Subalgebra.equivOfEq _ _ heq)
  have hval : Algebra.IsAlgebraic (adjoin R (range v)) (adjoin R u) := by
    refine ⟨fun a => ?_⟩
    have h0 : IsAlgebraic (adjoin R u) (a : L) := isAlgebraic_algebraMap a
    have h1 : IsAlgebraic (adjoin R (range w)) ((adjoin R u).val a) :=
      h0.adjoin_of_forall_isAlgebraic fun y hy => halg y hy.1
    exact (isAlgebraic_ringHom_iff_of_comp_eq e (adjoin R u).val Subtype.val_injective
      (by ext; rfl)).mp h1
  exact ((isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic.mpr
    ⟨hv, hval⟩).cardinalMk_eq_trdeg).symm

/- English proof (translation)
Introduce `R _ L _ _ _ hinj s t ι _ x hxt hx hxalg`. Establish `: FaithfulSMul R L` using `(faithfulSMul_iff_algebraMap_injective R L).mpr hinj`. Take `⟨b, hb⟩` from `(AlgebraicIndependent.matroid R L).exists_isBasis s (by simp)`. Take `⟨hbi, hbs, hbalg⟩` from `AlgebraicIndependent.matroid_isBasis_iff.mp hb`. Establish `hbi' : AlgebraicIndependent R ((↑) : b → L)` using `hbi`.

Establish `h1 : trdeg R (adjoin R s) = #b` using `AdjoinTrdegAdd.trdeg_adjoin_eq_of_family s ((↑) : b → L) (by rw [Subtype.range_coe]; exact hbs) hbi' (by rw [Subtype.range_coe]; exact hbalg)`. Set `_ : Algebra (adjoin R b) (adjoin R s)` to `(Subalgebra.inclusion (adjoin_mono hbs)).toAlgebra`. Establish `: IsScalarTower (adjoin R b) (adjoin R s) L` using `.of_algebraMap_eq fun _ => rfl`. Establish `hxb : AlgebraicIndependent (adjoin R (range ((↑) : b → L))) x`. Rewrite using `[Subtype.range_coe]`.

Conclude with `hx.restrictScalars (Subalgebra.inclusion_injective _)`. Establish `hsum : AlgebraicIndependent R (Sum.elim x ((↑) : b → L))` using `AlgebraicIndependent.sumElim_iff.mpr ⟨hbi', hxb⟩`. Establish `hrange : range (Sum.elim x ((↑) : b → L)) = range x ∪ b`. Rewrite using `[Set.Sum.elim_range, Subtype.range_coe]`. Establish `hs : ∀ a ∈ s, IsAlgebraic (adjoin R (range x ∪ b)) a` using `fun a ha => (hbalg a ha).adjoin_of_forall_isAlgebraic fun y hy => (hy.2 (Or.inr hy.1)).elim`.

Establish `hst : ∀ a ∈ s ∪ t, IsAlgebraic (adjoin R (range (Sum.elim x ((↑) : b → L)))) a`. Rewrite using `[hrange]`. Introduce and unpack `a (ha | ha)`. Conclude with `hs a ha`. Use `(hxalg a ha).adjoin_of_forall_isAlgebraic fun y hy => ?_` and prove the remaining obligations.

Break down `hy.1 with hy1 | hy1` into its components or cases. Conclude with `hs y hy1`. Conclude with `(hy.2 (Or.inl hy1)).elim`. Establish `h2 : trdeg R (adjoin R (s ∪ t)) = #(ι ⊕ b)` using `AdjoinTrdegAdd.trdeg_adjoin_eq_of_family (s ∪ t) (Sum.elim x ((↑) : b → L)) (by rw [hrange]; exact union_subset (hxt.trans subset_union_right) (hbs.trans subset_union_left)) hsum hst`. Rewrite using `[h2, h1, mk_sum, lift_id, lift_id, mk_fintype, add_comm]`.
-/
theorem AdjoinTrdegAdd.proof : AdjoinTrdegAdd.Statement := by
  intro R _ L _ _ _ hinj s t ι _ x hxt hx hxalg
  have : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).mpr hinj
  obtain ⟨b, hb⟩ := (AlgebraicIndependent.matroid R L).exists_isBasis s (by simp)
  obtain ⟨hbi, hbs, hbalg⟩ := AlgebraicIndependent.matroid_isBasis_iff.mp hb
  have hbi' : AlgebraicIndependent R ((↑) : b → L) := hbi

  have h1 : trdeg R (adjoin R s) = #b :=
    AdjoinTrdegAdd.trdeg_adjoin_eq_of_family s ((↑) : b → L) (by rw [Subtype.range_coe]; exact hbs) hbi'
      (by rw [Subtype.range_coe]; exact hbalg)

  let _ : Algebra (adjoin R b) (adjoin R s) := (Subalgebra.inclusion (adjoin_mono hbs)).toAlgebra
  have : IsScalarTower (adjoin R b) (adjoin R s) L := .of_algebraMap_eq fun _ => rfl
  have hxb : AlgebraicIndependent (adjoin R (range ((↑) : b → L))) x := by
    rw [Subtype.range_coe]
    exact hx.restrictScalars (Subalgebra.inclusion_injective _)
  have hsum : AlgebraicIndependent R (Sum.elim x ((↑) : b → L)) :=
    AlgebraicIndependent.sumElim_iff.mpr ⟨hbi', hxb⟩
  have hrange : range (Sum.elim x ((↑) : b → L)) = range x ∪ b := by
    rw [Set.Sum.elim_range, Subtype.range_coe]

  have hs : ∀ a ∈ s, IsAlgebraic (adjoin R (range x ∪ b)) a := fun a ha =>
    (hbalg a ha).adjoin_of_forall_isAlgebraic fun y hy => (hy.2 (Or.inr hy.1)).elim
  have hst : ∀ a ∈ s ∪ t, IsAlgebraic (adjoin R (range (Sum.elim x ((↑) : b → L)))) a := by
    rw [hrange]
    rintro a (ha | ha)
    · exact hs a ha
    · refine (hxalg a ha).adjoin_of_forall_isAlgebraic fun y hy => ?_
      rcases hy.1 with hy1 | hy1
      · exact hs y hy1
      · exact (hy.2 (Or.inl hy1)).elim
  have h2 : trdeg R (adjoin R (s ∪ t)) = #(ι ⊕ b) :=
    AdjoinTrdegAdd.trdeg_adjoin_eq_of_family (s ∪ t) (Sum.elim x ((↑) : b → L))
      (by rw [hrange]; exact union_subset (hxt.trans subset_union_right) (hbs.trans subset_union_left))
      hsum hst
  rw [h2, h1, mk_sum, lift_id, lift_id, mk_fintype, add_comm]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
