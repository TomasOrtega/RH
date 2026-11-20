import Mathlib

namespace GroundTheory.LocalField

section Completion

variable (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

def openFiniteIndex : Set (Subgroup G) :=
  {H | IsOpen (H : Set G) ∧ H.FiniteIndex}

variable {G} in

def quotientMapOfLE {H H' : Subgroup G} (h : H ≤ H') : G ⧸ H →* G ⧸ H' :=
  QuotientGroup.map H H' (MonoidHom.id G) h

omit [TopologicalSpace G] [IsTopologicalGroup G] in
variable {G} in
@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem quotientMapOfLE_mk {H H' : Subgroup G} (h : H ≤ H') (x : G) :
    quotientMapOfLE h (x : G ⧸ H) = (x : G ⧸ H') :=
  rfl

def openCompletion : Subgroup (∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G)) where
  carrier := {a | ∀ (H H' : openFiniteIndex G) (h : (H : Subgroup G) ≤ H'), quotientMapOfLE h (a H) = a H'}
  one_mem' := fun H H' h => by simp
  mul_mem' := fun ha hb H H' h => by simp [map_mul, ha H H' h, hb H H' h]
  inv_mem' := fun ha H H' h => by simp [map_inv, ha H H' h]

namespace openCompletion

variable {G}

omit [IsTopologicalGroup G] in
/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_iff {a : ∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G)} :
    a ∈ openCompletion G ↔
      ∀ (H H' : openFiniteIndex G) (h : (H : Subgroup G) ≤ H'), quotientMapOfLE h (a H) = a H' :=
  Iff.rfl

omit [IsTopologicalGroup G] in
/- English proof (translation)
The claim follows from `a.2 H H' h`.
-/
theorem apply_eq (a : openCompletion G) {H H' : openFiniteIndex G} (h : (H : Subgroup G) ≤ H') :
    quotientMapOfLE h ((a : ∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G)) H) =
      (a : ∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G)) H' :=
  a.2 H H' h

omit [IsTopologicalGroup G] in

/- English proof (translation)
The claim follows from `Subtype.ext (funext h)`.
-/
theorem ext {a b : openCompletion G}
    (h : ∀ H : openFiniteIndex G, (a : ∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G)) H =
      (b : ∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G)) H) : a = b :=
  Subtype.ext (funext h)

variable (G) in

def of : G →* openCompletion G :=
  MonoidHom.codRestrict (MonoidHom.pi fun H : openFiniteIndex G => QuotientGroup.mk' (H : Subgroup G))
    (openCompletion G) fun _ _ _ _ => rfl

omit [IsTopologicalGroup G] in
@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem of_apply (x : G) (H : openFiniteIndex G) :
    ((of G x : openCompletion G) : ∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G)) H =
      (x : G ⧸ (H : Subgroup G)) :=
  rfl

/- English proof (translation)
The claim follows from `QuotientGroup.discreteTopology H.2.1`.
-/
theorem discreteTopology_quotient (H : openFiniteIndex G) : DiscreteTopology (G ⧸ (H : Subgroup G)) :=
  QuotientGroup.discreteTopology H.2.1

/- English proof (translation)
Establish `hset : (openCompletion G : Set (∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G))) = ⋂ (H : openFiniteIndex G) (H' : openFiniteIndex G) (h : (H : Subgroup G) ≤ H'), {a | quotientMapOfLE h (a H) = a H'}`. Use extensionality with `a`. Simplify using `only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe]`. Both sides reduce to the same expression. Rewrite using `[hset]`.

Use `isClosed_iInter fun H => isClosed_iInter fun H' => isClosed_iInter fun h => ?_` and prove the remaining obligations. Use `discreteTopology_quotient H` as an intermediate fact. Use `discreteTopology_quotient H'` as an intermediate fact. Conclude with `isClosed_eq ((continuous_of_discreteTopology (f := quotientMapOfLE h)).comp (continuous_apply H)) (continuous_apply H')`.
-/
theorem isClosed : IsClosed (openCompletion G : Set (∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G))) := by
  have hset : (openCompletion G : Set (∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G))) =
      ⋂ (H : openFiniteIndex G) (H' : openFiniteIndex G) (h : (H : Subgroup G) ≤ H'),
        {a | quotientMapOfLE h (a H) = a H'} := by
    ext a
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe]
    rfl
  rw [hset]
  refine isClosed_iInter fun H => isClosed_iInter fun H' => isClosed_iInter fun h => ?_
  have := discreteTopology_quotient H
  have := discreteTopology_quotient H'
  exact isClosed_eq ((continuous_of_discreteTopology (f := quotientMapOfLE h)).comp (continuous_apply H))
    (continuous_apply H')

instance : IsTopologicalGroup (openCompletion G) := inferInstance

instance : CompactSpace (openCompletion G) := by
  have : ∀ H : openFiniteIndex G, CompactSpace (G ⧸ (H : Subgroup G)) := fun H => by
    have := H.2.2
    infer_instance
  exact isCompact_iff_compactSpace.1 isClosed.isCompact

instance : T2Space (openCompletion G) := by
  have : ∀ H : openFiniteIndex G, T2Space (G ⧸ (H : Subgroup G)) := fun H => by
    have := discreteTopology_quotient H
    infer_instance
  infer_instance

/- English proof (translation)
Rewrite using `[denseRange_iff_closure_range, Set.eq_univ_iff_forall]`. Introduce `a`. Rewrite using `[mem_closure_iff]`. Introduce `U hU haU`. Take `⟨V, hV, rfl⟩` from `isOpen_induced_iff.1 hU`.

Take `⟨I, u, hu, hIV⟩` from `isOpen_pi_iff.1 hV _ haU`. Set `H₀ : Subgroup G` to `⨅ H ∈ I, (H : Subgroup G)`. Establish `hH₀ : H₀ ∈ openFiniteIndex G`. Use `⟨?_, Subgroup.finiteIndex_iInf' _ fun H _ => H.2.2⟩` and prove the remaining obligations. Establish `: (H₀ : Set G) = ⋂ H ∈ I, ((H : Subgroup G) : Set G)`.

Simplify using `[H₀, Subgroup.coe_iInf]`. Rewrite using `[this]`. Conclude with `isOpen_biInter_finset fun H _ => H.2.1`. Take `⟨x, hx⟩` from `QuotientGroup.mk_surjective ((a : ∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G)) ⟨H₀, hH₀⟩)`. Use `⟨of G x, hIV fun H hH => ?_, x, rfl⟩` and prove the remaining obligations.

Establish `hle : H₀ ≤ (H : Subgroup G)` using `iInf₂_le H hH`. Use `apply_eq a (H := ⟨H₀, hH₀⟩) (H' := H) hle` as an intermediate fact. Rewrite `this` using `[← hx, quotientMapOfLE_mk]`. Express the relevant statement in the definitionally equal form `(x : G ⧸ (H : Subgroup G)) ∈ u H`. Rewrite using `[this]`.

Conclude with `(hu H hH).2`.
-/
theorem denseRange_of : DenseRange (of G) := by
  rw [denseRange_iff_closure_range, Set.eq_univ_iff_forall]
  intro a
  rw [mem_closure_iff]
  intro U hU haU
  obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.1 hU
  obtain ⟨I, u, hu, hIV⟩ := isOpen_pi_iff.1 hV _ haU
  let H₀ : Subgroup G := ⨅ H ∈ I, (H : Subgroup G)
  have hH₀ : H₀ ∈ openFiniteIndex G := by
    refine ⟨?_, Subgroup.finiteIndex_iInf' _ fun H _ => H.2.2⟩
    have : (H₀ : Set G) = ⋂ H ∈ I, ((H : Subgroup G) : Set G) := by
      simp [H₀, Subgroup.coe_iInf]
    rw [this]
    exact isOpen_biInter_finset fun H _ => H.2.1
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective
    ((a : ∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G)) ⟨H₀, hH₀⟩)
  refine ⟨of G x, hIV fun H hH => ?_, x, rfl⟩
  have hle : H₀ ≤ (H : Subgroup G) := iInf₂_le H hH
  have := apply_eq a (H := ⟨H₀, hH₀⟩) (H' := H) hle
  rw [← hx, quotientMapOfLE_mk] at this
  change (x : G ⧸ (H : Subgroup G)) ∈ u H
  rw [this]
  exact (hu H hH).2

end openCompletion

end Completion

end GroundTheory.LocalField
