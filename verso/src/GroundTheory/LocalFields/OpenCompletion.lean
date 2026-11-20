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
Unfold both sides to obtain the same proposition, which implies itself.
-/
theorem mem_iff {a : ∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G)} :
    a ∈ openCompletion G ↔
      ∀ (H H' : openFiniteIndex G) (h : (H : Subgroup G) ≤ H'), quotientMapOfLE h (a H) = a H' :=
  Iff.rfl

omit [IsTopologicalGroup G] in
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem apply_eq (a : openCompletion G) {H H' : openFiniteIndex G} (h : (H : Subgroup G) ≤ H') :
    quotientMapOfLE h ((a : ∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G)) H) =
      (a : ∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G)) H' :=
  a.2 H H' h

omit [IsTopologicalGroup G] in

/- English proof (translation)
A detailed English derivation is pending.
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
A detailed English derivation is pending.
-/
theorem discreteTopology_quotient (H : openFiniteIndex G) : DiscreteTopology (G ⧸ (H : Subgroup G)) :=
  QuotientGroup.discreteTopology H.2.1

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
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
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
