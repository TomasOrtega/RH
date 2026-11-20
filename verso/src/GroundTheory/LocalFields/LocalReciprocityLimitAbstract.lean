import Mathlib
import GroundTheory.LocalFields.AbstractLocalReciprocity.ReciprocityAbelianizationRestrictReciprocityLimi
import GroundTheory.LocalFields.AbstractLocalReciprocity.Functoriality

namespace GroundTheory.LocalField.Abstract

section TopologicalAbelianization

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
  [TopologicalSpace H] [IsTopologicalGroup H]

/- English proof (translation)
Use `Subgroup.topologicalClosure_minimal _ ?_ ((Subgroup.isClosed_topologicalClosure _).preimage hf)` and prove the remaining obligations. Rewrite using `[commutator, Subgroup.commutator_le]`. Introduce `a _ b _`. Rewrite using `[Subgroup.mem_comap, map_commutatorElement]`. Conclude with `Subgroup.le_topologicalClosure _ (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))`.
-/
theorem topologicalClosure_commutator_le_comap (f : G →* H) (hf : Continuous f) :
    (commutator G).topologicalClosure ≤ (commutator H).topologicalClosure.comap f := by
  refine Subgroup.topologicalClosure_minimal _ ?_
    ((Subgroup.isClosed_topologicalClosure _).preimage hf)
  rw [commutator, Subgroup.commutator_le]
  intro a _ b _
  rw [Subgroup.mem_comap, map_commutatorElement]
  exact Subgroup.le_topologicalClosure _
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))

def topologicalAbelianizationMap (f : G →* H) (hf : Continuous f) :
    TopologicalAbelianization G →* TopologicalAbelianization H :=
  QuotientGroup.map _ _ f (topologicalClosure_commutator_le_comap f hf)

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem topologicalAbelianizationMap_mk (f : G →* H) (hf : Continuous f) (g : G) :
    topologicalAbelianizationMap f hf (g : TopologicalAbelianization G) =
      (f g : TopologicalAbelianization H) :=
  rfl

/- English proof (translation)
Rewrite using `[(QuotientGroup.isQuotientMap_mk _).continuous_iff]`. Conclude with `(QuotientGroup.isQuotientMap_mk _).continuous.comp hf`.
-/
theorem continuous_topologicalAbelianizationMap (f : G →* H) (hf : Continuous f) :
    Continuous (topologicalAbelianizationMap f hf) := by
  rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
  exact (QuotientGroup.isQuotientMap_mk _).continuous.comp hf

end TopologicalAbelianization

section Maps

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
/- English proof (translation)
The claim follows from `continuous_subtype_val.subtype_mk _`.
-/
theorem continuous_inclusion {K K' : Subgroup G} (hK : K' ≤ K) :
    Continuous (Subgroup.inclusion hK) :=
  continuous_subtype_val.subtype_mk _

def limitRestrict {K K' : OpenSubgroup G} (hK : K' ≤ K) :
    TopologicalAbelianization (K' : Subgroup G) →* TopologicalAbelianization (K : Subgroup G) :=
  topologicalAbelianizationMap (Subgroup.inclusion hK) (continuous_inclusion hK)

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem limitRestrict_mk {K K' : OpenSubgroup G} (hK : K' ≤ K) (g : (K' : Subgroup G)) :
    limitRestrict hK (g : TopologicalAbelianization (K' : Subgroup G)) =
      ((⟨g, hK g.2⟩ : (K : Subgroup G)) : TopologicalAbelianization (K : Subgroup G)) :=
  rfl

def conjHom (σ : G) (K : OpenSubgroup G) :
    (K : Subgroup G) →* ((conjOpen σ K : OpenSubgroup G) : Subgroup G) where
  toFun τ := ⟨σ * τ * σ⁻¹, τ, τ.2, rfl⟩
  map_one' := Subtype.ext (by simp)
  map_mul' τ τ' := Subtype.ext (by simp [mul_assoc])

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_conjHom (σ : G) (K : OpenSubgroup G) (τ : (K : Subgroup G)) :
    ((conjHom σ K τ : ((conjOpen σ K : OpenSubgroup G) : Subgroup G)) : G) = σ * τ * σ⁻¹ :=
  rfl

/- English proof (translation)
The claim follows from `((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _`.
-/
theorem continuous_conjHom (σ : G) (K : OpenSubgroup G) : Continuous (conjHom σ K) :=
  ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

def limitConj (σ : G) (K : OpenSubgroup G) :
    TopologicalAbelianization (K : Subgroup G) →*
      TopologicalAbelianization ((conjOpen σ K : OpenSubgroup G) : Subgroup G) :=
  topologicalAbelianizationMap (conjHom σ K) (continuous_conjHom σ K)

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem limitConj_mk (σ : G) (K : OpenSubgroup G) (g : (K : Subgroup G)) :
    limitConj σ K (g : TopologicalAbelianization (K : Subgroup G)) =
      (conjHom σ K g : TopologicalAbelianization ((conjOpen σ K : OpenSubgroup G) : Subgroup G)) :=
  rfl

end Maps

namespace ClassFieldData

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  (D : ClassFieldData G A) (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]

/- English proof (translation)
Use `D.eq_reciprocityLimit hax fun L hL _ => ?_` and prove the remaining obligations. Establish `hmap : (commutator (K' : Subgroup G)).map (Subgroup.inclusion hK) ≤ commutator (K : Subgroup G)`. Rewrite using `[commutator, Subgroup.map_commutator]`. Conclude with `Subgroup.commutator_mono le_top le_top`. Establish `hL' : IsAbelianExtension K' (L ⊓ K')`.

Use `⟨inf_le_right, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[Subgroup.mem_subgroupOf]`. Use `⟨?_, x.2⟩` and prove the remaining obligations. Establish `h1` using `hL.commutator_le (hmap ⟨x, hx, rfl⟩)`. Rewrite `h1` using `[Subgroup.mem_subgroupOf]`.

Conclude with `h1`. Use `hL'.normal` as an intermediate fact. Take `⟨g, hg⟩` from `QuotientGroup.mk_surjective (D.reciprocityLimit hax K' a)`. Establish `e` using `D.reciprocity_abelianizationRestrict_reciprocityLimit hax hL' a`. Rewrite `e` using `[← hg, abelianizationRestrict_mk]`.

Rewrite using `[← hg, limitRestrict_mk, abelianizationRestrict_mk]`. Establish `h` using `D.reciprocity_galRestrict hax hL.le hL'.le hK inf_le_left (g : (K' : Subgroup G) ⧸ ((L ⊓ K' : OpenSubgroup G) : Subgroup G).subgroupOf K')`. Rewrite `h` using `[galRestrict_mk, e, normTateZero_mk]`. Conclude with `h`.
-/
theorem limitRestrict_reciprocityLimit {K K' : OpenSubgroup G} (hK : K' ≤ K)
    (a : fixedModule A (K' : Subgroup G)) :
    limitRestrict hK (D.reciprocityLimit hax K' a) =
      D.reciprocityLimit hax K (norm A (K : Subgroup G) (K' : Subgroup G) a) := by
  refine D.eq_reciprocityLimit hax fun L hL _ => ?_
  have hmap : (commutator (K' : Subgroup G)).map (Subgroup.inclusion hK) ≤
      commutator (K : Subgroup G) := by
    rw [commutator, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  have hL' : IsAbelianExtension K' (L ⊓ K') := by
    refine ⟨inf_le_right, fun x hx => ?_⟩
    rw [Subgroup.mem_subgroupOf]
    refine ⟨?_, x.2⟩
    have h1 := hL.commutator_le (hmap ⟨x, hx, rfl⟩)
    rw [Subgroup.mem_subgroupOf] at h1
    exact h1
  have := hL'.normal
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (D.reciprocityLimit hax K' a)
  have e := D.reciprocity_abelianizationRestrict_reciprocityLimit hax hL' a
  rw [← hg, abelianizationRestrict_mk] at e
  rw [← hg, limitRestrict_mk, abelianizationRestrict_mk]
  have h := D.reciprocity_galRestrict hax hL.le hL'.le hK inf_le_left
    (g : (K' : Subgroup G) ⧸ ((L ⊓ K' : OpenSubgroup G) : Subgroup G).subgroupOf K')
  rw [galRestrict_mk, e, normTateZero_mk] at h
  exact h

end ClassFieldData

end GroundTheory.LocalField.Abstract
