import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalRestriction
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

section Res

variable (K E : FiniteSubfield) [Fact (K ≤ E)]

def fixingIncl : E.1.fixingSubgroup →* K.1.fixingSubgroup :=
  Subgroup.inclusion (IntermediateField.fixingSubgroup_le (Fact.out : K ≤ E))

/- English proof (translation)
The claim follows from `continuous_subgroup_inclusion _`.
-/
theorem continuous_fixingIncl : Continuous (fixingIncl K E) :=
  continuous_subgroup_inclusion _

def unitsResMor : Rep.res (fixingIncl K E) (unitsLimitRep K) ⟶ unitsLimitRep E :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

def unitsResField (n : ℕ) : cohomology (unitsLimitRep K) n ⟶ cohomology (unitsLimitRep E) n :=
  cohomologyMapAlong (fixingIncl K E) (continuous_fixingIncl K E) (unitsResMor K E) n

end Res

section IntermediateRes

variable (Kv Ω : Type) [Field Kv] [Field Ω] [Algebra Kv Ω] [Algebra.IsIntegral Kv Ω] (L : IntermediateField Kv Ω)

def unitsScalarsMor :
    Rep.res (AlgEquiv.restrictScalarsHom Kv : Gal(Ω/L) →* Gal(Ω/Kv)) (galUnitsZ Kv Ω) ⟶ galUnitsZ L Ω :=
  Rep.ofHom ⟨LinearMap.id, fun _ => LinearMap.ext fun _ => rfl⟩

def unitsScalarsRes (n : ℕ) : cohomology (galUnitsZ Kv Ω) n ⟶ cohomology (galUnitsZ L Ω) n :=
  cohomologyMapAlong (AlgEquiv.restrictScalarsHom Kv) (continuous_restrictScalarsHom_of_tower Kv L Ω)
    (unitsScalarsMor Kv Ω L) n

end IntermediateRes

section Conj

variable {Ev Ωw Ωv : Type} [Field Ev] [Field Ωw] [Field Ωv] [Algebra Ev Ωw] (Kv : Type) [Field Kv]
  [Algebra Kv Ωv] (L : IntermediateField Kv Ωv) (e : Ωw ≃+* Ωv)
  (he : ∀ y : Ev, e (algebraMap Ev Ωw y) ∈ L) (hL : ∀ l ∈ L, ∃ y : Ev, e (algebraMap Ev Ωw y) = l)

def fieldConjHom : Gal(Ωw/Ev) →* Gal(Ωv/L) where
  toFun σ := AlgEquiv.ofRingEquiv (f := (e.symm.trans (σ : Ωw ≃+* Ωw)).trans e) fun l => by
    obtain ⟨y, hy⟩ := hL l l.2
    change e (σ (e.symm (l : Ωv))) = l
    rw [← hy, RingEquiv.symm_apply_apply, AlgEquiv.commutes]
  map_one' := AlgEquiv.ext fun x => by
    change e (e.symm x) = x
    exact e.apply_symm_apply x
  map_mul' σ τ := AlgEquiv.ext fun x => by
    change e ((σ * τ) (e.symm x)) = e (σ (e.symm (e (τ (e.symm x)))))
    rw [RingEquiv.symm_apply_apply]
    rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fieldConjHom_apply (σ : Gal(Ωw/Ev)) (x : Ωv) : fieldConjHom Kv L e hL σ x = e (σ (e.symm x)) :=
  rfl

variable [Algebra.IsIntegral Ev Ωw]

/- English proof (translation)
Use `continuous_of_continuousAt_one _ ?_` and prove the remaining obligations. Rewrite using `[ContinuousAt, map_one]`. Introduce `s hs`. Take `⟨M, hM, hMs⟩` from `(krullTopology_mem_nhds_one_iff L Ωv s).1 hs`. Rewrite using `[Filter.mem_map, krullTopology_mem_nhds_one_iff]`.

Establish `: Module.Free L M` using `Module.Free.of_divisionRing L M`. Set `b` to `Module.finBasis L M`. Set `T : Set Ωw` to `Set.range fun i => e.symm (b i : Ωv)`. Use `⟨IntermediateField.adjoin Ev T, ?_, ?_⟩` and prove the remaining obligations. Use `IntermediateField.finiteDimensional_adjoin fun x _ => ?_` and prove the remaining obligations.

Conclude with `Algebra.IsIntegral.isIntegral x`. Introduce `σ hσ`. Apply `hMs` to reduce the goal to its premises. Rewrite `hσ`, the goal using `[SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`.

Establish `hT : ∀ i, fieldConjHom Kv L e hL σ (b i : Ωv) = b i` using `fun i => by`. Rewrite using `[fieldConjHom_apply, hσ _ (IntermediateField.subset_adjoin Ev T ⟨i, rfl⟩), RingEquiv.apply_symm_apply]`. Establish `hx' : x = ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : Ωv)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_sum]`.

Conclude with `Finset.sum_congr rfl fun i _ => map_smul M.val _ _`. Rewrite using `[hx', map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, hT]`.
-/
theorem continuous_fieldConjHom : Continuous (fieldConjHom Kv L e hL) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro s hs
  obtain ⟨M, hM, hMs⟩ := (krullTopology_mem_nhds_one_iff L Ωv s).1 hs
  rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
  have : Module.Free L M := Module.Free.of_divisionRing L M
  let b := Module.finBasis L M
  let T : Set Ωw := Set.range fun i => e.symm (b i : Ωv)
  refine ⟨IntermediateField.adjoin Ev T, ?_, ?_⟩
  · refine IntermediateField.finiteDimensional_adjoin fun x _ => ?_
    exact Algebra.IsIntegral.isIntegral x
  · intro σ hσ
    apply hMs
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
    intro x hx
    have hT : ∀ i, fieldConjHom Kv L e hL σ (b i : Ωv) = b i := fun i => by
      rw [fieldConjHom_apply, hσ _ (IntermediateField.subset_adjoin Ev T ⟨i, rfl⟩), RingEquiv.apply_symm_apply]
    have hx' : x = ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : Ωv) := by
      calc x = M.val (∑ i, b.repr ⟨x, hx⟩ i • b i) := by rw [b.sum_repr]; rfl
        _ = ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : Ωv) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun i _ => map_smul M.val _ _
    rw [hx', map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hT]

variable [Algebra.IsIntegral L Ωv]

def fieldConjUnitsMor : Rep.res (fieldConjHom Kv L e hL) (galUnitsZ L Ωv) ⟶ galUnitsZ Ev Ωw :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (Units.map e.symm.toRingHom.toMonoidHom)).toIntLinearMap,
    fun σ => LinearMap.ext fun x => congrArg Additive.ofMul (Units.ext (by
      change e.symm (e (σ (e.symm ((Additive.toMul (x : Additive Ωvˣ) : Ωvˣ) : Ωv)))) =
        σ (e.symm ((Additive.toMul (x : Additive Ωvˣ) : Ωvˣ) : Ωv))
      exact e.symm_apply_apply _))⟩

end Conj

section Main

variable {K E : FiniteSubfield} [Fact (K ≤ E)]
  (Kv : Type) {Ωv : Type} [Field Kv] [Field Ωv] [Algebra K.1 Kv] [Algebra Kv Ωv] [Algebra K.1 Ωv]
  [IsScalarTower K.1 Kv Ωv] [Algebra.IsIntegral Kv Ωv]
  (Ew : Type) {Ωw : Type} [Field Ew] [Field Ωw] [Algebra E.1 Ew] [Algebra Ew Ωw] [Algebra E.1 Ωw]
  [IsScalarTower E.1 Ew Ωw] [Algebra.IsIntegral Ew Ωw]
  (L : IntermediateField Kv Ωv) [Algebra.IsIntegral L Ωv] (e : Ωw ≃+* Ωv)
  (hL : ∀ l ∈ L, ∃ y : Ew, e (algebraMap Ew Ωw y) = l)
  (ιK : ℚ̄ →ₐ[K.1] Ωv) (ιE : ℚ̄ →ₐ[E.1] Ωw) (hι : ∀ x, e (ιE x) = ιK x)

include hι in

/- English proof (translation)
Establish `h : unitsResField K E n ≫ unitsLocalRes Ew ιE n = unitsLocalRes Kv ιK n ≫ unitsScalarsRes Kv Ωv L n ≫ cohomologyMapAlong (fieldConjHom Kv L e hL) (continuous_fieldConjHom Kv L e hL) (fieldConjUnitsMor Kv L e hL) n`. Rewrite using `[unitsResField, unitsLocalRes, unitsLocalRes, unitsScalarsRes, ← cohomologyMapAlong_comp, ← cohomologyMapAlong_comp, ← cohomologyMapAlong_comp]`. Use `cohomologyMapAlong_congr _ _ _ _ (MonoidHom.ext fun σ => ?_) (fun a => ?_) n` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Apply `AlgEquiv.ext` to reduce the goal to its premises.

Introduce `y`. Apply `ιK.injective` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `ιK ((globalDecomp Ew ιE σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) y) = ιK ((globalDecomp Kv ιK (AlgEquiv.restrictScalarsHom Kv (fieldConjHom Kv L e hL σ)) : ℚ̄ ≃ₐ[ℚ] ℚ̄) y)`. Rewrite using `[globalDecomp_apply, ← hι, ← hι, globalDecomp_apply]`. Express the relevant statement in the definitionally equal form `e (σ (ιE y)) = e (σ (e.symm (e (ιE y))))`.

Rewrite using `[RingEquiv.symm_apply_apply]`. Apply `Additive.toMul.injective` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `ιE ((Additive.toMul (a : Additive ℚ̄ˣ) : ℚ̄ˣ) : ℚ̄) = e.symm (ιK ((Additive.toMul (a : Additive ℚ̄ˣ) : ℚ̄ˣ) : ℚ̄))`. Rewrite using `[← hι, RingEquiv.symm_apply_apply]`.

Conclude with `(congrArg (fun φ => φ.hom x) h)`.
-/
theorem unitsLocalRes_unitsResField (n : ℕ) (x : cohomology (unitsLimitRep K) n) :
    (unitsLocalRes Ew ιE n).hom ((unitsResField K E n).hom x) =
      (cohomologyMapAlong (fieldConjHom Kv L e hL) (continuous_fieldConjHom Kv L e hL) (fieldConjUnitsMor Kv L e hL) n).hom
        ((unitsScalarsRes Kv Ωv L n).hom ((unitsLocalRes Kv ιK n).hom x)) := by
  have h : unitsResField K E n ≫ unitsLocalRes Ew ιE n = unitsLocalRes Kv ιK n ≫
      unitsScalarsRes Kv Ωv L n ≫
        cohomologyMapAlong (fieldConjHom Kv L e hL) (continuous_fieldConjHom Kv L e hL) (fieldConjUnitsMor Kv L e hL) n := by
    rw [unitsResField, unitsLocalRes, unitsLocalRes, unitsScalarsRes, ← cohomologyMapAlong_comp,
      ← cohomologyMapAlong_comp, ← cohomologyMapAlong_comp]
    refine cohomologyMapAlong_congr _ _ _ _ (MonoidHom.ext fun σ => ?_) (fun a => ?_) n
    · apply Subtype.ext
      apply AlgEquiv.ext
      intro y
      apply ιK.injective
      change ιK ((globalDecomp Ew ιE σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) y) =
        ιK ((globalDecomp Kv ιK (AlgEquiv.restrictScalarsHom Kv (fieldConjHom Kv L e hL σ)) : ℚ̄ ≃ₐ[ℚ] ℚ̄) y)
      rw [globalDecomp_apply, ← hι, ← hι, globalDecomp_apply]
      change e (σ (ιE y)) = e (σ (e.symm (e (ιE y))))
      rw [RingEquiv.symm_apply_apply]
    · apply Additive.toMul.injective
      apply Units.ext
      change ιE ((Additive.toMul (a : Additive ℚ̄ˣ) : ℚ̄ˣ) : ℚ̄) =
        e.symm (ιK ((Additive.toMul (a : Additive ℚ̄ˣ) : ℚ̄ˣ) : ℚ̄))
      rw [← hι, RingEquiv.symm_apply_apply]
  exact (congrArg (fun φ => φ.hom x) h)

include hL hι in

/- English proof (translation)
Rewrite using `[unitsLocalRes_unitsResField Kv Ew L e hL ιK ιE hι, hx, map_zero]`.
-/
theorem unitsLocalRes_unitsResField_eq_zero (n : ℕ) (x : cohomology (unitsLimitRep K) n)
    (hx : (unitsScalarsRes Kv Ωv L n).hom ((unitsLocalRes Kv ιK n).hom x) = 0) :
    (unitsLocalRes Ew ιE n).hom ((unitsResField K E n).hom x) = 0 := by
  rw [unitsLocalRes_unitsResField Kv Ew L e hL ιK ιE hι, hx, map_zero]

end Main

end

end GroundTheory.ProfCoh
