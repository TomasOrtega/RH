import Mathlib
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.GroupStructure
import GroundTheory.ProfiniteCohomology.GaloisModules.FixedField
import GroundTheory.LocalFields.LubinTatePoints
import GroundTheory.LocalFields.SeparableClosure
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Vanishing
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open IntermediateField GroundTheory.LocalField ValuativeRel

section Preimage

variable {K Ksep : Type} [Field K] [Field Ksep] [Algebra K Ksep] [IsGalois K Ksep]
  (V : OpenNormalSubgroup Gal(Ksep/K))

noncomputable abbrev restrictFixed : Gal(Ksep/K) →* Gal(fixedField (V : Subgroup Gal(Ksep/K))/K) :=
  AlgEquiv.restrictNormalHom (fixedField (V : Subgroup Gal(Ksep/K)))

/- English proof (translation)
The claim follows from `AlgEquiv.restrictNormalHom_surjective Ksep`.
-/
theorem restrictFixed_surjective : Function.Surjective (restrictFixed V) :=
  AlgEquiv.restrictNormalHom_surjective Ksep

/- English proof (translation)
The claim follows from `AlgEquiv.restrictNormal_commutes σ _ x`.
-/
theorem restrictFixed_apply (σ : Gal(Ksep/K)) (x : fixedField (V : Subgroup Gal(Ksep/K))) :
    ((restrictFixed V σ x : fixedField (V : Subgroup Gal(Ksep/K))) : Ksep) = σ x :=
  AlgEquiv.restrictNormal_commutes σ _ x

/- English proof (translation)
Rewrite using `[restrictFixed, IntermediateField.restrictNormalHom_ker, fixingSubgroup_fixedField_openNormalSubgroup]`.
-/
theorem ker_restrictFixed : (restrictFixed V).ker = (V : Subgroup Gal(Ksep/K)) := by
  rw [restrictFixed, IntermediateField.restrictNormalHom_ker,
    fixingSubgroup_fixedField_openNormalSubgroup]

/- English proof (translation)
Rewrite using `[← MonoidHom.mem_ker]`. Conclude with `(SetLike.ext_iff.1 (ker_restrictFixed V) σ).symm`.
-/
theorem mem_V_iff_restrictFixed_eq_one (σ : Gal(Ksep/K)) :
    σ ∈ (V : Subgroup Gal(Ksep/K)) ↔ restrictFixed V σ = 1 := by
  rw [← MonoidHom.mem_ker]
  exact (SetLike.ext_iff.1 (ker_restrictFixed V) σ).symm

noncomputable def preimageOpen (S : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K)) :
    OpenSubgroup Gal(Ksep/K) where
  toSubgroup := S.comap (restrictFixed V)
  isOpen' := Subgroup.isOpen_mono (H₁ := (V : Subgroup Gal(Ksep/K))) (fun σ hσ => by
      change restrictFixed V σ ∈ S
      rw [(mem_V_iff_restrictFixed_eq_one V σ).1 hσ]
      exact S.one_mem) V.isOpen'

variable {V}

@[simp]
/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_preimageOpen {S : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K)} {σ : Gal(Ksep/K)} :
    σ ∈ (preimageOpen V S : Subgroup Gal(Ksep/K)) ↔ restrictFixed V σ ∈ S :=
  Iff.rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_preimageOpen (S : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K)) :
    (preimageOpen V S : Subgroup Gal(Ksep/K)) = S.comap (restrictFixed V) :=
  rfl

/- English proof (translation)
Introduce `σ hσ` and use `by rw [mem_preimageOpen, (mem_V_iff_restrictFixed_eq_one V σ).1 hσ] exact S.one_mem`.
-/
theorem le_preimageOpen (S : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K)) :
    (V : Subgroup Gal(Ksep/K)) ≤ preimageOpen V S := fun σ hσ => by
  rw [mem_preimageOpen, (mem_V_iff_restrictFixed_eq_one V σ).1 hσ]
  exact S.one_mem

/- English proof (translation)
Introduce `_ hσ` and use `h hσ`.
-/
theorem preimageOpen_le_preimageOpen {S S' : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K)}
    (h : S ≤ S') : preimageOpen V S ≤ preimageOpen V S' := fun _ hσ => h hσ

instance preimageOpen_normal (S : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K)) [S.Normal] :
    ((preimageOpen V S : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)).Normal :=
  Subgroup.Normal.comap inferInstance _

/- English proof (translation)
Use extensionality with `σ`. Rewrite using `[coe_preimageOpen, Subgroup.mem_comap, Subgroup.mem_bot, mem_V_iff_restrictFixed_eq_one]`.
-/
theorem preimageOpen_bot :
    ((preimageOpen V ⊥ : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)) = V := by
  ext σ
  rw [coe_preimageOpen, Subgroup.mem_comap, Subgroup.mem_bot, mem_V_iff_restrictFixed_eq_one]

/- English proof (translation)
Rewrite using `[coe_preimageOpen, coe_preimageOpen, Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective (restrictFixed_surjective V)]`.
-/
theorem relIndex_preimageOpen (S S' : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K)) :
    ((preimageOpen V S : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)).relIndex
      (preimageOpen V S') = S.relIndex S' := by
  rw [coe_preimageOpen, coe_preimageOpen, Subgroup.relIndex_comap,
    Subgroup.map_comap_eq_self_of_surjective (restrictFixed_surjective V)]

/- English proof (translation)
Establish `h` using `relIndex_preimageOpen (V := V) ⊥ S`. Rewrite `h` using `[preimageOpen_bot, Subgroup.relIndex_bot_left]`. Conclude with `h`.
-/
theorem relIndex_V_preimageOpen (S : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K)) :
    (V : Subgroup Gal(Ksep/K)).relIndex (preimageOpen V S) = Nat.card S := by
  have h := relIndex_preimageOpen (V := V) ⊥ S
  rw [preimageOpen_bot, Subgroup.relIndex_bot_left] at h
  exact h

/- English proof (translation)
Rewrite using `[coe_preimageOpen]`. Conclude with `Subgroup.index_comap_of_surjective S (restrictFixed_surjective V)`.
-/
theorem index_preimageOpen (S : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K)) :
    ((preimageOpen V S : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)).index = S.index := by
  rw [coe_preimageOpen]
  exact Subgroup.index_comap_of_surjective S (restrictFixed_surjective V)

noncomputable def quotientPreimageOpenEquiv (S : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K))
    [S.Normal] :
    Gal(Ksep/K) ⧸ ((preimageOpen V S : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)) ≃*
      Gal(fixedField (V : Subgroup Gal(Ksep/K))/K) ⧸ S :=
  (QuotientGroup.quotientMulEquivOfEq (by
      ext σ
      rw [coe_preimageOpen, Subgroup.mem_comap, MonoidHom.mem_ker, MonoidHom.comp_apply,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff])).trans
    (QuotientGroup.quotientKerEquivOfSurjective ((QuotientGroup.mk' S).comp (restrictFixed V))
      ((QuotientGroup.mk'_surjective S).comp (restrictFixed_surjective V)))

/- English proof (translation)
The claim follows from `isCyclic_of_surjective (quotientPreimageOpenEquiv S).symm.toMonoidHom (quotientPreimageOpenEquiv S).symm.surjective`.
-/
theorem isCyclic_quotient_preimageOpen (S : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K))
    [S.Normal] [IsCyclic (Gal(fixedField (V : Subgroup Gal(Ksep/K))/K) ⧸ S)] :
    IsCyclic (Gal(Ksep/K) ⧸ ((preimageOpen V S : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K))) :=
  isCyclic_of_surjective (quotientPreimageOpenEquiv S).symm.toMonoidHom
    (quotientPreimageOpenEquiv S).symm.surjective

/- English proof (translation)
The claim follows from `Nat.card_congr (quotientPreimageOpenEquiv S).toEquiv`.
-/
theorem card_quotient_preimageOpen (S : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K))
    [S.Normal] :
    Nat.card (Gal(Ksep/K) ⧸ ((preimageOpen V S : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K))) =
      Nat.card (Gal(fixedField (V : Subgroup Gal(Ksep/K))/K) ⧸ S) :=
  Nat.card_congr (quotientPreimageOpenEquiv S).toEquiv

/- English proof (translation)
Establish `hζV : ζ ∈ fixedField (V : Subgroup Gal(Ksep/K))` using `(mem_fixedField_iff _ _).2 fun σ hσ => hV σ hσ ζ hζ`. Use `set ζ' : fixedField (V : Subgroup Gal(Ksep/K)) := ⟨ζ, hζV⟩`. Establish `hζ' : ζ' ^ n = 1` using `Subtype.ext (by simp [ζ', hζ])`. Establish `h` using `(mem_fixedField_iff _ _).1 (hS ζ' hζ')`. Use `(mem_fixedField_iff _ _).2 fun σ hσ => ?_` and prove the remaining obligations.

Use `congrArg (fun y : fixedField (V : Subgroup Gal(Ksep/K)) => (y : Ksep)) (h _ hσ)` as an intermediate fact. Simplify `this` using `[ζ', restrictFixed_apply]`.
-/
theorem pow_eq_one_mem_fixedField_preimageOpen {n : ℕ}
    (hV : ∀ σ ∈ (V : Subgroup Gal(Ksep/K)), ∀ ζ : Ksep, ζ ^ n = 1 → σ ζ = ζ)
    {S : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K)}
    (hS : ∀ ζ : fixedField (V : Subgroup Gal(Ksep/K)), ζ ^ n = 1 → ζ ∈ IntermediateField.fixedField S)
    {ζ : Ksep} (hζ : ζ ^ n = 1) :
    ζ ∈ fixedField ((preimageOpen V S : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)) := by
  have hζV : ζ ∈ fixedField (V : Subgroup Gal(Ksep/K)) :=
    (mem_fixedField_iff _ _).2 fun σ hσ => hV σ hσ ζ hζ
  set ζ' : fixedField (V : Subgroup Gal(Ksep/K)) := ⟨ζ, hζV⟩
  have hζ' : ζ' ^ n = 1 := Subtype.ext (by simp [ζ', hζ])
  have h := (mem_fixedField_iff _ _).1 (hS ζ' hζ')
  refine (mem_fixedField_iff _ _).2 fun σ hσ => ?_
  have := congrArg (fun y : fixedField (V : Subgroup Gal(Ksep/K)) => (y : Ksep)) (h _ hσ)
  simpa [ζ', restrictFixed_apply] using this

end Preimage

section Inertia

variable {K Ksep : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] [ValuativeRel Ksep] [TopologicalSpace Ksep]
  [IsValuativeTopology Ksep] [ValuativeExtension K Ksep]
  {V : OpenNormalSubgroup Gal(Ksep/K)}

/- English proof (translation)
Establish `hx'1 : valuation (fixedField (V : Subgroup Gal(Ksep/K))) ⟨x, hx⟩ ≤ 1` using `(valuation_le_one_iff_coe _ ⟨x, hx⟩).2 hx1`. Establish `h` using `hS hσ ⟨⟨x, hx⟩, hx'1⟩`. Simplify using `only [zero_add, Int.toNat_one, pow_one] at h`. Establish `h2` using `mem_maximalIdeal_integer_iff.1 h`. Establish `h3` using `(valuation_lt_one_iff_coe _ _).1 h2`.

Simplify `h3` using `[restrictFixed_apply]`.
-/
theorem valuation_sub_lt_one_of_mem_preimageOpen
    {S : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K)}
    (hS : S ≤ lowerRamificationGroup K (fixedField (V : Subgroup Gal(Ksep/K))) 0)
    {σ : Gal(Ksep/K)} (hσ : σ ∈ (preimageOpen V S : Subgroup Gal(Ksep/K)))
    {x : Ksep} (hx : x ∈ fixedField (V : Subgroup Gal(Ksep/K))) (hx1 : valuation Ksep x ≤ 1) :
    valuation Ksep (σ x - x) < 1 := by
  have hx'1 : valuation (fixedField (V : Subgroup Gal(Ksep/K))) ⟨x, hx⟩ ≤ 1 :=
    (valuation_le_one_iff_coe _ ⟨x, hx⟩).2 hx1
  have h := hS hσ ⟨⟨x, hx⟩, hx'1⟩
  simp only [zero_add, Int.toNat_one, pow_one] at h
  have h2 := mem_maximalIdeal_integer_iff.1 h
  have h3 := (valuation_lt_one_iff_coe _ _).1 h2
  simpa [restrictFixed_apply] using h3

end Inertia

end GroundTheory.ProfCoh
