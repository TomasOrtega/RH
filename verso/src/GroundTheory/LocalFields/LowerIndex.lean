import Mathlib
import GroundTheory.LocalFields.Ramification
import GroundTheory.LocalFields.Monogenic
import GroundTheory.LocalFields.Unramified

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing IsDiscreteValuationRing Polynomial

/- English proof (translation)
Use extensionality with `σ`. Rewrite using `[MonoidHom.mem_range, IntermediateField.mem_fixingSubgroup_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨τ, rfl⟩ m hm`. Conclude with `τ.commutes ⟨m, hm⟩`.

Introduce `h`. Use `⟨{ σ with commutes' := fun m ↦ h m m.2 }, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Both sides reduce to the same expression.
-/
theorem range_restrictScalarsHom {K L : Type*} [Field K] [Field L] [Algebra K L]
    (M : IntermediateField K L) :
    (AlgEquiv.restrictScalarsHom K : (L ≃ₐ[M] L) →* (L ≃ₐ[K] L)).range = M.fixingSubgroup := by
  ext σ
  rw [MonoidHom.mem_range, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · rintro ⟨τ, rfl⟩ m hm
    exact τ.commutes ⟨m, hm⟩
  · intro h
    refine ⟨{ σ with commutes' := fun m ↦ h m m.2 }, ?_⟩
    ext x
    rfl

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

def lowerIndex (σ : L ≃ₐ[K] L) : ℕ∞ :=
  ⨅ x : 𝒪[L], addVal 𝒪[L] (integerAlgEquiv K L σ x - x)

variable {K L}

/- English proof (translation)
The claim follows from `le_iInf_iff`.
-/
theorem le_lowerIndex_iff {σ : L ≃ₐ[K] L} {n : ℕ∞} :
    n ≤ lowerIndex K L σ ↔ ∀ x : 𝒪[L], n ≤ addVal 𝒪[L] (integerAlgEquiv K L σ x - x) :=
  le_iInf_iff

/- English proof (translation)
The claim follows from `iInf_le _ x`.
-/
theorem lowerIndex_le (σ : L ≃ₐ[K] L) (x : 𝒪[L]) :
    lowerIndex K L σ ≤ addVal 𝒪[L] (integerAlgEquiv K L σ x - x) :=
  iInf_le _ x

/- English proof (translation)
Rewrite using `[mem_lowerRamificationGroup_iff, le_lowerIndex_iff]`. Simplify using `only [mem_maximalIdeal_pow_iff_le_addVal]`.
-/
theorem mem_lowerRamificationGroup_iff_lowerIndex {i : ℤ} {σ : L ≃ₐ[K] L} :
    σ ∈ lowerRamificationGroup K L i ↔ (((i + 1).toNat : ℕ) : ℕ∞) ≤ lowerIndex K L σ := by
  rw [mem_lowerRamificationGroup_iff, le_lowerIndex_iff]
  simp only [mem_maximalIdeal_pow_iff_le_addVal]

/- English proof (translation)
Rewrite using `[mem_lowerRamificationGroup_natCast_iff, le_lowerIndex_iff]`. Simplify using `only [mem_maximalIdeal_pow_iff_le_addVal]`. Use the proof step `@[simp]`.
-/
theorem mem_lowerRamificationGroup_natCast_iff_lowerIndex {n : ℕ} {σ : L ≃ₐ[K] L} :
    σ ∈ lowerRamificationGroup K L n ↔ ((n + 1 : ℕ) : ℕ∞) ≤ lowerIndex K L σ := by
  rw [mem_lowerRamificationGroup_natCast_iff, le_lowerIndex_iff]
  simp only [mem_maximalIdeal_pow_iff_le_addVal]

@[simp]
/- English proof (translation)
Simplify using `[lowerIndex]`.
-/
theorem lowerIndex_one : lowerIndex K L 1 = ⊤ := by
  simp [lowerIndex]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Apply `algEquiv_eq_one_of_forall_integer` to reduce the goal to its premises. Introduce `x`. Use `lowerIndex_le σ x` as an intermediate fact.

Rewrite `this` using `[h, top_le_iff, addVal_eq_top_iff, sub_eq_zero]`. Then use the resulting hypothesis. Introduce and unpack `rfl`. Conclude with `lowerIndex_one`.
-/
theorem lowerIndex_eq_top_iff {σ : L ≃ₐ[K] L} : lowerIndex K L σ = ⊤ ↔ σ = 1 := by
  constructor
  · intro h
    apply algEquiv_eq_one_of_forall_integer
    intro x
    have := lowerIndex_le σ x
    rwa [h, top_le_iff, addVal_eq_top_iff, sub_eq_zero] at this
  · rintro rfl
    exact lowerIndex_one

/- English proof (translation)
The claim follows from `fun h ↦ hσ (lowerIndex_eq_top_iff.mp h)`.
-/
theorem lowerIndex_ne_top {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) : lowerIndex K L σ ≠ ⊤ :=
  fun h ↦ hσ (lowerIndex_eq_top_iff.mp h)

/- English proof (translation)
Rewrite using `[show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, mem_lowerRamificationGroup_natCast_iff_lowerIndex]`. Simplify using the standard rewrite rules.
-/
theorem one_le_lowerIndex_iff {σ : L ≃ₐ[K] L} :
    1 ≤ lowerIndex K L σ ↔ σ ∈ lowerRamificationGroup K L 0 := by
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, mem_lowerRamificationGroup_natCast_iff_lowerIndex]
  simp

/- English proof (translation)
Rewrite using `[← one_le_lowerIndex_iff, not_le, Order.lt_one_iff]`.
-/
theorem lowerIndex_eq_zero_iff {σ : L ≃ₐ[K] L} :
    lowerIndex K L σ = 0 ↔ σ ∉ lowerRamificationGroup K L 0 := by
  rw [← one_le_lowerIndex_iff, not_le, Order.lt_one_iff]

/- English proof (translation)
Rewrite using `[le_lowerIndex_iff]`. Introduce `x`. Establish `h : integerAlgEquiv K L (σ * τ) x - x = (integerAlgEquiv K L σ (integerAlgEquiv K L τ x) - integerAlgEquiv K L τ x) + (integerAlgEquiv K L τ x - x)`. Rewrite using `[map_mul, AlgEquiv.mul_apply]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h]`. Conclude with `le_trans (min_le_min (lowerIndex_le σ _) (lowerIndex_le τ x)) ((addVal 𝒪[L]).map_add _ _)`.
-/
theorem min_le_lowerIndex_mul (σ τ : L ≃ₐ[K] L) :
    min (lowerIndex K L σ) (lowerIndex K L τ) ≤ lowerIndex K L (σ * τ) := by
  rw [le_lowerIndex_iff]
  intro x
  have h : integerAlgEquiv K L (σ * τ) x - x =
      (integerAlgEquiv K L σ (integerAlgEquiv K L τ x) - integerAlgEquiv K L τ x) +
        (integerAlgEquiv K L τ x - x) := by
    rw [map_mul, AlgEquiv.mul_apply]; ring
  rw [h]
  exact le_trans (min_le_min (lowerIndex_le σ _) (lowerIndex_le τ x)) ((addVal 𝒪[L]).map_add _ _)

/- English proof (translation)
Rewrite using `[le_lowerIndex_iff]`. Introduce `x`. Establish `h : integerAlgEquiv K L σ⁻¹ x - x = -(integerAlgEquiv K L σ (integerAlgEquiv K L σ⁻¹ x) - integerAlgEquiv K L σ⁻¹ x)`. Rewrite using `[← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgEquiv.one_apply]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h, AddValuation.map_neg]`. Conclude with `lowerIndex_le σ _`. Use the proof step `@[simp]`.
-/
theorem lowerIndex_le_lowerIndex_inv (σ : L ≃ₐ[K] L) : lowerIndex K L σ ≤ lowerIndex K L σ⁻¹ := by
  rw [le_lowerIndex_iff]
  intro x
  have h : integerAlgEquiv K L σ⁻¹ x - x =
      -(integerAlgEquiv K L σ (integerAlgEquiv K L σ⁻¹ x) - integerAlgEquiv K L σ⁻¹ x) := by
    rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgEquiv.one_apply]
    ring
  rw [h, AddValuation.map_neg]
  exact lowerIndex_le σ _

@[simp]
/- English proof (translation)
The claim follows from `le_antisymm (by simpa using lowerIndex_le_lowerIndex_inv σ⁻¹) (lowerIndex_le_lowerIndex_inv σ)`.
-/
theorem lowerIndex_inv (σ : L ≃ₐ[K] L) : lowerIndex K L σ⁻¹ = lowerIndex K L σ :=
  le_antisymm (by simpa using lowerIndex_le_lowerIndex_inv σ⁻¹) (lowerIndex_le_lowerIndex_inv σ)

/- English proof (translation)
Use `le_antisymm ?_ ((min_eq_right h.le).symm.le.trans (min_le_lowerIndex_mul σ τ))` and prove the remaining obligations. Establish `h1` using `min_le_lowerIndex_mul σ⁻¹ (σ * τ)`. Rewrite `h1` using `[inv_mul_cancel_left, lowerIndex_inv]`. Assume the negation of the conclusion as `h2`. Rewrite `h2` using `[not_le]`.

Conclude with `(lt_min h h2).not_ge h1`.
-/
theorem lowerIndex_mul_of_lt {σ τ : L ≃ₐ[K] L} (h : lowerIndex K L τ < lowerIndex K L σ) :
    lowerIndex K L (σ * τ) = lowerIndex K L τ := by
  refine le_antisymm ?_ ((min_eq_right h.le).symm.le.trans (min_le_lowerIndex_mul σ τ))
  have h1 := min_le_lowerIndex_mul σ⁻¹ (σ * τ)
  rw [inv_mul_cancel_left, lowerIndex_inv] at h1
  by_contra h2
  rw [not_le] at h2
  exact (lt_min h h2).not_ge h1

/- English proof (translation)
Use `le_antisymm (lowerIndex_le σ x) ?_` and prove the remaining obligations. Rewrite using `[le_lowerIndex_iff]`. Introduce `z`. Establish `hz : z ∈ Algebra.adjoin 𝒪[K] {x}` using `hx ▸ trivial`. Rewrite `hz` using `[Algebra.adjoin_singleton_eq_range_aeval]`.

Take `⟨p, rfl⟩` from `hz`. Rewrite using `[addVal_le_iff_dvd]`. Simplify using `only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]`. Rewrite using `[← aeval_algHom_apply, ← eval_map_algebraMap, ← eval_map_algebraMap]`. Conclude with `sub_dvd_eval_sub _ _ _`.
-/
theorem lowerIndex_eq_addVal_of_adjoin_eq_top {x : 𝒪[L]} (hx : Algebra.adjoin 𝒪[K] {x} = ⊤)
    (σ : L ≃ₐ[K] L) : lowerIndex K L σ = addVal 𝒪[L] (integerAlgEquiv K L σ x - x) := by
  refine le_antisymm (lowerIndex_le σ x) ?_
  rw [le_lowerIndex_iff]
  intro z
  have hz : z ∈ Algebra.adjoin 𝒪[K] {x} := hx ▸ trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hz
  obtain ⟨p, rfl⟩ := hz
  rw [addVal_le_iff_dvd]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [← aeval_algHom_apply, ← eval_map_algebraMap, ← eval_map_algebraMap]
  exact sub_dvd_eval_sub _ _ _

section Subgroup

variable (M : IntermediateField K L)

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lowerIndex_restrictScalars (σ : L ≃ₐ[M] L) :
    lowerIndex K L (σ.restrictScalars K) = lowerIndex M L σ :=
  rfl

/- English proof (translation)
Use extensionality with `σ`. Rewrite using `[Subgroup.mem_comap, AlgEquiv.restrictScalarsHom_apply, mem_lowerRamificationGroup_iff_lowerIndex, mem_lowerRamificationGroup_iff_lowerIndex, lowerIndex_restrictScalars]`.
-/
theorem lowerRamificationGroup_comap_restrictScalars (i : ℤ) :
    (lowerRamificationGroup K L i).comap (AlgEquiv.restrictScalarsHom K) =
      lowerRamificationGroup M L i := by
  ext σ
  rw [Subgroup.mem_comap, AlgEquiv.restrictScalarsHom_apply, mem_lowerRamificationGroup_iff_lowerIndex,
    mem_lowerRamificationGroup_iff_lowerIndex, lowerIndex_restrictScalars]

/- English proof (translation)
Rewrite using `[← lowerRamificationGroup_comap_restrictScalars M, Subgroup.map_comap_eq, range_restrictScalarsHom, inf_comm]`.
-/
theorem lowerRamificationGroup_map_restrictScalars (i : ℤ) :
    (lowerRamificationGroup M L i).map (AlgEquiv.restrictScalarsHom K) =
      lowerRamificationGroup K L i ⊓ M.fixingSubgroup := by
  rw [← lowerRamificationGroup_comap_restrictScalars M, Subgroup.map_comap_eq,
    range_restrictScalarsHom, inf_comm]

/- English proof (translation)
Rewrite using `[lowerRamificationGroup_map_restrictScalars, IntermediateField.fixingSubgroup_fixedField]`.
-/
theorem lowerRamificationGroup_map_fixedField [IsGalois K L] (H : Subgroup (L ≃ₐ[K] L)) (i : ℤ) :
    (lowerRamificationGroup (IntermediateField.fixedField H) L i).map
        (AlgEquiv.restrictScalarsHom K) = lowerRamificationGroup K L i ⊓ H := by
  rw [lowerRamificationGroup_map_restrictScalars, IntermediateField.fixingSubgroup_fixedField]

end Subgroup

variable (K L) in

/- English proof (translation)
Rewrite using `[lowerRamificationGroup_zero]`. Conclude with `card_inertiaSubgroup K L`.
-/
theorem card_lowerRamificationGroup_zero [IsGalois K L] :
    Nat.card (lowerRamificationGroup K L 0) = ramificationIndex K L := by
  rw [lowerRamificationGroup_zero]
  exact card_inertiaSubgroup K L

end GroundTheory.LocalField
