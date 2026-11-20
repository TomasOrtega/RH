import Mathlib
import GroundTheory.LocalFields.LocalArtinBaseChange
import GroundTheory.LocalFields.LocalArtinTransport

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel

section Valuation

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/- English proof (translation)
Rewrite using `[vle_iff_spectralNorm_le (K := K), vle_iff_spectralNorm_le (K := K)]`. Simplify using `only [spectralNorm, minpoly.algEquiv_eq]`.
-/
theorem vle_algEquiv_apply_iff {L L' : Type*} [Field L] [Field L'] [Algebra K L] [Algebra K L']
    [Algebra.IsAlgebraic K L] [Algebra.IsAlgebraic K L'] [ValuativeRel L] [ValuativeRel L']
    [ValuativeExtension K L] [ValuativeExtension K L'] (e : L ≃ₐ[K] L') (x y : L) :
    e x ≤ᵥ e y ↔ x ≤ᵥ y := by
  rw [vle_iff_spectralNorm_le (K := K), vle_iff_spectralNorm_le (K := K)]
  simp only [spectralNorm, minpoly.algEquiv_eq]

end Valuation

section Conjugation

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]
  (E : IntermediateField K Ω) [FiniteDimensional K E] (σ : Ω ≃ₐ[K] Ω)

instance finiteDimensional_map_algEquiv :
    FiniteDimensional K (E.map (σ : Ω →ₐ[K] Ω)) :=
  LinearEquiv.finiteDimensional (IntermediateField.equivMap E (σ : Ω →ₐ[K] Ω)).toLinearEquiv

/- English proof (translation)
The claim follows from `transport_localArtinMap_apply (IntermediateField.equivMap E (σ : Ω →ₐ[K] Ω)).toRingEquiv (fun a b => vle_algEquiv_apply_iff (IntermediateField.equivMap E (σ : Ω →ₐ[K] Ω)) a b) σ.toRingEquiv (fun _ => rfl) x hy`.
-/
theorem localArtinMap_conj_apply (x : Eˣ) {y : Ω} (hy : y ∈ maximalAbelianExtension E Ω) :
    σ ((localArtinMap E Ω x ⟨y, hy⟩ : maximalAbelianExtension E Ω) : Ω) =
      ((localArtinMap (E.map (σ : Ω →ₐ[K] Ω)) Ω
        (Units.map (IntermediateField.equivMap E (σ : Ω →ₐ[K] Ω)).toRingEquiv.toRingHom.toMonoidHom x)
          ⟨σ y, (mem_maximalAbelianExtension_transport_iff
            (IntermediateField.equivMap E (σ : Ω →ₐ[K] Ω)).toRingEquiv σ.toRingEquiv
            (fun _ => rfl)).2 hy⟩ : maximalAbelianExtension (E.map (σ : Ω →ₐ[K] Ω)) Ω) : Ω) :=
  transport_localArtinMap_apply (IntermediateField.equivMap E (σ : Ω →ₐ[K] Ω)).toRingEquiv
    (fun a b => vle_algEquiv_apply_iff (IntermediateField.equivMap E (σ : Ω →ₐ[K] Ω)) a b)
    σ.toRingEquiv (fun _ => rfl) x hy

end Conjugation

section Finite

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {K' : Type*} [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']
  [Algebra K K'] [ValuativeExtension K K'] [FiniteDimensional K K']
  {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra K' Ω] [IsScalarTower K K' Ω]
  [IsSepClosure K Ω] [IsSepClosure K' Ω]

omit [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K'] [ValuativeExtension K K'] in

/- English proof (translation)
Set `` to `algebraicValuativeRel K Ω`. Set `` to `algebraicTopology K Ω`. Use `algebraicValuativeRel_valuativeExtension K Ω` as an intermediate fact. Use `algebraicTopology_isValuativeTopology K Ω` as an intermediate fact. Use `set ι := IsScalarTower.toAlgHom K K' Ω`.

Establish `: FiniteDimensional K ι.fieldRange` using `LinearEquiv.finiteDimensional (AlgHom.equivFieldRange ι).toLinearEquiv`. Conclude with `(mem_maximalAbelianExtension_transport_iff (AlgHom.equivFieldRange ι).toRingEquiv (RingEquiv.refl Ω) (fun _ => rfl)).1 (maximalAbelianExtension_le_restrictScalars ι.fieldRange hy)`.
-/
theorem maximalAbelianExtension_le_of_algebra {y : Ω} (hy : y ∈ maximalAbelianExtension K Ω) :
    y ∈ maximalAbelianExtension K' Ω := by
  let := algebraicValuativeRel K Ω
  let := algebraicTopology K Ω
  have := algebraicValuativeRel_valuativeExtension K Ω
  have := algebraicTopology_isValuativeTopology K Ω
  set ι := IsScalarTower.toAlgHom K K' Ω
  have : FiniteDimensional K ι.fieldRange :=
    LinearEquiv.finiteDimensional (AlgHom.equivFieldRange ι).toLinearEquiv
  exact (mem_maximalAbelianExtension_transport_iff (AlgHom.equivFieldRange ι).toRingEquiv
    (RingEquiv.refl Ω) (fun _ => rfl)).1 (maximalAbelianExtension_le_restrictScalars ι.fieldRange hy)

/- English proof (translation)
Set `` to `algebraicValuativeRel K Ω`. Set `` to `algebraicTopology K Ω`. Use `algebraicValuativeRel_valuativeExtension K Ω` as an intermediate fact. Use `algebraicTopology_isValuativeTopology K Ω` as an intermediate fact. Use `set ι := IsScalarTower.toAlgHom K K' Ω`.

Establish `: FiniteDimensional K ι.fieldRange` using `LinearEquiv.finiteDimensional (AlgHom.equivFieldRange ι).toLinearEquiv`. Use `set e := AlgHom.equivFieldRange ι`. Establish `he : ∀ a b : K', e a ≤ᵥ e b ↔ a ≤ᵥ b` using `vle_algEquiv_apply_iff e`. Establish `h1` using `transport_localArtinMap_apply e.toRingEquiv he (RingEquiv.refl Ω) (fun _ => rfl) x (maximalAbelianExtension_le_of_algebra hy)`. Simplify using `only [RingEquiv.refl_apply] at h1`.

Rewrite using `[h1, localArtinMap_apply_of_mem ι.fieldRange _ hy]`. Use `congr 3`. Use `ext`. Rewrite using `[coe_normUnits, coe_normUnits]`. Conclude with `Algebra.norm_eq_of_algEquiv e x`.
-/
theorem localArtinMap_apply_of_algebra (x : K'ˣ) {y : Ω} (hy : y ∈ maximalAbelianExtension K Ω) :
    ((localArtinMap K' Ω x ⟨y, maximalAbelianExtension_le_of_algebra hy⟩ :
      maximalAbelianExtension K' Ω) : Ω) =
      ((localArtinMap K Ω (normUnits K K' x) ⟨y, hy⟩ : maximalAbelianExtension K Ω) : Ω) := by
  let := algebraicValuativeRel K Ω
  let := algebraicTopology K Ω
  have := algebraicValuativeRel_valuativeExtension K Ω
  have := algebraicTopology_isValuativeTopology K Ω
  set ι := IsScalarTower.toAlgHom K K' Ω
  have : FiniteDimensional K ι.fieldRange :=
    LinearEquiv.finiteDimensional (AlgHom.equivFieldRange ι).toLinearEquiv
  set e := AlgHom.equivFieldRange ι
  have he : ∀ a b : K', e a ≤ᵥ e b ↔ a ≤ᵥ b := vle_algEquiv_apply_iff e
  have h1 := transport_localArtinMap_apply e.toRingEquiv he (RingEquiv.refl Ω) (fun _ => rfl) x
    (maximalAbelianExtension_le_of_algebra hy)
  simp only [RingEquiv.refl_apply] at h1
  rw [h1, localArtinMap_apply_of_mem ι.fieldRange _ hy]
  congr 3
  ext
  rw [coe_normUnits, coe_normUnits]
  exact Algebra.norm_eq_of_algEquiv e x

end Finite

end GroundTheory.LocalField
