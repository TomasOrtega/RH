import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.DSurjDef

noncomputable section

namespace PI.CntNotIntW

open scoped TensorProduct
open ValuativeRel

/- English proof (translation)
Establish `: T0Space Fp`. Use `⟨fun x y hxy => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `hv : valuation Fp (y - x) ≠ 0` using `(valuation Fp).ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm hne))`. Establish `hs : {z : Fp | z ≠ y} ∈ nhds x`.

Rewrite using `[IsValuativeTopology.mem_nhds_iff]`. Use `⟨Units.mk0 _ hv, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨z, hz, rfl⟩ h`. Establish `h' : x + z = y` using `h`. Establish `hz' : valuation Fp z < valuation Fp (y - x)` using `hz`.

Establish `hzy : z = y - x` using `by rw [← h']; ring`. Rewrite `hz'` using `[hzy]`. Conclude with `lt_irrefl _ hz'`. Rewrite `hs` using `[hxy.nhds_eq]`. Conclude with `(mem_of_mem_nhds hs : y ≠ y) rfl`.

Use `infer_instance`.
-/
theorem t2Space_of_nonarchimedeanLocalField' (Fp : Type) [Field Fp] [ValuativeRel Fp] [TopologicalSpace Fp] [IsNonarchimedeanLocalField Fp] :
    T2Space Fp := by
  have : T0Space Fp := by
    refine ⟨fun x y hxy => ?_⟩
    by_contra hne
    have hv : valuation Fp (y - x) ≠ 0 :=
      (valuation Fp).ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm hne))
    have hs : {z : Fp | z ≠ y} ∈ nhds x := by
      rw [IsValuativeTopology.mem_nhds_iff]
      refine ⟨Units.mk0 _ hv, ?_⟩
      rintro _ ⟨z, hz, rfl⟩ h
      have h' : x + z = y := h
      have hz' : valuation Fp z < valuation Fp (y - x) := hz
      have hzy : z = y - x := by rw [← h']; ring
      rw [hzy] at hz'
      exact lt_irrefl _ hz'
    rw [hxy.nhds_eq] at hs
    exact (mem_of_mem_nhds hs : y ≠ y) rfl
  infer_instance

/- English proof (translation)
Unfold `PiSurj`. Introduce `K _ _ ℓ _ Fp _ _ _ _ _ _ hcont hfin ι hdense`. Establish `: T2Space Fp` using `t2Space_of_nonarchimedeanLocalField' Fp`. Establish `: FiniteDimensional ℚ_[ℓ] Fp` using `hfin`. Establish `: ContinuousSMul ℚ_[ℓ] Fp`.

Prove the components needed by the constructor for the conclusion. Establish `h : (fun p : ℚ_[ℓ] × Fp => p.1 • p.2) = fun p => algebraMap ℚ_[ℓ] Fp p.1 * p.2`. Use function extensionality and compare the values at `p`. Conclude with `Algebra.smul_def _ _`. Rewrite using `[h]`.

Conclude with `(hcont.comp continuous_fst).mul continuous_snd`. Set `S : Submodule ℚ_[ℓ] Fp` to `LinearMap.range (piMap K ℓ Fp ι).toLinearMap`. Establish `hS : IsClosed (S : Set Fp)` using `S.closed_of_finiteDimensional`. Establish `hsub : Set.range ι ⊆ (S : Set Fp)`. Introduce and unpack `_ ⟨y, rfl⟩`.

Conclude with `⟨1 ⊗ₜ y, piMap_one_tmul K ℓ Fp ι y⟩`. Introduce `z`. Take `⟨w, hw⟩` from `closure_minimal hsub hS (hdense z)`. Conclude with `⟨w, hw⟩`.
-/
theorem tensorLiftSurjective : PiSurj := by
  unfold PiSurj
  intro K _ _ ℓ _ Fp _ _ _ _ _ _ hcont hfin ι hdense
  have : T2Space Fp := t2Space_of_nonarchimedeanLocalField' Fp
  have : FiniteDimensional ℚ_[ℓ] Fp := hfin
  have : ContinuousSMul ℚ_[ℓ] Fp := by
    constructor
    have h : (fun p : ℚ_[ℓ] × Fp => p.1 • p.2) = fun p => algebraMap ℚ_[ℓ] Fp p.1 * p.2 := by
      funext p
      exact Algebra.smul_def _ _
    rw [h]
    exact (hcont.comp continuous_fst).mul continuous_snd
  let S : Submodule ℚ_[ℓ] Fp := LinearMap.range (piMap K ℓ Fp ι).toLinearMap
  have hS : IsClosed (S : Set Fp) := S.closed_of_finiteDimensional
  have hsub : Set.range ι ⊆ (S : Set Fp) := by
    rintro _ ⟨y, rfl⟩
    exact ⟨1 ⊗ₜ y, piMap_one_tmul K ℓ Fp ι y⟩
  intro z
  obtain ⟨w, hw⟩ := closure_minimal hsub hS (hdense z)
  exact ⟨w, hw⟩

end PI.CntNotIntW
