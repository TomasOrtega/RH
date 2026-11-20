import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsSphereLaw
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory ProbabilityTheory

noncomputable section

namespace SphereLawBasic

def firstRow (N : ℕ) : (Fin 1 × Fin N → ℂ) →ₗ[ℝ] (Fin N → ℂ) where
  toFun u j := u (0, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem firstRow_apply (N : ℕ) (u : Fin 1 × Fin N → ℂ) (j : Fin N) : firstRow N u j = u (0, j) :=
  rfl

/- English proof (translation)
Use extensionality with `j`. Simplify using `[sphereNormalize, HermNorm.std_norm_eq, firstRow_apply]`.
-/
theorem sphereNormalize_eq (N : ℕ) (u : Fin 1 × Fin N → ℂ) :
    (fun j ↦ sphereNormalize (HermNorm.std N) 1 u (0, j)) =
      ((√(∑ i, ‖u (0, i)‖ ^ 2) : ℝ) : ℂ)⁻¹ • firstRow N u := by
  ext j
  simp [sphereNormalize, HermNorm.std_norm_eq, firstRow_apply]

/- English proof (translation)
Establish `h'` using `(Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ sq_nonneg ‖u (0, i)‖)).mp (le_antisymm h (Finset.sum_nonneg fun i _ ↦ sq_nonneg _))`. Use extensionality with `j`. Simplify `h' j (Finset.mem_univ j)` using `[firstRow_apply]`.
-/
theorem firstRow_eq_zero (N : ℕ) (u : Fin 1 × Fin N → ℂ) (h : ∑ i, ‖u (0, i)‖ ^ 2 ≤ 0) :
    firstRow N u = 0 := by
  have h' := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ sq_nonneg ‖u (0, i)‖)).mp
    (le_antisymm h (Finset.sum_nonneg fun i _ ↦ sq_nonneg _))
  ext j
  simpa [firstRow_apply] using h' j (Finset.mem_univ j)

/- English proof (translation)
Set `T : Submodule ℝ (Fin 1 × Fin N → ℂ)` to `(S.restrictScalars ℝ).comap (firstRow N)`. Establish `hT : T ≠ ⊤`. Introduce `h`. Apply `hS` to reduce the goal to its premises. Rewrite using `[eq_top_iff]`.

Introduce `v _`. Set `u : Fin 1 × Fin N → ℂ` to `fun ij ↦ v ij.2`. Establish `hu : u ∈ T` using `h ▸ Submodule.mem_top`. Conclude with `hu`. Conclude with `Measure.addHaar_submodule volume T hT`.
-/
theorem volume_firstRow_mem (N : ℕ) (S : Submodule ℂ (Fin N → ℂ)) (hS : S ≠ ⊤) :
    volume {u : Fin 1 × Fin N → ℂ | firstRow N u ∈ S} = 0 := by
  let T : Submodule ℝ (Fin 1 × Fin N → ℂ) := (S.restrictScalars ℝ).comap (firstRow N)
  have hT : T ≠ ⊤ := by
    intro h
    apply hS
    rw [eq_top_iff]
    intro v _
    let u : Fin 1 × Fin N → ℂ := fun ij ↦ v ij.2
    have hu : u ∈ T := h ▸ Submodule.mem_top
    exact hu
  exact Measure.addHaar_submodule volume T hT

end SphereLawBasic

open SphereLawBasic in

/- English proof (translation)
Introduce `N hN`. Establish `hf : Measurable fun (u : Fin 1 × Fin N → ℂ) (j : Fin N) ↦ sphereNormalize (HermNorm.std N) 1 u (0, j)`. Unfold `sphereNormalize`. Simplify using `only [HermNorm.std_norm_eq]`. Use `fun_prop`.

Establish `hbot : (⊥ : Submodule ℂ (Fin N → ℂ)) ≠ ⊤`. Introduce `h`. Establish `hmem : (Pi.single ⟨0, hN⟩ 1 : Fin N → ℂ) ∈ (⊥ : Submodule ℂ (Fin N → ℂ))` using `h ▸ Submodule.mem_top`. Simplify using `using congrFun ((Submodule.mem_bot ℂ).mp hmem) ⟨0, hN⟩`. Establish `h0 : ∀ᵐ u ∂(volume[|sphereBall (HermNorm.std N) 1]), firstRow N u ≠ 0`.

Use `cond_absolutelyContinuous.ae_le ?_` and prove the remaining obligations. Use `filter_upwards [measure_eq_zero_iff_ae_notMem.mp (volume_firstRow_mem N ⊥ hbot)] with u hu`. Simplify using `using hu`. Use `⟨inferInstance, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[sphereLaw, ae_map_iff hf.aemeasurable (measurableSet_eq_fun (by fun_prop) measurable_const)] filter_upwards [h0] with u hu`.

Establish `hs : 0 < ∑ i, ‖u (0, i)‖ ^ 2` using `lt_of_not_ge fun h ↦ hu (firstRow_eq_zero N u h)`. Establish `key : ∀ j, ‖sphereNormalize (HermNorm.std N) 1 u (0, j)‖ ^ 2 = (∑ i, ‖u (0, i)‖ ^ 2)⁻¹ * ‖u (0, j)‖ ^ 2`. Introduce `j`. Establish `e` using `congrFun (sphereNormalize_eq N u) j`. Rewrite using `[e]`.

Simplify using `only [Pi.smul_apply, smul_eq_mul, firstRow_apply, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow, Real.sq_sqrt hs.le]`. Simplify using `only [key, ← Finset.mul_sum]`. Conclude with `inv_mul_cancel₀ hs.ne'`. Introduce `S hS`. Establish `hSm : MeasurableSet (S : Set (Fin N → ℂ))` using `(S.restrictScalars ℝ).closed_of_finiteDimensional.measurableSet`.

Rewrite using `[sphereLaw, Measure.map_apply hf hSm]`. Use `measure_mono_null ?_ (cond_absolutelyContinuous (volume_firstRow_mem N S hS))` and prove the remaining obligations. Introduce `u hu`. Simplify using `only [Set.mem_preimage, SetLike.mem_coe] at hu`. Rewrite `hu` using `[sphereNormalize_eq]`.

Use `show firstRow N u ∈ S`. Distinguish the cases in `hc : ((√(∑ i, ‖u (0, i)‖ ^ 2) : ℝ) : ℂ) = 0`. Establish `hle : ∑ i, ‖u (0, i)‖ ^ 2 ≤ 0` using `Real.sqrt_eq_zero'.mp (by exact_mod_cast hc)`. Rewrite using `[firstRow_eq_zero N u hle]`. Conclude with `S.zero_mem`.

Use `S.smul_mem ((√(∑ i, ‖u (0, i)‖ ^ 2) : ℝ) : ℂ) hu` as an intermediate fact. Rewrite `this` using `[smul_smul, mul_inv_cancel₀ hc, one_smul]`. Then use the resulting hypothesis.
-/
theorem SphereLawBasic.proof : SphereLawBasic.Statement := by
  intro N hN
  have hf : Measurable fun (u : Fin 1 × Fin N → ℂ) (j : Fin N) ↦
      sphereNormalize (HermNorm.std N) 1 u (0, j) := by
    unfold sphereNormalize
    simp only [HermNorm.std_norm_eq]
    fun_prop
  have hbot : (⊥ : Submodule ℂ (Fin N → ℂ)) ≠ ⊤ := by
    intro h
    have hmem : (Pi.single ⟨0, hN⟩ 1 : Fin N → ℂ) ∈ (⊥ : Submodule ℂ (Fin N → ℂ)) :=
      h ▸ Submodule.mem_top
    simpa using congrFun ((Submodule.mem_bot ℂ).mp hmem) ⟨0, hN⟩
  have h0 : ∀ᵐ u ∂(volume[|sphereBall (HermNorm.std N) 1]), firstRow N u ≠ 0 := by
    refine cond_absolutelyContinuous.ae_le ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (volume_firstRow_mem N ⊥ hbot)] with u hu
    simpa using hu
  refine ⟨inferInstance, ?_, ?_⟩
  · rw [sphereLaw, ae_map_iff hf.aemeasurable (measurableSet_eq_fun (by fun_prop) measurable_const)]
    filter_upwards [h0] with u hu
    have hs : 0 < ∑ i, ‖u (0, i)‖ ^ 2 := lt_of_not_ge fun h ↦ hu (firstRow_eq_zero N u h)
    have key : ∀ j, ‖sphereNormalize (HermNorm.std N) 1 u (0, j)‖ ^ 2 =
        (∑ i, ‖u (0, i)‖ ^ 2)⁻¹ * ‖u (0, j)‖ ^ 2 := by
      intro j
      have e := congrFun (sphereNormalize_eq N u) j
      rw [e]
      simp only [Pi.smul_apply, smul_eq_mul, firstRow_apply, norm_mul, norm_inv,
        Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow,
        Real.sq_sqrt hs.le]
    simp only [key, ← Finset.mul_sum]
    exact inv_mul_cancel₀ hs.ne'
  · intro S hS
    have hSm : MeasurableSet (S : Set (Fin N → ℂ)) :=
      (S.restrictScalars ℝ).closed_of_finiteDimensional.measurableSet
    rw [sphereLaw, Measure.map_apply hf hSm]
    refine measure_mono_null ?_ (cond_absolutelyContinuous (volume_firstRow_mem N S hS))
    intro u hu
    simp only [Set.mem_preimage, SetLike.mem_coe] at hu
    rw [sphereNormalize_eq] at hu
    show firstRow N u ∈ S
    by_cases hc : ((√(∑ i, ‖u (0, i)‖ ^ 2) : ℝ) : ℂ) = 0
    · have hle : ∑ i, ‖u (0, i)‖ ^ 2 ≤ 0 := Real.sqrt_eq_zero'.mp (by exact_mod_cast hc)
      rw [firstRow_eq_zero N u hle]
      exact S.zero_mem
    · have := S.smul_mem ((√(∑ i, ‖u (0, i)‖ ^ 2) : ℝ) : ℂ) hu
      rwa [smul_smul, mul_inv_cancel₀ hc, one_smul] at this

end

end GroundTheory.Heights₂.Heights
