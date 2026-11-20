import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

variable {n : ℕ}

/- English proof (translation)
Establish `h : Continuous fun g : Mat n => g.det` using `continuous_id.matrix_det`. Conclude with `isOpen_ne.preimage h`.
-/
theorem isOpen_GLs_dens (n : ℕ) : IsOpen (GLs n) := by
  have h : Continuous fun g : Mat n => g.det := continuous_id.matrix_det
  exact isOpen_ne.preimage h

/- English proof (translation)
Establish `h1 : k.1 * star k.1 = 1` using `Matrix.mem_unitaryGroup_iff.1 k.2`. Establish `h2 : k.1.det ≠ 0` using `Matrix.det_ne_zero_of_right_inverse h1`. Establish `h3 : y.det ≠ 0` using `hy`. Express the relevant statement in the definitionally equal form `(y * k.1).det ≠ 0`. Rewrite using `[Matrix.det_mul]`.

Conclude with `mul_ne_zero h3 h2`.
-/
theorem mul_unitary_mem_GLs {y : Mat n} (hy : y ∈ GLs n) (k : Matrix.unitaryGroup (Fin n) ℂ) :
    y * k.1 ∈ GLs n := by
  have h1 : k.1 * star k.1 = 1 := Matrix.mem_unitaryGroup_iff.1 k.2
  have h2 : k.1.det ≠ 0 := Matrix.det_ne_zero_of_right_inverse h1
  have h3 : y.det ≠ 0 := hy
  change (y * k.1).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero h3 h2

/- English proof (translation)
Set `L : E.V →ₗᵢ[ℂ] E.V` to `⟨(E.ρ k : E.V →ₗ[ℂ] E.V), E.iso k⟩`. Establish `h1 : E.ρ k (E.ρ k⁻¹ a) = a`. Establish `: (E.ρ k * E.ρ k⁻¹) a = a`. Rewrite using `[← map_mul, mul_inv_cancel, map_one]`. Both sides reduce to the same expression.

Simplify using `using this`. Establish `h2` using `L.inner_map_map (E.ρ k⁻¹ a) v`. Establish `h3 : L (E.ρ k⁻¹ a) = a` using `h1`. Establish `h4 : L v = E.ρ k v` using `rfl`. Rewrite `h2` using `[h3, h4]`.

Conclude with `h2.symm`.
-/
theorem inner_rho_inv (E : KMod n) (k : Matrix.unitaryGroup (Fin n) ℂ) (a v : E.V) :
    ⟪E.ρ k⁻¹ a, v⟫_ℂ = ⟪a, E.ρ k v⟫_ℂ := by
  let L : E.V →ₗᵢ[ℂ] E.V := ⟨(E.ρ k : E.V →ₗ[ℂ] E.V), E.iso k⟩
  have h1 : E.ρ k (E.ρ k⁻¹ a) = a := by
    have : (E.ρ k * E.ρ k⁻¹) a = a := by
      rw [← map_mul, mul_inv_cancel, map_one]; rfl
    simpa using this
  have h2 := L.inner_map_map (E.ρ k⁻¹ a) v
  have h3 : L (E.ρ k⁻¹ a) = a := h1
  have h4 : L v = E.ρ k v := rfl
  rw [h3, h4] at h2
  exact h2.symm

/- English proof (translation)
Introduce `hK n _ _ μ _ E A hA hEq hOrth y hy`. Use `haveI : CompleteSpace E.V := FiniteDimensional.complete ℂ E.V`. Set `e : E.V` to `A y`. Set `κ : Mat n → (E.V →L[ℂ] E.V)` to `fun z => (innerSL ℂ (A z)).smulRight e`. Establish `hκ : ∀ z v, κ z v = ⟪A z, v⟫_ℂ • e` using `fun z v => by simp [κ]`.

Establish `hcont : ContinuousOn κ (GLs n)`. Establish `h1 : Continuous fun a : E.V => (innerSL ℂ a).smulRight e` using `((ContinuousLinearMap.smulRightL ℂ E.V E.V).flip e).continuous.comp (innerSL ℂ).continuous`. Conclude with `h1.comp_continuousOn hA`. Establish `hequi : ∀ z ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, κ (z * k₂.1) = κ z * E.ρ k₂`. Introduce `z hz k₂`.

Use extensionality with `v`. Rewrite using `[ContinuousLinearMap.mul_apply, hκ, hκ, hEq z hz k₂, inner_rho_inv]`. Establish `hact : ∀ f ∈ CE E, Cpt f → (∀ z ∈ GLs n, z ∉ GLs n → f z = 0) → act μ E κ f 1 = 0`. Introduce `f hf hc _`. Establish `h0` using `hOrth f hf hc`.

Unfold `act`. Simplify using `only [one_mul, hκ]`. Rewrite using `[integral_smul_const, h0, zero_smul]`. Establish `hz` using `hK n μ E κ (GLs n) (isOpen_GLs_dens n) subset_rfl (fun z hz k => mul_unitary_mem_GLs hz k) hcont hequi hact y hy`. Establish `h1 : ⟪A y, A y⟫_ℂ • e = 0`.

Rewrite using `[← hκ, hz]`. Both sides reduce to the same expression. Break down `smul_eq_zero.1 h1 with h | h` into its components or cases. Conclude with `inner_self_eq_zero.1 h`. Conclude with `h`.
-/
theorem section_orth_cpt_zero : KerUniq → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (E : KMod n) (A : Mat n → E.V), ContinuousOn A (GLs n) →
    (∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, A (y * k₂.1) = E.ρ k₂⁻¹ (A y)) →
    (∀ h ∈ CE E, Cpt h → ∫ y : G n, ⟪A y.val, h y.val⟫_ℂ ∂μ = 0) → ∀ y ∈ GLs n, A y = 0 := by
  intro hK n _ _ μ _ E A hA hEq hOrth y hy
  haveI : CompleteSpace E.V := FiniteDimensional.complete ℂ E.V
  let e : E.V := A y
  let κ : Mat n → (E.V →L[ℂ] E.V) := fun z => (innerSL ℂ (A z)).smulRight e
  have hκ : ∀ z v, κ z v = ⟪A z, v⟫_ℂ • e := fun z v => by simp [κ]
  have hcont : ContinuousOn κ (GLs n) := by
    have h1 : Continuous fun a : E.V => (innerSL ℂ a).smulRight e :=
      ((ContinuousLinearMap.smulRightL ℂ E.V E.V).flip e).continuous.comp (innerSL ℂ).continuous
    exact h1.comp_continuousOn hA
  have hequi : ∀ z ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, κ (z * k₂.1) = κ z * E.ρ k₂ := by
    intro z hz k₂
    ext v
    rw [ContinuousLinearMap.mul_apply, hκ, hκ, hEq z hz k₂, inner_rho_inv]
  have hact : ∀ f ∈ CE E, Cpt f → (∀ z ∈ GLs n, z ∉ GLs n → f z = 0) → act μ E κ f 1 = 0 := by
    intro f hf hc _
    have h0 := hOrth f hf hc
    unfold act
    simp only [one_mul, hκ]
    rw [integral_smul_const, h0, zero_smul]
  have hz := hK n μ E κ (GLs n) (isOpen_GLs_dens n) subset_rfl
    (fun z hz k => mul_unitary_mem_GLs hz k) hcont hequi hact y hy
  have h1 : ⟪A y, A y⟫_ℂ • e = 0 := by
    rw [← hκ, hz]; rfl
  rcases smul_eq_zero.1 h1 with h | h
  · exact inner_self_eq_zero.1 h
  · exact h

end GlobalTheory.CompanionTheory.WaveMult
