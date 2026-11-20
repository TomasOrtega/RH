import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableFh
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.UnipotentTateFunctionalEquation

noncomputable section

open MeasureTheory Matrix Filter Topology
open Ad3 Ad3.K Ad3.K.LC Ad3.K.LC.C GlobalTheory.CompanionTheory.PuBndC

namespace GlobalTheory.CompanionTheory.PuBndC.RowSwap

def rowSwap (h : M22) : M22 := fun i => h (Equiv.swap 0 1 i)

/- English proof (translation)
Simplify using `[rowSwap]`.
-/
@[simp] theorem rowSwap_zero (h : M22) : rowSwap h 0 = h 1 := by simp [rowSwap]

/- English proof (translation)
Simplify using `[rowSwap]`.
-/
@[simp] theorem rowSwap_one (h : M22) : rowSwap h 1 = h 0 := by simp [rowSwap]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[rowSwap]`.
-/
theorem rowSwap_rowSwap (h : M22) : rowSwap (rowSwap h) = h := by
  funext i
  simp [rowSwap]

/- English proof (translation)
Establish `hm` using `volume_measurePreserving_piCongrLeft (fun _ : Fin 2 => Fin 2 → ℂ) (Equiv.swap (0 : Fin 2) 1)`. Establish `e : (⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin 2 => Fin 2 → ℂ) (Equiv.swap (0 : Fin 2) 1)) : M22 → M22) = rowSwap`. Use function extensionality and compare the values at `h i`. Simplify using `only [MeasurableEquiv.piCongrLeft, MeasurableEquiv.coe_mk, Equiv.piCongrLeft_apply, rowSwap, Equiv.symm_swap]`. Conclude with `eq_rec_constant _ _`.

Rewrite using `[← e]`. Conclude with `hm`.
-/
theorem measurePreserving_rowSwap : MeasurePreserving rowSwap (volume : Measure M22) volume := by
  have hm := volume_measurePreserving_piCongrLeft (fun _ : Fin 2 => Fin 2 → ℂ) (Equiv.swap (0 : Fin 2) 1)
  have e : (⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin 2 => Fin 2 → ℂ) (Equiv.swap (0 : Fin 2) 1)) : M22 → M22) = rowSwap := by
    funext h i
    simp only [MeasurableEquiv.piCongrLeft, MeasurableEquiv.coe_mk, Equiv.piCongrLeft_apply, rowSwap, Equiv.symm_swap]
    exact eq_rec_constant _ _
  rw [← e]
  exact hm

def rowSwapEquiv : M22 ≃ᵐ M22 where
  toFun := rowSwap
  invFun := rowSwap
  left_inv := rowSwap_rowSwap
  right_inv := rowSwap_rowSwap
  measurable_toFun := measurePreserving_rowSwap.measurable
  measurable_invFun := measurePreserving_rowSwap.measurable

/- English proof (translation)
Simplify using `[rr, add_comm]`.
-/
theorem rr_rowSwap (h : M22) : rr (rowSwap h) = rr h := by
  simp [rr, add_comm]

/- English proof (translation)
Unfold `dd`. Simplify using `only [Matrix.det_fin_two, Matrix.of_apply, rowSwap_zero, rowSwap_one]`. Rewrite using `[← norm_neg]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dd_rowSwap (h : M22) : dd (rowSwap h) = dd h := by
  unfold dd
  simp only [Matrix.det_fin_two, Matrix.of_apply, rowSwap_zero, rowSwap_one]
  rw [← norm_neg]
  congr 1
  ring

/- English proof (translation)
Simplify using `[yy, rr_rowSwap, dd_rowSwap]`.
-/
theorem yy_rowSwap (h : M22) : yy (rowSwap h) = yy h := by
  simp [yy, rr_rowSwap, dd_rowSwap]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Conclude with `(pi_norm_le_iff_of_nonneg (norm_nonneg h)).2 fun i => norm_le_pi_norm h _`. Use `(pi_norm_le_iff_of_nonneg (norm_nonneg (rowSwap h))).2 fun i => ?_` and prove the remaining obligations. Use `norm_le_pi_norm (rowSwap h) (Equiv.swap 0 1 i)` as an intermediate fact. Simplify `this` using `[rowSwap]`.
-/
theorem norm_rowSwap (h : M22) : ‖rowSwap h‖ = ‖h‖ := by
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg h)).2 fun i => norm_le_pi_norm h _
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg (rowSwap h))).2 fun i => ?_
    have := norm_le_pi_norm (rowSwap h) (Equiv.swap 0 1 i)
    simpa [rowSwap] using this

/- English proof (translation)
Simplify using `only [Fh, rr_rowSwap, dd_rowSwap, yy_rowSwap, norm_rowSwap]`.
-/
theorem Fh_rowSwap (σ : ℝ) (h : M22) : Fh σ (rowSwap h) = Fh σ h := by
  simp only [Fh, rr_rowSwap, dd_rowSwap, yy_rowSwap, norm_rowSwap]

/- English proof (translation)
Introduce `σ hS`. Establish `h2 : IntegrableOn (Fh σ ∘ rowSwap) (rowSwap ⁻¹' {h : M22 | ‖h 1 0‖ ≤ ‖h 0 0‖})` using `(measurePreserving_rowSwap.integrableOn_comp_preimage rowSwapEquiv.measurableEmbedding).2 hS`. Establish `e : Fh σ ∘ rowSwap = Fh σ` using `funext (Fh_rowSwap σ)`. Rewrite `h2` using `[e]`. Establish `hu : {h : M22 | ‖h 1 0‖ ≤ ‖h 0 0‖} ∪ rowSwap ⁻¹' {h : M22 | ‖h 1 0‖ ≤ ‖h 0 0‖} = Set.univ`.

Use extensionality with `h`. Simplify using `using le_total ‖h 1 0‖ ‖h 0 0‖`. Use `hS.union h2` as an intermediate fact. Rewrite `this` using `[hu]`. Conclude with `integrableOn_univ.1 this`.
-/
theorem integrable_Fh_of_half : ∀ σ : ℝ, IntegrableOn (Fh σ) {h : M22 | ‖h 1 0‖ ≤ ‖h 0 0‖} → Integrable (Fh σ) := by
  intro σ hS
  have h2 : IntegrableOn (Fh σ ∘ rowSwap) (rowSwap ⁻¹' {h : M22 | ‖h 1 0‖ ≤ ‖h 0 0‖}) :=
    (measurePreserving_rowSwap.integrableOn_comp_preimage rowSwapEquiv.measurableEmbedding).2 hS
  have e : Fh σ ∘ rowSwap = Fh σ := funext (Fh_rowSwap σ)
  rw [e] at h2
  have hu : {h : M22 | ‖h 1 0‖ ≤ ‖h 0 0‖} ∪ rowSwap ⁻¹' {h : M22 | ‖h 1 0‖ ≤ ‖h 0 0‖} = Set.univ := by
    ext h
    simpa using le_total ‖h 1 0‖ ‖h 0 0‖
  have := hS.union h2
  rw [hu] at this
  exact integrableOn_univ.1 this

end GlobalTheory.CompanionTheory.PuBndC.RowSwap
