import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEqZeroOfHolomorphic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvatureFormVerticalRiemannStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcLogVerticalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialMixedDerivativeStatement

open Matrix GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.FlatAcyc
open scoped Real ContDiff

noncomputable section

namespace GlobalTheory.FlatHessian

/- English proof (translation)
Simplify using `[riem, flatOf, ev, Pi.single_apply, vecMul, dotProduct, apply_ite Complex.re, apply_ite Complex.im]`.
-/
theorem riem_flatOf_I {g : ℕ} (T : Matrix (Fin g) (Fin g) ℂ) (a c : Fin g) :
    riem (flatOf T (ev a)) (flatOf T (Complex.I • ev c)) = (T.map Complex.im)⁻¹ c a := by
  simp [riem, flatOf, ev, Pi.single_apply, vecMul, dotProduct, apply_ite Complex.re,
    apply_ite Complex.im]

/- English proof (translation)
Simplify using `[riem, flatOf, ev, Pi.single_apply, vecMul, dotProduct, apply_ite Complex.re, apply_ite Complex.im]`.
-/
theorem riem_flatOf_real {g : ℕ} (T : Matrix (Fin g) (Fin g) ℂ) (a c : Fin g) :
    riem (flatOf T (ev a)) (flatOf T (ev c)) = 0 := by
  simp [riem, flatOf, ev, Pi.single_apply, vecMul, dotProduct, apply_ite Complex.re,
    apply_ite Complex.im]

/- English proof (translation)
Establish `h1` using `(Complex.ofRealHom).map_adjugate Y`. Establish `h2` using `(Complex.ofRealHom).map_det Y`. Simplify using `only [RingHom.mapMatrix_apply] at h1 h2`. Establish `e : (fun t : ℝ => (t : ℂ)) = ⇑Complex.ofRealHom` using `rfl`. Rewrite using `[e, Matrix.inv_def, Matrix.inv_def, ← h1, ← h2]`.

Use extensionality with `i j`. Simplify using `[Ring.inverse_eq_inv']`.
-/
theorem inv_map_ofReal' {g : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) :
    (Y.map (fun t : ℝ => (t : ℂ)))⁻¹ = Y⁻¹.map (fun t : ℝ => (t : ℂ)) := by
  have h1 := (Complex.ofRealHom).map_adjugate Y
  have h2 := (Complex.ofRealHom).map_det Y
  simp only [RingHom.mapMatrix_apply] at h1 h2
  have e : (fun t : ℝ => (t : ℂ)) = ⇑Complex.ofRealHom := rfl
  rw [e, Matrix.inv_def, Matrix.inv_def, ← h1, ← h2]
  ext i j
  simp [Ring.inverse_eq_inv']

/- English proof (translation)
Introduce `E _ _ g B τ h hτ hh hpos hc b hb z a c`. Establish `hB : IsOpen B` using `hτ.1`. Use `set ψ : (Fin g → ℂ) → ℝ := fun z'' => Real.log (h (b, z'')) with hψdef`. Establish `hh' : ContDiff ℝ ∞ (fun z'' : Fin g → ℂ => h (b, z''))` using `hh.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun z'' => ⟨hb, trivial⟩)`. Establish `hψ : ContDiff ℝ 2 ψ` using `(hh'.log fun z'' => (hpos (b, z'') ⟨hb, trivial⟩).ne').of_le (WithTop.coe_le_coe.2 le_top)`.

Use `set Ω : (Fin g → ℂ) → (Fin g → ℂ) → ℝ := fun v w => riem (flatOf (τ b) v) (flatOf (τ b) w) with hΩdef`. Establish `hΩ : ∀ v w, fderiv ℝ (fun z' => fderiv ℝ ψ z' (Complex.I • w)) z v - fderiv ℝ (fun z' => fderiv ℝ ψ z' (Complex.I • v)) z w = 4 * π * Ω v w`. Introduce `v w`. Establish `e` using `hc (b, z) ⟨hb, trivial⟩ (0, v) (0, w)`. Rewrite `e` using `[GlobalTheory.T.ddc_log_vertical hB hh hpos hb z v w, GlobalTheory.T.curvature_form_vertical_riemann hτ hb z v w]`.

Establish `hpi : (π : ℝ) ≠ 0` using `Real.pi_ne_zero`. Rewrite using `[hΩdef]`. Simplify using `only`. Rewrite using `[← e]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Establish `key` using `GlobalTheory.T.potential_mixed_derivative ψ hψ Ω z hΩ a c`. Rewrite `key` using `[hΩdef]`. Simplify using `only [riem_flatOf_I, riem_flatOf_real] at key`. Rewrite using `[key]`.

Take `⟨_, hpd⟩` from `hτ.2.2 b hb`. Establish `hsym : ((τ b).map Complex.im)⁻¹ c a = ((τ b).map Complex.im)⁻¹ a c`. Use `hpd.isHermitian.inv.apply a c` as an intermediate fact. Simplify using `using this`. Establish `hm : imPart τ b = ((τ b).map Complex.im).map (fun t : ℝ => (t : ℂ))`.

Simplify using `[imPart, Matrix.map_map]`. Both sides reduce to the same expression. Rewrite using `[hm, inv_map_ofReal', Matrix.map_apply, hsym]`. Simplify using the standard rewrite rules.
-/
theorem dholo_dbar_log_metric : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ} {B : Set E}
    {τ : E → Matrix (Fin g) (Fin g) ℂ} {h : Pt E g → ℝ} (hτ : IsPeriodMap B τ)
    (hh : ContDiffOn ℝ ∞ h (cov B g)) (hpos : ∀ P ∈ cov B g, 0 < h P) (hc : ChernIsFlat B τ h)
    {b : E} (hb : b ∈ B) (z : Fin g → ℂ) (a c : Fin g),
    d10 (fun z' => d01 (fun z'' => (Real.log (h (b, z'')) : ℂ)) z' (ev c)) z (ev a) =
      -(π : ℂ) * (imPart τ b)⁻¹ a c := by
  intro E _ _ g B τ h hτ hh hpos hc b hb z a c
  have hB : IsOpen B := hτ.1
  set ψ : (Fin g → ℂ) → ℝ := fun z'' => Real.log (h (b, z'')) with hψdef
  have hh' : ContDiff ℝ ∞ (fun z'' : Fin g → ℂ => h (b, z'')) :=
    hh.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun z'' => ⟨hb, trivial⟩)
  have hψ : ContDiff ℝ 2 ψ :=
    (hh'.log fun z'' => (hpos (b, z'') ⟨hb, trivial⟩).ne').of_le (WithTop.coe_le_coe.2 le_top)
  set Ω : (Fin g → ℂ) → (Fin g → ℂ) → ℝ := fun v w => riem (flatOf (τ b) v) (flatOf (τ b) w)
    with hΩdef
  have hΩ : ∀ v w, fderiv ℝ (fun z' => fderiv ℝ ψ z' (Complex.I • w)) z v -
      fderiv ℝ (fun z' => fderiv ℝ ψ z' (Complex.I • v)) z w = 4 * π * Ω v w := by
    intro v w
    have e := hc (b, z) ⟨hb, trivial⟩ (0, v) (0, w)
    rw [GlobalTheory.T.ddc_log_vertical hB hh hpos hb z v w, GlobalTheory.T.curvature_form_vertical_riemann hτ hb z v w] at e
    have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    rw [hΩdef]
    simp only
    rw [← e]
    field_simp
    ring
  have key := GlobalTheory.T.potential_mixed_derivative ψ hψ Ω z hΩ a c
  rw [hΩdef] at key
  simp only [riem_flatOf_I, riem_flatOf_real] at key
  rw [key]
  obtain ⟨_, hpd⟩ := hτ.2.2 b hb
  have hsym : ((τ b).map Complex.im)⁻¹ c a = ((τ b).map Complex.im)⁻¹ a c := by
    have := hpd.isHermitian.inv.apply a c
    simpa using this
  have hm : imPart τ b = ((τ b).map Complex.im).map (fun t : ℝ => (t : ℂ)) := by
    simp [imPart, Matrix.map_map]; rfl
  rw [hm, inv_map_ofReal', Matrix.map_apply, hsym]
  simp

end GlobalTheory.FlatHessian
