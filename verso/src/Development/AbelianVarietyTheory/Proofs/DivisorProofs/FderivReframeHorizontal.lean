import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodVectorMoebiusTransform
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapSymplecticTransform
open Matrix MeasureTheory Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Gauge
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsionForm.ReframeHor

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem re_vecMul_ofReal (p : Fin g → ℝ) (T : Matrix (Fin g) (Fin g) ℂ) (j : Fin g) :
    (((fun i => (p i : ℂ)) ᵥ* T) j).re = (p ᵥ* T.map Complex.re) j := by
  simp [vecMul, dotProduct, Complex.re_sum]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem im_vecMul_ofReal (p : Fin g → ℝ) (T : Matrix (Fin g) (Fin g) ℂ) (j : Fin g) :
    (((fun i => (p i : ℂ)) ᵥ* T) j).im = (p ᵥ* T.map Complex.im) j := by
  simp [vecMul, dotProduct, Complex.im_sum]

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem flatOf_per_eq {T : Matrix (Fin g) (Fin g) ℂ} (h : IsUnit (T.map Complex.im).det)
    (x : Fl g) : flatOf T (per T x) = x := by
  have him : (fun i => (per T x i).im) = (fun i => x (Sum.inl i)) ᵥ* T.map Complex.im := by
    ext i; simp [per, im_vecMul_ofReal]
  have hre : (fun i => (per T x i).re) =
      (fun i => x (Sum.inl i)) ᵥ* T.map Complex.re + fun i => x (Sum.inr i) := by
    ext i; simp [per, re_vecMul_ofReal]
  have hp : ((fun i => x (Sum.inl i)) ᵥ* T.map Complex.im) ᵥ* (T.map Complex.im)⁻¹ =
      fun i => x (Sum.inl i) := by
    rw [vecMul_vecMul, mul_nonsing_inv _ h, vecMul_one]
  ext (j | j) <;> simp only [flatOf, Sum.elim_inl, Sum.elim_inr, him, hre, hp] <;> simp

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
theorem per_flatOf_eq {T : Matrix (Fin g) (Fin g) ℂ} (h : IsUnit (T.map Complex.im).det)
    (z : Fin g → ℂ) : per T (flatOf T z) = z := by
  have hp : ((fun i => (z i).im) ᵥ* (T.map Complex.im)⁻¹) ᵥ* T.map Complex.im =
      fun i => (z i).im := by
    rw [vecMul_vecMul, nonsing_inv_mul _ h, vecMul_one]
  ext i; apply Complex.ext
  · simp [per, flatOf, re_vecMul_ofReal]
  · simp [per, flatOf, im_vecMul_ofReal, hp]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isUnit_det_im {T : Matrix (Fin g) (Fin g) ℂ} (h : IsSiegel T) :
    IsUnit (T.map Complex.im).det :=
  (h.2.det_pos).ne'.isUnit

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem differentiableAt_per (σ : E → Matrix (Fin g) (Fin g) ℂ) {b₀ : E}
    (hσ : ∀ i j, DifferentiableAt ℂ (fun b => σ b i j) b₀) (x : Fl g) :
    DifferentiableAt ℂ (fun b => per (σ b) x) b₀ := by
  rw [differentiableAt_pi]
  intro j
  simp only [per, Pi.add_apply, vecMul, dotProduct]
  exact (DifferentiableAt.fun_sum fun k _ => (hσ k j).const_mul _).add (differentiableAt_const _)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem fderiv_flatCurve (σ : E → Matrix (Fin g) (Fin g) ℂ) {b₀ : E}
    (hσ : ∀ i j, DifferentiableAt ℂ (fun b => σ b i j) b₀) (x : Fl g) (v : E) :
    fderiv ℝ (fun b => ((b, per (σ b) x) : Pt E g)) b₀ v =
      (v, fderiv ℂ (fun b => per (σ b) x) b₀ v) := by
  have hd := (differentiableAt_per σ hσ x).hasFDerivAt.restrictScalars ℝ
  have h : HasFDerivAt (fun b => ((b, per (σ b) x) : Pt E g))
      ((ContinuousLinearMap.id ℝ E).prod
        ((fderiv ℂ (fun b => per (σ b) x) b₀).restrictScalars ℝ)) b₀ :=
    (hasFDerivAt_id (𝕜 := ℝ) b₀).prodMk hd
  rw [h.fderiv]
  rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem differentiableAt_flatCurve (σ : E → Matrix (Fin g) (Fin g) ℂ) {b₀ : E}
    (hσ : ∀ i j, DifferentiableAt ℂ (fun b => σ b i j) b₀) (x : Fl g) :
    DifferentiableAt ℝ (fun b => ((b, per (σ b) x) : Pt E g)) b₀ :=
  (differentiableAt_id.prodMk ((differentiableAt_per σ hσ x).restrictScalars ℝ))

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem fderiv_reframe_hor : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {g : ℕ} (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (γ : Sp g),
    IsPeriodMap B τ → IsPeriodMap B (fun b => moeb γ (τ b)) → ∀ P ∈ cov B g, ∀ v : E,
      fderiv ℝ (reframe τ γ) P (hor τ P v) =
        hor (fun b => moeb γ (τ b)) (reframe τ γ P) v := by
  intro E _ _ _ g B τ γ hτ hτ' P hP v
  obtain ⟨-, hu, hRon⟩ := GlobalTheory.SympBase.main hτ γ
  have hB : IsOpen B := hτ.1
  have hb₀ : P.1 ∈ B := hP.1
  have hcov : IsOpen (cov B g) := hB.prod isOpen_univ
  have hRd : DifferentiableAt ℝ (reframe τ γ) P :=
    ((hRon P hP).differentiableAt (hcov.mem_nhds hP)).restrictScalars ℝ
  have hσ : ∀ i j, DifferentiableAt ℂ (fun b => τ b i j) P.1 := fun i j =>
    (hτ.2.1 i j).differentiableAt (hB.mem_nhds hb₀)
  have hσ' : ∀ i j, DifferentiableAt ℂ (fun b => moeb γ (τ b) i j) P.1 := fun i j =>
    (hτ'.2.1 i j).differentiableAt (hB.mem_nhds hb₀)
  set x : Fl g := flat τ P with hx
  set y : Fl g := x ᵥ* (γ⁻¹).mat with hy
  have hP2 : per (τ P.1) x = P.2 := per_flatOf_eq (isUnit_det_im (hτ.2.2 _ hb₀)) P.2
  have hc0 : ((P.1, per (τ P.1) x) : Pt E g) = P := Prod.ext rfl hP2
  have heq : (reframe τ γ ∘ fun b => ((b, per (τ b) x) : Pt E g)) =ᶠ[𝓝 P.1]
      fun b => ((b, per (moeb γ (τ b)) y) : Pt E g) := by
    filter_upwards [hB.mem_nhds hb₀] with b hb
    simp only [Function.comp, reframe]
    rw [per_vecMul_den_inv_eq_per_moeb γ (τ b) x (hu b hb)]
  have hflat : flat (fun b => moeb γ (τ b)) (reframe τ γ P) = y := by
    simp only [flat, reframe]
    rw [← hP2, per_vecMul_den_inv_eq_per_moeb γ (τ P.1) x (hu _ hb₀)]
    exact flatOf_per_eq (isUnit_det_im (hτ'.2.2 _ hb₀)) y
  have hRd' : DifferentiableAt ℝ (reframe τ γ) ((P.1, per (τ P.1) x) : Pt E g) := by
    rw [hc0]; exact hRd
  have hcomp := fderiv_comp (𝕜 := ℝ) P.1 hRd' (differentiableAt_flatCurve τ hσ x)
  have h1 : hor τ P v = fderiv ℝ (fun b => ((b, per (τ b) x) : Pt E g)) P.1 v := by
    rw [fderiv_flatCurve τ hσ x v]; rfl
  calc fderiv ℝ (reframe τ γ) P (hor τ P v)
      = fderiv ℝ (reframe τ γ ∘ fun b => ((b, per (τ b) x) : Pt E g)) P.1 v := by
        rw [hcomp, h1, hc0]; rfl
    _ = fderiv ℝ (fun b => ((b, per (moeb γ (τ b)) y) : Pt E g)) P.1 v := by
        rw [heq.fderiv_eq]
    _ = hor (fun b => moeb γ (τ b)) (reframe τ γ P) v := by
        rw [fderiv_flatCurve _ hσ' y v]
        simp only [hor, hflat]
        rfl

end GlobalTheory.TorsionForm.ReframeHor
