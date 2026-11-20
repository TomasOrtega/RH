import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapMoebiusDenomUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvEntryDifferentiableAt
open Matrix MeasureTheory Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Gauge
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ReframeVert

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.InverseEntryDifferentiability.main`. Consider the case `exact _root_.GlobalTheory.InverseEntryDifferentiability.main`. Consider the case `(apply _root_.GlobalTheory.InverseEntryDifferentiability.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.InverseEntryDifferentiability.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.InverseEntryDifferentiability.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.InverseEntryDifferentiability.main ..)`.
-/
theorem differentiableAt_inv_apply {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] {n : Type}
    [Fintype n] [DecidableEq n] (f : F → Matrix n n ℂ) (x : F)
    (hf : ∀ i j, DifferentiableAt ℂ (fun y => f y i j) x) (hu : IsUnit (f x)) (i j : n) :
    DifferentiableAt ℂ (fun y => (f y)⁻¹ i j) x := by
  first
  | exact @_root_.GlobalTheory.InverseEntryDifferentiability.main
  | exact _root_.GlobalTheory.InverseEntryDifferentiability.main
  | (apply _root_.GlobalTheory.InverseEntryDifferentiability.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.InverseEntryDifferentiability.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InverseEntryDifferentiability.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InverseEntryDifferentiability.main ..)

/- English proof (translation)
Establish `h : ∀ k l, DifferentiableAt ℂ (fun y => τ y k l) b` using `fun k l => (hτ.2.1 k l).differentiableAt (hτ.1.mem_nhds hb)`. Simplify using `only [den, Matrix.add_apply, Matrix.mul_apply, Matrix.map_apply]`. Use `fun_prop`.
-/
theorem differentiableAt_den_apply {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}
    (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (γ : Sp g) (hτ : IsPeriodMap B τ) {b : E}
    (hb : b ∈ B) (i j : Fin g) : DifferentiableAt ℂ (fun y => den γ (τ y) i j) b := by
  have h : ∀ k l, DifferentiableAt ℂ (fun y => τ y k l) b := fun k l =>
    (hτ.2.1 k l).differentiableAt (hτ.1.mem_nhds hb)
  simp only [den, Matrix.add_apply, Matrix.mul_apply, Matrix.map_apply]
  fun_prop

end GlobalTheory.ReframeVert

namespace GlobalTheory.ReframeVert

/- English proof (translation)
Introduce `E _ _ _ g B τ γ hτ hγ P hP`. Establish `hb : P.1 ∈ B` using `hP.1`. Establish `hN : ∀ i j, DifferentiableAt ℂ (fun y => (den γ (τ y))⁻¹ i j) P.1` using `differentiableAt_inv_apply (fun y => den γ (τ y)) P.1 (differentiableAt_den_apply B τ γ hτ hb) (GlobalTheory.SiegelAction.den_isUnit_of_isPeriodMap B τ γ hγ P.1 hb)`. Establish `hD : DifferentiableAt ℂ (reframe τ γ) P`. Establish `h2 : DifferentiableAt ℂ (fun Q : Pt E g => Q.2 ᵥ* (den γ (τ Q.1))⁻¹) P`.

Rewrite using `[differentiableAt_pi]`. Introduce `c`. Simplify using `only [Matrix.vecMul, dotProduct]`. Establish `hN' : ∀ i, DifferentiableAt ℂ (fun Q : Pt E g => (den γ (τ Q.1))⁻¹ i c) P` using `fun i => (hN i c).comp P differentiableAt_fst`. Establish `hs` using `DifferentiableAt.sum (u := Finset.univ) fun i _ => (differentiableAt_pi.1 (differentiableAt_snd (𝕜 := ℂ) (p := P)) i).mul (hN' i)`.

Use `hs using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `Q`. Simplify using `[Finset.sum_apply]`. Conclude with `differentiableAt_fst.prodMk h2`. Use `⟨hD, fun a => ?_⟩` and prove the remaining obligations.

Use `set N := (den γ (τ P.1))⁻¹ with hNdef`. Establish `hline : (fun t : ℝ => reframe τ γ (P + t • vert E a)) = fun t : ℝ => (P.1, P.2 ᵥ* N + t • (Pi.single a (1 : ℂ) ᵥ* N))`. Use function extensionality and compare the values at `t`. Use extensionality with `d`. Simplify using `[reframe, vert]`.

Simplify using `[reframe, vert, hNdef, Matrix.vecMul, dotProduct, Finset.sum_add_distrib, add_mul, Finset.smul_sum, mul_assoc, Pi.single_apply]`. Establish `hder : HasLineDerivAt ℝ (reframe τ γ) ((0 : E), Pi.single a (1 : ℂ) ᵥ* N) P (vert E a)`. Unfold `HasLineDerivAt`. Rewrite using `[hline]`. Use `(hasDerivAt_const (0 : ℝ) P.1).prodMk ?_` and prove the remaining obligations.

Simplify using `using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single a (1 : ℂ) ᵥ* N)).const_add (P.2 ᵥ* N)`. Rewrite using `[← (hD.restrictScalars ℝ).lineDeriv_eq_fderiv, hder.lineDeriv]`. Use extensionality with `d`. Simplify using `[vert, Prod.fst_sum]`. Simplify using `[vert, Prod.snd_sum, Finset.sum_apply, Pi.single_apply, Matrix.vecMul, dotProduct]`.
-/
theorem reframe_vert : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g : ℕ} (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (γ : Sp g), IsPeriodMap B τ → IsPeriodMap B (fun b => moeb γ (τ b)) → ∀ P ∈ cov B g, DifferentiableAt ℂ (reframe τ γ) P ∧ ∀ a : Fin g, fderiv ℝ (reframe τ γ) P (vert E a) = ∑ c, (den γ (τ P.1))⁻¹ a c • vert E c := by
  intro E _ _ _ g B τ γ hτ hγ P hP
  have hb : P.1 ∈ B := hP.1
  have hN : ∀ i j, DifferentiableAt ℂ (fun y => (den γ (τ y))⁻¹ i j) P.1 :=
    differentiableAt_inv_apply (fun y => den γ (τ y)) P.1 (differentiableAt_den_apply B τ γ hτ hb)
      (GlobalTheory.SiegelAction.den_isUnit_of_isPeriodMap B τ γ hγ P.1 hb)
  have hD : DifferentiableAt ℂ (reframe τ γ) P := by
    have h2 : DifferentiableAt ℂ (fun Q : Pt E g => Q.2 ᵥ* (den γ (τ Q.1))⁻¹) P := by
      rw [differentiableAt_pi]
      intro c
      simp only [Matrix.vecMul, dotProduct]
      have hN' : ∀ i, DifferentiableAt ℂ (fun Q : Pt E g => (den γ (τ Q.1))⁻¹ i c) P :=
        fun i => (hN i c).comp P differentiableAt_fst
      have hs := DifferentiableAt.sum (u := Finset.univ) fun i _ =>
        (differentiableAt_pi.1 (differentiableAt_snd (𝕜 := ℂ) (p := P)) i).mul (hN' i)
      convert hs using 1
      funext Q
      simp [Finset.sum_apply]
    exact differentiableAt_fst.prodMk h2
  refine ⟨hD, fun a => ?_⟩
  set N := (den γ (τ P.1))⁻¹ with hNdef
  have hline : (fun t : ℝ => reframe τ γ (P + t • vert E a)) =
      fun t : ℝ => (P.1, P.2 ᵥ* N + t • (Pi.single a (1 : ℂ) ᵥ* N)) := by
    funext t
    ext d
    · simp [reframe, vert]
    · simp [reframe, vert, hNdef, Matrix.vecMul, dotProduct, Finset.sum_add_distrib, add_mul,
        Finset.smul_sum, mul_assoc, Pi.single_apply]
  have hder : HasLineDerivAt ℝ (reframe τ γ) ((0 : E), Pi.single a (1 : ℂ) ᵥ* N) P (vert E a) := by
    unfold HasLineDerivAt
    rw [hline]
    refine (hasDerivAt_const (0 : ℝ) P.1).prodMk ?_
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single a (1 : ℂ) ᵥ* N)).const_add (P.2 ᵥ* N)
  rw [← (hD.restrictScalars ℝ).lineDeriv_eq_fderiv, hder.lineDeriv]
  ext d
  · simp [vert, Prod.fst_sum]
  · simp [vert, Prod.snd_sum, Finset.sum_apply, Pi.single_apply, Matrix.vecMul, dotProduct]

end GlobalTheory.ReframeVert
