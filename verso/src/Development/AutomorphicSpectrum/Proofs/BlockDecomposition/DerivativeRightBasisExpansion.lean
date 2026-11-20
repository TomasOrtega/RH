import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RwAppend

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA

namespace GlobalTheory.CompanionTheory.PresSobA.Frame

section Norm

attribute [-instance] instTopologicalSpaceMatrix

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
  Matrix.linftyOpNormedSpace

def chartM (n : ℕ) : (Fin n → Fin n → ℂ) ≃L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  (Matrix.ofLinearEquiv ℝ).toContinuousLinearEquiv

/- English proof (translation)
Establish `: CompleteSpace (Matrix (Fin n) (Fin n) ℂ)` using `FiniteDimensional.complete ℝ _`. Introduce `M hM`. Take `⟨u, hu⟩` from `hM`. Establish `h1 : ContDiffAt ℝ ∞ (Ring.inverse : Matrix (Fin n) (Fin n) ℂ → _) (chartM n M)`. Rewrite using `[← hu]`.

Conclude with `contDiffAt_ringInverse ℝ u`. Establish `h2 : ContDiffAt ℝ ∞ (fun M => (chartM n).symm (Ring.inverse (chartM n M))) M` using `(chartM n).symm.contDiff.contDiffAt.comp M (h1.comp M (chartM n).contDiff.contDiffAt)`. Conclude with `h2.contDiffWithinAt`.
-/
theorem contDiffOn_invPi (n : ℕ) :
    ContDiffOn ℝ ∞ (fun M : Fin n → Fin n → ℂ => (chartM n).symm (Ring.inverse (chartM n M)))
      {M | IsUnit (chartM n M)} := by
  have : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  intro M hM
  obtain ⟨u, hu⟩ := hM
  have h1 : ContDiffAt ℝ ∞ (Ring.inverse : Matrix (Fin n) (Fin n) ℂ → _) (chartM n M) := by
    rw [← hu]
    exact contDiffAt_ringInverse ℝ u
  have h2 : ContDiffAt ℝ ∞ (fun M => (chartM n).symm (Ring.inverse (chartM n M))) M :=
    (chartM n).symm.contDiff.contDiffAt.comp M (h1.comp M (chartM n).contDiff.contDiffAt)
  exact h2.contDiffWithinAt

end Norm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

/- English proof (translation)
Use `(contDiffOn_invPi n).mono ?_` and prove the remaining obligations. Introduce `M hM`. Conclude with `(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hM)`.
-/
theorem contDiffOn_inverse : ContDiffOn ℝ ∞ (Ring.inverse : Mat n → Mat n) (GLs n) := by
  refine (contDiffOn_invPi n).mono ?_
  intro M hM
  exact (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hM)

def mulB (n : ℕ) : CLof (Mat n) (CLof (Mat n) (Mat n)) :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
      (Mat n →ₗ[ℝ] Mat n) ≃ₗ[ℝ] CLof (Mat n) (Mat n)).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ (fun P Z : Mat n => P * Z) add_mul (fun c P Z => Matrix.smul_mul c P Z)
        mul_add (fun c P Z => Matrix.mul_smul P c Z))

def coordL (p : Bool × Fin n × Fin n) : CLof (Mat n) ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.proj p : ((Bool × Fin n × Fin n) → ℝ) →ₗ[ℝ] ℝ) ∘ₗ
      (GlobalTheory.CompanionTheory.SobGL.HaarDom.cmE n).symm.toLinearMap)

/- English proof (translation)
The claim follows from `(GlobalTheory.CompanionTheory.SobGL.HaarDom.cmE n).apply_symm_apply M`.
-/
theorem sum_coordL (M : Mat n) : ∑ p, coordL p M • bs p = M :=
  (GlobalTheory.CompanionTheory.SobGL.HaarDom.cmE n).apply_symm_apply M

def frameA (p : Bool × Fin n × Fin n) (z : Mat n) : CLof (Mat n) ℝ :=
  (coordL p).comp (mulB n (Ring.inverse z))

/- English proof (translation)
The claim follows from `((ContinuousLinearMap.compL ℝ (Mat n) (Mat n) ℝ (coordL p)).comp (mulB n)).contDiff.comp_contDiffOn contDiffOn_inverse`.
-/
theorem contDiffOn_frameA (p : Bool × Fin n × Fin n) : ContDiffOn ℝ ∞ (frameA p) (GLs n) :=
  ((ContinuousLinearMap.compL ℝ (Mat n) (Mat n) ℝ (coordL p)).comp
    (mulB n)).contDiff.comp_contDiffOn contDiffOn_inverse

/- English proof (translation)
Establish `hu : IsUnit z` using `(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hz)`. Apply `ContinuousLinearMap.ext` to reduce the goal to its premises. Introduce `v`. Establish `hv : z * (Ring.inverse z * v) = v`. Rewrite using `[← mul_assoc, Ring.mul_inverse_cancel z hu, one_mul]`.

Establish `hs` using `sum_coordL (Ring.inverse z * v)`. Establish `h0 : v = ∑ p, coordL p (Ring.inverse z * v) • (z * bs p)` using `by conv_lhs => rw [← hv, ← hs]`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun p _ => Matrix.mul_smul _ _ _`. Simplify using `only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]`.

Use `conv_lhs => rw [h0]`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun p _ => D.map_smul _ _`.
-/
theorem frame_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (D : CLof (Mat n) V)
    {z : Mat n} (hz : z ∈ GLs n) : D = ∑ p, (frameA p z).smulRight (D (z * bs p)) := by
  have hu : IsUnit z := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hz)
  apply ContinuousLinearMap.ext
  intro v
  have hv : z * (Ring.inverse z * v) = v := by
    rw [← mul_assoc, Ring.mul_inverse_cancel z hu, one_mul]
  have hs := sum_coordL (Ring.inverse z * v)
  have h0 : v = ∑ p, coordL p (Ring.inverse z * v) • (z * bs p) := by
    conv_lhs => rw [← hv, ← hs]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => Matrix.mul_smul _ _ _
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]
  conv_lhs => rw [h0]
  rw [map_sum]
  exact Finset.sum_congr rfl fun p _ => D.map_smul _ _

/- English proof (translation)
Introduce `_` and use `⟨frameA, contDiffOn_frameA, fun _ _ _ D _ hz => frame_eq D hz⟩`.
-/
theorem frame :
    ∀ n : ℕ, ∃ A : (Bool × Fin n × Fin n) → Mat n → CLof (Mat n) ℝ,
      (∀ p, ContDiffOn ℝ ∞ (A p) (GLs n)) ∧
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (D : CLof (Mat n) V), ∀ z ∈ GLs n,
        D = ∑ p, (A p z).smulRight (D (z * bs p)) :=
  fun _ => ⟨frameA, contDiffOn_frameA, fun _ _ _ D _ hz => frame_eq D hz⟩

end GlobalTheory.CompanionTheory.PresSobA.Frame
