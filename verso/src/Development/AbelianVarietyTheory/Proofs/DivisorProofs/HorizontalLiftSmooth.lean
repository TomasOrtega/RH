import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFormSmoothOnCover
open Matrix Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Pullback
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HorSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g : ℕ}
  {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}

/- English proof (translation)
The claim follows from `(GlobalTheory.FlatSmooth.analyticOnNhd_of_differentiableOn hτ.1 (hτ.2.1 i j)).contDiffOn hτ.1.uniqueDiffOn`.
-/
theorem contDiffOn_tau_C (hτ : IsPeriodMap B τ) (i j : Fin g) :
    ContDiffOn ℂ ∞ (fun b => τ b i j) B :=
  (GlobalTheory.FlatSmooth.analyticOnNhd_of_differentiableOn hτ.1 (hτ.2.1 i j)).contDiffOn hτ.1.uniqueDiffOn

/- English proof (translation)
The claim follows from `(contDiffOn_pi.1 (GlobalTheory.FlatSmooth.contDiffOn_flat hτ)) (Sum.inl i)`.
-/
theorem contDiffOn_flat_inl (hτ : IsPeriodMap B τ) (i : Fin g) :
    ContDiffOn ℝ ∞ (fun P : Pt E g => flat τ P (Sum.inl i)) (cov B g) :=
  (contDiffOn_pi.1 (GlobalTheory.FlatSmooth.contDiffOn_flat hτ)) (Sum.inl i)

/- English proof (translation)
Establish `hd : ∀ i j, DifferentiableAt ℂ (fun b' => τ b' i j) b` using `fun i j => (hτ.2.1 i j).differentiableAt (hτ.1.mem_nhds hb)`. Establish `hH : HasFDerivAt (fun b' => per (τ b') x) (ContinuousLinearMap.pi fun j => ∑ i, (x (Sum.inl i) : ℂ) • fderiv ℂ (fun b' => τ b' i j) b) b`. Use `hasFDerivAt_pi.2 fun j => ?_` and prove the remaining obligations. Establish `: (fun b' => per (τ b') x j) = fun b' => (∑ i, (x (Sum.inl i) : ℂ) * τ b' i j) + (x (Sum.inr j) : ℂ)`. Use function extensionality and compare the values at `b'`.

Simplify using `[per, Matrix.vecMul, dotProduct]`. Rewrite using `[this]`. Use `(HasFDerivAt.fun_sum fun i _ => ?_).add_const _` and prove the remaining obligations. Conclude with `(hd i j).hasFDerivAt.const_mul _`. Rewrite using `[hH.fderiv]`.

Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules.
-/
theorem fderiv_per (hτ : IsPeriodMap B τ) {b : E} (hb : b ∈ B) (x : Fl g) (v : E) :
    fderiv ℂ (fun b' => per (τ b') x) b v =
      fun j => ∑ i, (x (Sum.inl i) : ℂ) * fderiv ℂ (fun b' => τ b' i j) b v := by
  have hd : ∀ i j, DifferentiableAt ℂ (fun b' => τ b' i j) b := fun i j =>
    (hτ.2.1 i j).differentiableAt (hτ.1.mem_nhds hb)
  have hH : HasFDerivAt (fun b' => per (τ b') x)
      (ContinuousLinearMap.pi fun j =>
        ∑ i, (x (Sum.inl i) : ℂ) • fderiv ℂ (fun b' => τ b' i j) b) b := by
    refine hasFDerivAt_pi.2 fun j => ?_
    have : (fun b' => per (τ b') x j) =
        fun b' => (∑ i, (x (Sum.inl i) : ℂ) * τ b' i j) + (x (Sum.inr j) : ℂ) := by
      funext b'
      simp [per, Matrix.vecMul, dotProduct]
    rw [this]
    refine (HasFDerivAt.fun_sum fun i _ => ?_).add_const _
    exact (hd i j).hasFDerivAt.const_mul _
  rw [hH.fderiv]
  funext j
  simp

/- English proof (translation)
Introduce `E _ _ _ g B τ hτ v`. Establish `hdv : ∀ i j, ContDiffOn ℝ ∞ (fun P : Pt E g => fderiv ℂ (fun b' => τ b' i j) P.1 v) (cov B g)` using `fun i j => by`. Establish `h1 : ContDiffOn ℂ ∞ (fun b => fderiv ℂ (fun b' => τ b' i j) b) B` using `(contDiffOn_tau_C hτ i j).fderiv_of_isOpen hτ.1 (by simp)`. Establish `h2 : ContDiffOn ℂ ∞ (fun b => fderiv ℂ (fun b' => τ b' i j) b v) B` using `h1.clm_apply contDiffOn_const`. Conclude with `(h2.restrict_scalars ℝ).comp contDiff_fst.contDiffOn fun P (hP : P ∈ cov B g) => hP.1`.

Establish `hF : ContDiffOn ℝ ∞ (fun Q : Pt E g => ((v : E), fun j => ∑ i, ((flat τ Q (Sum.inl i) : ℝ) : ℂ) * fderiv ℂ (fun b' => τ b' i j) Q.1 v)) (cov B g)`. Use `contDiffOn_const.prodMk (contDiffOn_pi.2 fun j => ContDiffOn.sum fun i _ => ?_)` and prove the remaining obligations. Conclude with `(Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_flat_inl hτ i)).mul (hdv i j)`. Use `hF.congr fun Q hQ => ?_` and prove the remaining obligations. Simplify using `only [hor]`.

Rewrite using `[fderiv_per hτ hQ.1]`.
-/
theorem horSmooth : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {g : ℕ} (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ), IsPeriodMap B τ →
    ∀ v : E, ContDiffOn ℝ ∞ (fun Q : Pt E g => hor τ Q v) (cov B g) := by
  intro E _ _ _ g B τ hτ v
  have hdv : ∀ i j, ContDiffOn ℝ ∞ (fun P : Pt E g => fderiv ℂ (fun b' => τ b' i j) P.1 v)
      (cov B g) := fun i j => by
    have h1 : ContDiffOn ℂ ∞ (fun b => fderiv ℂ (fun b' => τ b' i j) b) B :=
      (contDiffOn_tau_C hτ i j).fderiv_of_isOpen hτ.1 (by simp)
    have h2 : ContDiffOn ℂ ∞ (fun b => fderiv ℂ (fun b' => τ b' i j) b v) B :=
      h1.clm_apply contDiffOn_const
    exact (h2.restrict_scalars ℝ).comp contDiff_fst.contDiffOn fun P (hP : P ∈ cov B g) => hP.1
  have hF : ContDiffOn ℝ ∞ (fun Q : Pt E g => ((v : E), fun j =>
      ∑ i, ((flat τ Q (Sum.inl i) : ℝ) : ℂ) * fderiv ℂ (fun b' => τ b' i j) Q.1 v)) (cov B g) := by
    refine contDiffOn_const.prodMk (contDiffOn_pi.2 fun j => ContDiffOn.sum fun i _ => ?_)
    exact (Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_flat_inl hτ i)).mul (hdv i j)
  refine hF.congr fun Q hQ => ?_
  simp only [hor]
  rw [fderiv_per hτ hQ.1]

end GlobalTheory.HorSmooth
