import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

noncomputable section
namespace GlobalTheory.TranslFlat

variable {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Use extensionality with `i`. Simplify using `[per, Matrix.vecMul, dotProduct, Finset.sum_neg_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem per_neg (τ : Matrix (Fin g) (Fin g) ℂ) (x : Fl g) : per τ (-x) = - per τ x := by
  ext i; simp [per, Matrix.vecMul, dotProduct, Finset.sum_neg_distrib]; ring

/- English proof (translation)
Simplify using `[transl, per_neg]`.
-/
theorem transl_neg_transl (τ : E → Matrix (Fin g) (Fin g) ℂ) (x : Fl g) (P : Pt E g) :
    transl τ (-x) (transl τ x P) = P := by
  simp [transl, per_neg]

/- English proof (translation)
Simplify using `[transl, per_neg]`.
-/
theorem transl_transl_neg (τ : E → Matrix (Fin g) (Fin g) ℂ) (x : Fl g) (P : Pt E g) :
    transl τ x (transl τ (-x) P) = P := by
  simp [transl, per_neg]

/- English proof (translation)
Use extensionality with `i`. Simplify using `[per, Matrix.vecMul, dotProduct, Complex.im_sum]`.
-/
theorem im_per (τ : Matrix (Fin g) (Fin g) ℂ) (x : Fl g) :
    (fun i => (per τ x i).im) = (fun i => x (Sum.inl i)) ᵥ* τ.map Complex.im := by
  ext i; simp [per, Matrix.vecMul, dotProduct, Complex.im_sum]

/- English proof (translation)
Use extensionality with `i`. Simplify using `[per, Matrix.vecMul, dotProduct, Complex.re_sum]`.
-/
theorem re_per (τ : Matrix (Fin g) (Fin g) ℂ) (x : Fl g) :
    (fun i => (per τ x i).re) = (fun i => x (Sum.inl i)) ᵥ* τ.map Complex.re + fun i => x (Sum.inr i) := by
  ext i; simp [per, Matrix.vecMul, dotProduct, Complex.re_sum]

/- English proof (translation)
Establish `hi : (fun i => (z i + per τ x i).im) = (fun i => (z i).im) + (fun i => (per τ x i).im)`. Use extensionality with `i`. Simplify using the standard rewrite rules. Establish `hinv : (τ.map Complex.im) * (τ.map Complex.im)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ h`. Establish `hp : ((fun i => x (Sum.inl i)) ᵥ* τ.map Complex.im) ᵥ* (τ.map Complex.im)⁻¹ = fun i => x (Sum.inl i)`.

Rewrite using `[Matrix.vecMul_vecMul, hinv, Matrix.vecMul_one]`. Use extensionality with `(i | i)`. Simplify using `only [flatOf, Pi.add_apply, Sum.elim_inl]`. Rewrite using `[hi, im_per, Matrix.add_vecMul, hp, Pi.add_apply]`. Simplify using `only [flatOf, Pi.add_apply, Sum.elim_inr, Pi.sub_apply]`.

Rewrite using `[hi, im_per, Matrix.add_vecMul, hp, Matrix.add_vecMul, Pi.add_apply, Complex.add_re, show (per τ x i).re = (fun i => (per τ x i).re) i from rfl, re_per]`. Simplify using `only [Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem flatOf_add_per (τ : Matrix (Fin g) (Fin g) ℂ) (h : IsUnit (τ.map Complex.im).det)
    (z : Fin g → ℂ) (x : Fl g) : flatOf τ (z + per τ x) = flatOf τ z + x := by
  have hi : (fun i => (z i + per τ x i).im) = (fun i => (z i).im) + (fun i => (per τ x i).im) := by
    ext i; simp
  have hinv : (τ.map Complex.im) * (τ.map Complex.im)⁻¹ = 1 := Matrix.mul_nonsing_inv _ h
  have hp : ((fun i => x (Sum.inl i)) ᵥ* τ.map Complex.im) ᵥ* (τ.map Complex.im)⁻¹ = fun i => x (Sum.inl i) := by
    rw [Matrix.vecMul_vecMul, hinv, Matrix.vecMul_one]
  ext (i | i)
  · simp only [flatOf, Pi.add_apply, Sum.elim_inl]
    rw [hi, im_per, Matrix.add_vecMul, hp, Pi.add_apply]
  · simp only [flatOf, Pi.add_apply, Sum.elim_inr, Pi.sub_apply]
    rw [hi, im_per, Matrix.add_vecMul, hp, Matrix.add_vecMul, Pi.add_apply, Complex.add_re,
      show (per τ x i).re = (fun i => (per τ x i).re) i from rfl, re_per]
    simp only [Pi.add_apply]
    ring

/- English proof (translation)
Establish `hd : ∀ i j, DifferentiableOn ℂ (fun P : Pt E g => τ P.1 i j) (cov B g)` using `fun i j => (hτ.2.1 i j).comp differentiableOn_fst fun P hP => hP.1`. Use `differentiableOn_fst.prodMk (differentiableOn_snd.add ?_)` and prove the remaining obligations. Rewrite using `[differentiableOn_pi]`. Introduce `i`. Simplify using `only [per, Matrix.vecMul, dotProduct, Pi.add_apply]`.

Conclude with `(DifferentiableOn.fun_sum fun j _ => (hd j i).const_mul _).add_const _`.
-/
theorem differentiableOn_transl {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}
    (hτ : IsPeriodMap B τ) (x : Fl g) : DifferentiableOn ℂ (transl τ x) (cov B g) := by
  have hd : ∀ i j, DifferentiableOn ℂ (fun P : Pt E g => τ P.1 i j) (cov B g) := fun i j =>
    (hτ.2.1 i j).comp differentiableOn_fst fun P hP => hP.1
  refine differentiableOn_fst.prodMk (differentiableOn_snd.add ?_)
  rw [differentiableOn_pi]
  intro i
  simp only [per, Matrix.vecMul, dotProduct, Pi.add_apply]
  exact (DifferentiableOn.fun_sum fun j _ => (hd j i).const_mul _).add_const _

/- English proof (translation)
The claim follows from `hB.prod isOpen_univ`.
-/
theorem isOpen_cov {B : Set E} (hB : IsOpen B) : IsOpen (cov B g) := hB.prod isOpen_univ

/- English proof (translation)
Establish `hu : IsUnit ((τ P.1).map Complex.im).det` using `(Matrix.isUnit_iff_isUnit_det _).1 (hτ.2.2 P.1 hP.1).2.isUnit`. Conclude with `flatOf_add_per _ hu _ _`.
-/
theorem flat_transl {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}
    (hτ : IsPeriodMap B τ) (x : Fl g) {P : Pt E g} (hP : P ∈ cov B g) :
    flat τ (transl τ x P) = flat τ P + x := by
  have hu : IsUnit ((τ P.1).map Complex.im).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (hτ.2.2 P.1 hP.1).2.isUnit
  exact flatOf_add_per _ hu _ _

/- English proof (translation)
Introduce `x`. Use `⟨differentiableOn_transl hτ x, fun P hP => ?_⟩` and prove the remaining obligations. Establish `ho : IsOpen (cov B g)` using `isOpen_cov hτ.1`. Establish `hTP : transl τ x P ∈ cov B g` using `⟨hP.1, Set.mem_univ _⟩`. Establish `hT : DifferentiableAt ℝ (transl τ x) P` using `((differentiableOn_transl hτ x).differentiableAt (ho.mem_nhds hP)).restrictScalars ℝ`.

Establish `hT' : DifferentiableAt ℝ (transl τ (-x)) (transl τ x P)` using `((differentiableOn_transl hτ (-x)).differentiableAt (ho.mem_nhds hTP)).restrictScalars ℝ`. Establish `hev : flat τ ∘ transl τ x =ᶠ[nhds P] fun Q => flat τ Q + x` using `Filter.eventually_of_mem (ho.mem_nhds hP) fun Q hQ => flat_transl hτ x hQ`. Establish `hcomp : fderiv ℝ (flat τ ∘ transl τ x) P = fderiv ℝ (flat τ) P`. Rewrite using `[hev.fderiv_eq, fderiv_add_const]`. Establish `key : (fderiv ℝ (flat τ) (transl τ x P)).comp (fderiv ℝ (transl τ x) P) = fderiv ℝ (flat τ) P`.

Distinguish the cases in `hf : DifferentiableAt ℝ (flat τ) (transl τ x P)`. Rewrite using `[← hcomp, fderiv_comp _ hf hT]`. Establish `hnd : ¬ DifferentiableAt ℝ (flat τ ∘ transl τ x) P`. Introduce `hc`. Apply `hf` to reduce the goal to its premises.

Establish `: DifferentiableAt ℝ ((flat τ ∘ transl τ x) ∘ transl τ (-x)) (transl τ x P)`. Apply `DifferentiableAt.comp _ _ hT'` to reduce the goal to its premises. Rewrite using `[transl_neg_transl]` and apply the resulting hypothesis. Establish `he : (flat τ ∘ transl τ x) ∘ transl τ (-x) = flat τ`. Use function extensionality and compare the values at `Q`.

Simplify using `[transl_transl_neg]`. Rewrite `this` using `[he]`. Then use the resulting hypothesis. Rewrite using `[← hcomp, fderiv_zero_of_not_differentiableAt hf, fderiv_zero_of_not_differentiableAt hnd, ContinuousLinearMap.zero_comp]`. Use extensionality with `v`. Simplify using `only [pull, om0, dflat, ContinuousAlternatingMap.compContinuousLinearMap_apply]`.

Rewrite using `[← key]`. Both sides reduce to the same expression.
-/
theorem translInv {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} (hτ : IsPeriodMap B τ) :
    ∀ x : Fl g, DifferentiableOn ℂ (transl τ x) (cov B g) ∧
      ∀ P ∈ cov B g, pull (transl τ x) (om0 τ) P = om0 τ P := by
  intro x
  refine ⟨differentiableOn_transl hτ x, fun P hP => ?_⟩
  have ho : IsOpen (cov B g) := isOpen_cov hτ.1
  have hTP : transl τ x P ∈ cov B g := ⟨hP.1, Set.mem_univ _⟩
  have hT : DifferentiableAt ℝ (transl τ x) P :=
    ((differentiableOn_transl hτ x).differentiableAt (ho.mem_nhds hP)).restrictScalars ℝ
  have hT' : DifferentiableAt ℝ (transl τ (-x)) (transl τ x P) :=
    ((differentiableOn_transl hτ (-x)).differentiableAt (ho.mem_nhds hTP)).restrictScalars ℝ
  have hev : flat τ ∘ transl τ x =ᶠ[nhds P] fun Q => flat τ Q + x :=
    Filter.eventually_of_mem (ho.mem_nhds hP) fun Q hQ => flat_transl hτ x hQ
  have hcomp : fderiv ℝ (flat τ ∘ transl τ x) P = fderiv ℝ (flat τ) P := by
    rw [hev.fderiv_eq, fderiv_add_const]
  have key : (fderiv ℝ (flat τ) (transl τ x P)).comp (fderiv ℝ (transl τ x) P) =
      fderiv ℝ (flat τ) P := by
    by_cases hf : DifferentiableAt ℝ (flat τ) (transl τ x P)
    · rw [← hcomp, fderiv_comp _ hf hT]
    · have hnd : ¬ DifferentiableAt ℝ (flat τ ∘ transl τ x) P := by
        intro hc
        apply hf
        have : DifferentiableAt ℝ ((flat τ ∘ transl τ x) ∘ transl τ (-x)) (transl τ x P) := by
          apply DifferentiableAt.comp _ _ hT'
          rwa [transl_neg_transl]
        have he : (flat τ ∘ transl τ x) ∘ transl τ (-x) = flat τ := by
          funext Q; simp [transl_transl_neg]
        rwa [he] at this
      rw [← hcomp, fderiv_zero_of_not_differentiableAt hf, fderiv_zero_of_not_differentiableAt hnd,
        ContinuousLinearMap.zero_comp]
  ext v
  simp only [pull, om0, dflat, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  rw [← key]
  rfl

/- English proof (translation)
Introduce `hτ` and use `translInv hτ`.
-/
theorem transl_holomorphic_preserves_flat_form : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ →
    ∀ x : Fl g, DifferentiableOn ℂ (transl τ x) (cov B g) ∧
      ∀ P ∈ cov B g, pull (transl τ x) (om0 τ) P = om0 τ P :=
  fun hτ => translInv hτ

end GlobalTheory.TranslFlat
