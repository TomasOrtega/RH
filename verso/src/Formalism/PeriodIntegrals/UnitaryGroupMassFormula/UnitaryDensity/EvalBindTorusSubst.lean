import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryDensity.GramStep

open Matrix MvPolynomial
open scoped ComplexOrder

namespace PI.UD

/- English proof (translation)
Use `Set.Infinite.of_image Complex.re ((Set.Icc_infinite (by norm_num : (-1 : ℝ) < 1)).mono ?_)` and prove the remaining obligations. Introduce `x hx`. Establish `h1 : 0 ≤ 1 - x ^ 2` using `by nlinarith [hx.1, hx.2]`. Use `⟨⟨x, Real.sqrt (1 - x ^ 2)⟩, ?_, rfl⟩` and prove the remaining obligations. Use `show ‖(⟨x, Real.sqrt (1 - x ^ 2)⟩ : ℂ)‖ = 1`.

Rewrite using `[Complex.norm_def, Complex.normSq_mk, Real.mul_self_sqrt h1]`. Simplify using `[sq]`.
-/
theorem circle_infinite : {z : ℂ | ‖z‖ = 1}.Infinite := by
  refine Set.Infinite.of_image Complex.re
    ((Set.Icc_infinite (by norm_num : (-1 : ℝ) < 1)).mono ?_)
  intro x hx
  have h1 : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  refine ⟨⟨x, Real.sqrt (1 - x ^ 2)⟩, ?_, rfl⟩
  show ‖(⟨x, Real.sqrt (1 - x ^ 2)⟩ : ℂ)‖ = 1
  rw [Complex.norm_def, Complex.normSq_mk, Real.mul_self_sqrt h1]
  simp [sq]

/- English proof (translation)
The claim follows from `MvPolynomial.funext_set (fun _ => {z : ℂ | ‖z‖ = 1}) (fun _ => circle_infinite) fun t ht => by simpa using h t fun i => ht i (Set.mem_univ i)`.
-/
theorem eq_zero_of_torus {σ : Type*} (R : MvPolynomial σ ℂ)
    (h : ∀ t : σ → ℂ, (∀ i, ‖t i‖ = 1) → eval t R = 0) : R = 0 :=
  MvPolynomial.funext_set (fun _ => {z : ℂ | ‖z‖ = 1}) (fun _ => circle_infinite)
    fun t ht => by simpa using h t fun i => ht i (Set.mem_univ i)

noncomputable def torusSubst {ι : Type} {n : ℕ} (w v : ι → Matrix (Fin n) (Fin n) ℂ) :
    ι × Fin n × Fin n → MvPolynomial (ι × Fin n) ℂ :=
  fun x => ∑ k, C (w x.1 x.2.1 k) * X (x.1, k) * C (v x.1 k x.2.2)

/- English proof (translation)
Use `(eval₂Hom_bind₁ (RingHom.id ℂ) t (torusSubst w v) P).trans (congrArg (fun f => eval f P) (funext fun x => ?_))` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply]`. Simplify using `[torusSubst, Matrix.mul_diagonal]`.
-/
theorem eval_bind_torusSubst {ι : Type} {n : ℕ} (w v : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) (t : ι × Fin n → ℂ) :
    eval t (bind₁ (torusSubst w v) P) =
      eval (fun x : ι × Fin n × Fin n =>
        (w x.1 * diagonal (fun k => t (x.1, k)) * v x.1) x.2.1 x.2.2) P := by
  refine (eval₂Hom_bind₁ (RingHom.id ℂ) t (torusSubst w v) P).trans
    (congrArg (fun f => eval f P) (funext fun x => ?_))
  rw [Matrix.mul_apply]
  simp [torusSubst, Matrix.mul_diagonal]

noncomputable def leftSubst {ι : Type} {n : ℕ} (A : ι → Matrix (Fin n) (Fin n) ℂ) :
    ι × Fin n × Fin n → MvPolynomial (ι × Fin n × Fin n) ℂ :=
  fun x => ∑ k, C (A x.1 x.2.1 k) * X (x.1, k, x.2.2)

/- English proof (translation)
Use `(eval₂Hom_bind₁ (RingHom.id ℂ) _ (leftSubst A) P).trans (congrArg (fun f => eval f P) (funext fun x => ?_))` and prove the remaining obligations. Simplify using `[leftSubst, Matrix.mul_apply]`.
-/
theorem eval_bind_leftSubst {ι : Type} {n : ℕ} (A : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) (u : ι → Matrix (Fin n) (Fin n) ℂ) :
    eval (fun x : ι × Fin n × Fin n => u x.1 x.2.1 x.2.2) (bind₁ (leftSubst A) P) =
      eval (fun x : ι × Fin n × Fin n => (A x.1 * u x.1) x.2.1 x.2.2) P := by
  refine (eval₂Hom_bind₁ (RingHom.id ℂ) _ (leftSubst A) P).trans
    (congrArg (fun f => eval f P) (funext fun x => ?_))
  simp [leftSubst, Matrix.mul_apply]

/- English proof (translation)
Establish `hd : (diagonal t)ᴴ * diagonal t = 1`. Rewrite using `[diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `k`. Rewrite using `[Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, ht k]`.

Evaluate the numerical expressions. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc wᴴ, hw, Matrix.one_mul, ← Matrix.mul_assoc (diagonal t)ᴴ, hd, Matrix.one_mul, hv]`.
-/
theorem unitary_of_torus {n : ℕ} (w v : Matrix (Fin n) (Fin n) ℂ) (hw : wᴴ * w = 1)
    (hv : vᴴ * v = 1) (t : Fin n → ℂ) (ht : ∀ k, ‖t k‖ = 1) :
    (w * diagonal t * v)ᴴ * (w * diagonal t * v) = 1 := by
  have hd : (diagonal t)ᴴ * diagonal t = 1 := by
    rw [diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    rw [Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, ht k]
    norm_num
  simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc wᴴ, hw, Matrix.one_mul, ← Matrix.mul_assoc (diagonal t)ᴴ, hd,
    Matrix.one_mul, hv]

end PI.UD
