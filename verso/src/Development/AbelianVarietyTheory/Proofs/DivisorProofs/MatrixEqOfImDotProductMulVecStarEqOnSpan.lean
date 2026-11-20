import Mathlib
open scoped Matrix

namespace GlobalTheory

/- English proof (translation)
Introduce `g H H' S hS h`. Use `set D := H - H' with hD`. Establish `hS0 : ∀ a ∈ S, ∀ b ∈ S, (a ⬝ᵥ D.mulVec (star b)).im = 0`. Introduce `a ha b hb`. Simplify using `only [hD, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_im, h a ha b hb, sub_self]`.

Set `B : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ` to `LinearMap.mk₂ ℝ (fun a b => (a ⬝ᵥ D.mulVec (star b)).im) (by intro a a' b; simp [add_dotProduct]) (by intro r a b; simp [smul_dotProduct]) (by intro a b b'; simp [star_add, Matrix.mulVec_add, dotProduct_add]) (by intro r a b; simp [star_smul, Matrix.mulVec_smul, dotProduct_smul])`. Establish `hB : B = 0`. Apply `LinearMap.ext_on hS` to reduce the goal to its premises. Introduce `a ha`. Apply `LinearMap.ext_on hS` to reduce the goal to its premises.

Introduce `b hb`. Simplify `hS0 a ha b hb` using `[B]`. Establish `hall : ∀ a b, (a ⬝ᵥ D.mulVec (star b)) = 0`. Introduce `a b`. Establish `h1 : (a ⬝ᵥ D.mulVec (star b)).im = 0`.

Use `congrArg (fun f => f a b) hB` as an intermediate fact. Simplify `this` using `[B]`. Establish `h2 : ((Complex.I • a) ⬝ᵥ D.mulVec (star b)).im = 0`. Use `congrArg (fun f => f (Complex.I • a) b) hB` as an intermediate fact. Simplify `this` using `[B]`.

Rewrite `h2` using `[smul_dotProduct, smul_eq_mul, Complex.mul_im]`. Simplify using `at h2`. Conclude with `Complex.ext h2 h1`. Establish `hDz : D = 0`. Use extensionality with `i j`.

Use `hall (Pi.single i 1) (Pi.single j 1)` as an intermediate fact. Simplify `this` using `[Matrix.mulVec_single_one, Pi.star_single]`. Conclude with `sub_eq_zero.mp hDz`.
-/
theorem matrix_eq_of_im_dotProduct_mulVec_star_eq_on_span :
    ∀ (g : ℕ) (H H' : Matrix (Fin g) (Fin g) ℂ) (S : Set (Fin g → ℂ)),
    Submodule.span ℝ S = ⊤ →
    (∀ a ∈ S, ∀ b ∈ S, (a ⬝ᵥ H.mulVec (star b)).im = (a ⬝ᵥ H'.mulVec (star b)).im) → H = H' := by
  intro g H H' S hS h
  set D := H - H' with hD
  have hS0 : ∀ a ∈ S, ∀ b ∈ S, (a ⬝ᵥ D.mulVec (star b)).im = 0 := by
    intro a ha b hb
    simp only [hD, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_im, h a ha b hb, sub_self]
  let B : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun a b => (a ⬝ᵥ D.mulVec (star b)).im)
      (by intro a a' b; simp [add_dotProduct])
      (by intro r a b; simp [smul_dotProduct])
      (by intro a b b'; simp [star_add, Matrix.mulVec_add, dotProduct_add])
      (by intro r a b; simp [star_smul, Matrix.mulVec_smul, dotProduct_smul])
  have hB : B = 0 := by
    apply LinearMap.ext_on hS
    intro a ha
    apply LinearMap.ext_on hS
    intro b hb
    simpa [B] using hS0 a ha b hb
  have hall : ∀ a b, (a ⬝ᵥ D.mulVec (star b)) = 0 := by
    intro a b
    have h1 : (a ⬝ᵥ D.mulVec (star b)).im = 0 := by
      have := congrArg (fun f => f a b) hB
      simpa [B] using this
    have h2 : ((Complex.I • a) ⬝ᵥ D.mulVec (star b)).im = 0 := by
      have := congrArg (fun f => f (Complex.I • a) b) hB
      simpa [B] using this
    rw [smul_dotProduct, smul_eq_mul, Complex.mul_im] at h2
    simp at h2
    exact Complex.ext h2 h1
  have hDz : D = 0 := by
    ext i j
    have := hall (Pi.single i 1) (Pi.single j 1)
    simpa [Matrix.mulVec_single_one, Pi.star_single] using this
  exact sub_eq_zero.mp hDz

end GlobalTheory
