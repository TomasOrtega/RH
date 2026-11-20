import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DwCons

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.SobGL.LeftTr

variable {n : ℕ}

/- English proof (translation)
Establish `h : Continuous (fun g : Mat n => g.det)` using `Continuous.matrix_det continuous_id`. Conclude with `isOpen_ne.preimage h`.
-/
theorem isOpen_gls (n : ℕ) : IsOpen (GLs n) := by
  have h : Continuous (fun g : Mat n => g.det) := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage h

def lmul (x : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ x)

def rmul (x : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ x)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lmul_apply (x y : Mat n) : lmul x y = x * y := rfl

/- English proof (translation)
Simplify using `only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at *`. Conclude with `mul_ne_zero hx hy`.
-/
theorem mul_mem_gls {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at *
  exact mul_ne_zero hx hy

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

/- English proof (translation)
Establish `h1 : ContDiffOn ℝ ∞ (fderiv ℝ f) U` using `hf.fderiv_of_isOpen hU (by simp)`. Conclude with `h1.clm_apply A.contDiff.contDiffOn`.
-/
theorem contDiffOn_along {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) (A : E →L[ℝ] E) :
    ContDiffOn ℝ ∞ (fun g => fderiv ℝ f g (A g)) U := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  exact h1.clm_apply A.contDiff.contDiffOn

/- English proof (translation)
The claim follows from `contDiffOn_along (isOpen_gls n) hf (rmul X)`.
-/
theorem contDiffOn_Rd {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (X : Mat n) :
    ContDiffOn ℝ ∞ (Rd X f) (GLs n) :=
  contDiffOn_along (isOpen_gls n) hf (rmul X)

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => exact hf`. Consider the case `cons p w ih => exact contDiffOn_Rd ih (bs p)`.
-/
theorem contDiffOn_Rw {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (w : List (Idx n)) : ContDiffOn ℝ ∞ (Rw w f) (GLs n) := by
  induction w with
  | nil => exact hf
  | cons p w ih => exact contDiffOn_Rd ih (bs p)

/- English proof (translation)
Establish `hmaps : Set.MapsTo (fun y : Mat n => x * y) (GLs n) (GLs n)` using `fun y hy => mul_mem_gls hx hy`. Use `⟨hf.comp (lmul x).contDiff.contDiffOn hmaps, fun w => ?_⟩` and prove the remaining obligations. Proceed by induction on `w with`. Consider the case `nil => intro y _`. Both sides reduce to the same expression.

Consider the case `cons p w ih`. Introduce `y hy`. Establish `hev : Rw w (fun y => f (x * y)) =ᶠ[nhds y] (Rw w f) ∘ (lmul x)` using `Filter.eventually_of_mem ((isOpen_gls n).mem_nhds hy) ih`. Establish `hd : DifferentiableAt ℝ (Rw w f) (lmul x y)` using `((contDiffOn_Rw hf w).contDiffAt ((isOpen_gls n).mem_nhds (mul_mem_gls hx hy))).differentiableAt (by simp)`. Establish `hc : HasFDerivAt ((Rw w f) ∘ (lmul x)) ((fderiv ℝ (Rw w f) (lmul x y)).comp (lmul x)) y` using `hd.hasFDerivAt.comp y (lmul x).hasFDerivAt`.

Express the relevant statement in the definitionally equal form `fderiv ℝ (Rw w (fun y => f (x * y))) y (y * bs p) = fderiv ℝ (Rw w f) (x * y) (x * y * bs p)`. Rewrite using `[hev.fderiv_eq, hc.fderiv]`. Simplify using `only [ContinuousLinearMap.comp_apply, lmul_apply, Matrix.mul_assoc]`.
-/
theorem Rw_left (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V)
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (x : Mat n) (hx : x ∈ GLs n) :
    ContDiffOn ℝ ∞ (fun y => f (x * y)) (GLs n) ∧
      ∀ (w : List (Idx n)), ∀ y ∈ GLs n, Rw w (fun y => f (x * y)) y = Rw w f (x * y) := by
  have hmaps : Set.MapsTo (fun y : Mat n => x * y) (GLs n) (GLs n) :=
    fun y hy => mul_mem_gls hx hy
  refine ⟨hf.comp (lmul x).contDiff.contDiffOn hmaps, fun w => ?_⟩
  induction w with
  | nil => intro y _; rfl
  | cons p w ih =>
    intro y hy
    have hev : Rw w (fun y => f (x * y)) =ᶠ[nhds y] (Rw w f) ∘ (lmul x) :=
      Filter.eventually_of_mem ((isOpen_gls n).mem_nhds hy) ih
    have hd : DifferentiableAt ℝ (Rw w f) (lmul x y) :=
      ((contDiffOn_Rw hf w).contDiffAt ((isOpen_gls n).mem_nhds (mul_mem_gls hx hy))).differentiableAt
        (by simp)
    have hc : HasFDerivAt ((Rw w f) ∘ (lmul x))
        ((fderiv ℝ (Rw w f) (lmul x y)).comp (lmul x)) y :=
      hd.hasFDerivAt.comp y (lmul x).hasFDerivAt
    change fderiv ℝ (Rw w (fun y => f (x * y))) y (y * bs p) =
      fderiv ℝ (Rw w f) (x * y) (x * y * bs p)
    rw [hev.fderiv_eq, hc.fderiv]
    simp only [ContinuousLinearMap.comp_apply, lmul_apply, Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.SobGL.LeftTr
