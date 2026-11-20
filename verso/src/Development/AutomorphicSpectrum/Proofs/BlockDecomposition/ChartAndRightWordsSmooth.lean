import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DwCons
open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.SobGL.Smooth

/- English proof (translation)
Establish `: Continuous fun g : Mat n => g.det` using `Continuous.matrix_det continuous_id`. Conclude with `isOpen_ne.preimage this`.
-/
theorem isOpen_GLs' (n : ℕ) : IsOpen (GLs n) := by
  have : Continuous fun g : Mat n => g.det := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage this

/- English proof (translation)
Unfold `cm`. Conclude with `continuous_finset_sum _ fun p _ => (continuous_apply p).smul continuous_const`.
-/
theorem continuous_cm' (n : ℕ) : Continuous (cm (n := n)) := by
  unfold cm
  exact continuous_finset_sum _ fun p _ => (continuous_apply p).smul continuous_const

/- English proof (translation)
Simplify using `[cm]`.
-/
theorem cm_zero' (n : ℕ) : cm (n := n) 0 = 0 := by
  simp [cm]

def mulRight' {n : ℕ} (X : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)

/- English proof (translation)
Establish `h1 : ContDiffOn ℝ ∞ (fderiv ℝ f) U` using `hf.fderiv_of_isOpen hU (by simp)`. Conclude with `h1.clm_apply hA`.
-/
theorem contDiffOn_fderiv_apply' {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) {A : E → E} (hA : ContDiffOn ℝ ∞ A U) :
    ContDiffOn ℝ ∞ (fun g => fderiv ℝ f g (A g)) U := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  exact h1.clm_apply hA

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => exact hf`. Consider the case `cons p w ih`. Conclude with `contDiffOn_fderiv_apply' (isOpen_GLs' n) ih (mulRight' (bs p)).contDiff.contDiffOn`.
-/
theorem Rw_contDiffOn' {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (w : List (Idx n)) :
    ContDiffOn ℝ ∞ (Rw w f) (GLs n) := by
  induction w with
  | nil => exact hf
  | cons p w ih =>
    exact contDiffOn_fderiv_apply' (isOpen_GLs' n) ih (mulRight' (bs p)).contDiff.contDiffOn

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => exact hf`. Consider the case `cons p L ih`. Conclude with `contDiffOn_fderiv_apply' (isOpen_GLs' n) ih contDiffOn_const`.
-/
theorem Dw_contDiffOn' {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (L : List (Idx n)) :
    ContDiffOn ℝ ∞ (Dw L f) (GLs n) := by
  induction L with
  | nil => exact hf
  | cons p L ih =>
    exact contDiffOn_fderiv_apply' (isOpen_GLs' n) ih contDiffOn_const

/- English proof (translation)
Introduce `n` and use `⟨isOpen_GLs' n, continuous_cm' n, cm_zero' n, fun _ _ _ _ hf => ⟨Rw_contDiffOn' hf, Dw_contDiffOn' hf⟩⟩`.
-/
theorem smooth_all : ∀ n : ℕ, IsOpen (GLs n) ∧ Continuous (cm (n := n)) ∧ cm (n := n) 0 = 0 ∧
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) →
      (∀ w, ContDiffOn ℝ ∞ (Rw w f) (GLs n)) ∧ ∀ L : List (Idx n), ContDiffOn ℝ ∞ (Dw L f) (GLs n) :=
  fun n => ⟨isOpen_GLs' n, continuous_cm' n, cm_zero' n, fun _ _ _ _ hf =>
    ⟨Rw_contDiffOn' hf, Dw_contDiffOn' hf⟩⟩

end GlobalTheory.CompanionTheory.SobGL.Smooth
