import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Sec2

noncomputable section

open MeasureTheory Matrix Complex
open Ad3 Ad3.LR Ad3.K.GL2LocalData Ad3.K.GL2LocalData.WR GlobalTheory.CompanionTheory.GL2LocalData.RealWhittakerFirst

namespace GlobalTheory.CompanionTheory.GL2LocalData.RealWhittakerFirst.BndFin

def gW (J : ℕ) (c : ℝ) (g : M22) : ℝ :=
  |(Matrix.of g).det| ^ c *
    ((2 * nrm (Matrix.of g)) ^ ((J : ℝ) / 2) * Real.exp (-Real.pi * nrm (Matrix.of g)))

def Tv (J : ℕ) (α c : ℝ) (v : Fin 2 → ℝ) : ENNReal :=
  ∫⁻ g : M22, ENNReal.ofReal (nv (Matrix.vecMul v (Matrix.of g)) ^ (-α) * gW J c g)

def dK (β K N d : ℝ) : ℝ :=
  if 0 < d then d ^ β * (d / N) ^ K * Real.exp (-2 * Real.pi * (d / N)) else 0

/- English proof (translation)
Unfold `nv`. Check the signs of the components of the expression.
-/
theorem nv_nonneg (v : Fin 2 → ℝ) : 0 ≤ nv v := by unfold nv; positivity

/- English proof (translation)
Unfold `nrm; exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity`.
-/
theorem nrm_nonneg (g : Mt) : 0 ≤ nrm g := by
  unfold nrm; exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity

/- English proof (translation)
Use `nrm_nonneg (Matrix.of g)` as an intermediate fact. Unfold `gW`. Check the signs of the components of the expression.
-/
theorem gW_nonneg (J : ℕ) (c : ℝ) (g : M22) : 0 ≤ gW J c g := by
  have := nrm_nonneg (Matrix.of g)
  unfold gW; positivity

/- English proof (translation)
Unfold `dK`. Use `split_ifs with h`. Use `h.le` as an intermediate fact. Check the signs of the components of the expression. Conclude with `le_rfl`.
-/
theorem dK_nonneg (β K : ℝ) {N : ℝ} (hN : 0 ≤ N) (d : ℝ) : 0 ≤ dK β K N d := by
  unfold dK; split_ifs with h
  · have := h.le; positivity
  · exact le_rfl

/- English proof (translation)
Unfold `nv`. Use `fun_prop`.
-/
theorem measurable_nv : Measurable nv := by unfold nv; fun_prop

/- English proof (translation)
Simplify using `only [Matrix.det_fin_two, Matrix.of_apply]`. Use `fun_prop`.
-/
theorem measurable_det : Measurable fun g : M22 => (Matrix.of g).det := by
  simp only [Matrix.det_fin_two, Matrix.of_apply]; fun_prop

/- English proof (translation)
Unfold `nrm`. Simplify using `only [Matrix.of_apply, Fin.sum_univ_two]`. Use `fun_prop`.
-/
theorem measurable_nrm : Measurable fun g : M22 => nrm (Matrix.of g) := by
  unfold nrm; simp only [Matrix.of_apply, Fin.sum_univ_two]; fun_prop

/- English proof (translation)
Establish `h3` using `measurable_det`. Establish `h4` using `measurable_nrm`. Unfold `gW`. Use `fun_prop`.
-/
theorem measurable_gW (J : ℕ) (c : ℝ) : Measurable (gW J c) := by
  have h3 := measurable_det
  have h4 := measurable_nrm
  unfold gW
  fun_prop

end GlobalTheory.CompanionTheory.GL2LocalData.RealWhittakerFirst.BndFin

end
