import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open Finset
open scoped ComplexConjugate Matrix

noncomputable section

/- English proof (translation)
Use `symm`. Apply `Finset.orderEmbOfFin_unique` to reduce the goal to its premises. Introduce `x`. Conclude with `Finset.mem_map.mpr ⟨x, mem_univ x, rfl⟩`. Introduce `a b hab`.

Conclude with `hab`.
-/
theorem orderEmbOfFin_map_castLEEmb {l N : ℕ} (hl : l ≤ N)
    (h : ((univ : Finset (Fin l)).map (Fin.castLEEmb hl)).card = l) :
    (((univ : Finset (Fin l)).map (Fin.castLEEmb hl)).orderEmbOfFin h : Fin l → Fin N) =
      Fin.castLE hl := by
  symm
  apply Finset.orderEmbOfFin_unique
  · intro x
    exact Finset.mem_map.mpr ⟨x, mem_univ x, rfl⟩
  · intro a b hab
    exact hab

/- English proof (translation)
Distinguish the cases in `hl : l ≤ N`. Set `g : Matrix (Fin N) (Fin N) ℂ` to `Matrix.of fun k j => if h : j.val < l then star (V ⟨j.val, h⟩ k) else 0`. Set `I0 : Finset (Fin N)` to `(univ : Finset (Fin l)).map (Fin.castLEEmb hl)`. Establish `hI0 : I0.card = l` using `by simp [I0]`. Establish `hemb` using `orderEmbOfFin_map_castLEEmb hl hI0`.

Establish `key` using `h0 ℂ l N V g I0 hI0`. Establish `lhs : pluckerCoord (V * g) I0 = (V * Vᴴ).det`. Unfold `pluckerCoord`. Rewrite using `[dif_pos hI0]`. Use `congr 1`.

Use extensionality with `i j`. Simplify using `[I0, Matrix.mul_apply, hemb, g, Matrix.conjTranspose_apply]`. Establish `rhs : ∀ J ∈ powersetCard l (univ : Finset (Fin N)), pluckerCoord V J * minorOn g l J I0 = ((‖pluckerCoord V J‖ ^ 2 : ℝ) : ℂ)`. Introduce `J hJ`. Establish `hJc : J.card = l` using `(mem_powersetCard.mp hJ).2`.

Establish `hm : minorOn g l J I0 = star (pluckerCoord V J)`. Unfold `minorOn pluckerCoord`. Rewrite using `[dif_pos ⟨hJc, hI0⟩, dif_pos hJc, ← Matrix.det_conjTranspose]`. Use `congr 1`. Use extensionality with `i j`.

Simplify using `[I0, hemb, g, Matrix.conjTranspose_apply]`. Rewrite using `[hm, Complex.star_def, RCLike.mul_conj]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[← lhs, key, Complex.ofReal_sum]`.

Conclude with `(sum_congr rfl rhs).symm`. Rewrite `hl` using `[not_le]`. Establish `hE : powersetCard l (univ : Finset (Fin N)) = ∅` using `Finset.powersetCard_eq_empty.mpr (by simpa using hl)`. Rewrite using `[hE, sum_empty, Complex.ofReal_zero, eq_comm]`. Assume the negation of the conclusion as `hd`.

Establish `hu : IsUnit (V * Vᴴ)` using `(Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd)`. Establish `h1` using `Matrix.rank_of_isUnit _ hu`. Establish `h2` using `(Matrix.rank_mul_le_left V Vᴴ).trans (Matrix.rank_le_width V)`. Simplify using `only [Fintype.card_fin] at h1`. Use linear arithmetic over natural numbers and integers.
-/
theorem sum_sq_norm_pluckerCoord_eq_det_mul_conjTranspose (h0 : PluckerFrameChange.Statement)
    {l N : ℕ} (V : Matrix (Fin l) (Fin N) ℂ) :
    (((∑ I ∈ powersetCard l (univ : Finset (Fin N)), ‖pluckerCoord V I‖ ^ 2 : ℝ)) : ℂ) =
      (V * Vᴴ).det := by
  by_cases hl : l ≤ N
  · let g : Matrix (Fin N) (Fin N) ℂ :=
      Matrix.of fun k j => if h : j.val < l then star (V ⟨j.val, h⟩ k) else 0
    let I0 : Finset (Fin N) := (univ : Finset (Fin l)).map (Fin.castLEEmb hl)
    have hI0 : I0.card = l := by simp [I0]
    have hemb := orderEmbOfFin_map_castLEEmb hl hI0
    have key := h0 ℂ l N V g I0 hI0
    have lhs : pluckerCoord (V * g) I0 = (V * Vᴴ).det := by
      unfold pluckerCoord
      rw [dif_pos hI0]
      congr 1
      ext i j
      simp [I0, Matrix.mul_apply, hemb, g, Matrix.conjTranspose_apply]
    have rhs : ∀ J ∈ powersetCard l (univ : Finset (Fin N)),
        pluckerCoord V J * minorOn g l J I0 = ((‖pluckerCoord V J‖ ^ 2 : ℝ) : ℂ) := by
      intro J hJ
      have hJc : J.card = l := (mem_powersetCard.mp hJ).2
      have hm : minorOn g l J I0 = star (pluckerCoord V J) := by
        unfold minorOn pluckerCoord
        rw [dif_pos ⟨hJc, hI0⟩, dif_pos hJc, ← Matrix.det_conjTranspose]
        congr 1
        ext i j
        simp [I0, hemb, g, Matrix.conjTranspose_apply]
      rw [hm, Complex.star_def, RCLike.mul_conj]
      push_cast
      rfl
    rw [← lhs, key, Complex.ofReal_sum]
    exact (sum_congr rfl rhs).symm
  · rw [not_le] at hl
    have hE : powersetCard l (univ : Finset (Fin N)) = ∅ :=
      Finset.powersetCard_eq_empty.mpr (by simpa using hl)
    rw [hE, sum_empty, Complex.ofReal_zero, eq_comm]
    by_contra hd
    have hu : IsUnit (V * Vᴴ) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd)
    have h1 := Matrix.rank_of_isUnit _ hu
    have h2 := (Matrix.rank_mul_le_left V Vᴴ).trans (Matrix.rank_le_width V)
    simp only [Fintype.card_fin] at h1
    omega

/- English proof (translation)
Introduce `l N V`. Establish `hg` using `sum_sq_norm_pluckerCoord_eq_det_mul_conjTranspose h0 V`. Use `⟨hg, fun hd => ?_⟩` and prove the remaining obligations. Establish `hS : (0 : ℝ) ≤ ∑ I ∈ powersetCard l (univ : Finset (Fin N)), ‖pluckerCoord V I‖ ^ 2` using `sum_nonneg fun _ _ => by positivity`. Rewrite using `[← Finset.sum_div, ← hg, Complex.norm_real, Real.norm_of_nonneg hS]`.

Apply `div_self` to reduce the goal to its premises. Introduce `hz`. Apply `hd` to reduce the goal to its premises. Rewrite using `[← hg, hz, Complex.ofReal_zero]`.
-/
theorem GramSumOfMinors.proof (h0 : PluckerFrameChange.Statement) : GramSumOfMinors.Statement := by
  intro l N V
  have hg := sum_sq_norm_pluckerCoord_eq_det_mul_conjTranspose h0 V
  refine ⟨hg, fun hd => ?_⟩
  have hS : (0 : ℝ) ≤ ∑ I ∈ powersetCard l (univ : Finset (Fin N)), ‖pluckerCoord V I‖ ^ 2 :=
    sum_nonneg fun _ _ => by positivity
  rw [← Finset.sum_div, ← hg, Complex.norm_real, Real.norm_of_nonneg hS]
  apply div_self
  intro hz
  apply hd
  rw [← hg, hz, Complex.ofReal_zero]

end

end GroundTheory.Heights₂.Heights.FlagBundles
