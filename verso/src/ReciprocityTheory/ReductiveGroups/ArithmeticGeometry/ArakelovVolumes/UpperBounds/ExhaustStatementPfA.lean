import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LiftFactorization
import ReciprocityTheory.L2DbarEstimates.LeviForms.DetMonoDetOneAdd
import Lemmata.PosDefOfRealQuadratic.QuadFormRealSmul

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA

open Matrix
open scoped ComplexOrder Matrix

variable {p q : ℕ}

/- English proof (translation)
Use `set B := 1 - W * Wᴴ with hBdef`. Use `set C := 1 - Z * Wᴴ with hCdef`. Use `set S := B⁻¹ with hSdef`. Establish `hBu : IsUnit B.det` using `isUnit_iff_ne_zero.2 hW.det_pos.ne'`. Establish `hSB : S * B = 1` using `Matrix.nonsing_inv_mul B hBu`.

Establish `hBS : B * S = 1` using `Matrix.mul_nonsing_inv B hBu`. Establish `hBh : Bᴴ = B` using `hW.1`. Establish `hS : Sᴴ = S` using `by rw [hSdef, Matrix.conjTranspose_nonsing_inv, hBh]`. Establish `h1 : (C * S - 1) * B * (C * S - 1)ᴴ = C * S * Cᴴ - C - Cᴴ + B`. Establish `e : (C * S - 1) * B = C - B`.

Rewrite using `[Matrix.sub_mul, Matrix.mul_assoc, hSB, Matrix.mul_one, Matrix.one_mul]`. Rewrite using `[e, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hS, Matrix.conjTranspose_one, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_one, ← Matrix.mul_assoc B S, hBS, Matrix.one_mul, Matrix.mul_assoc C S]`. Normalize the expressions using the abelian group laws. Establish `h2 : C + Cᴴ - B = (1 - Z * Zᴴ) + (W - Z) * (W - Z)ᴴ`. Rewrite using `[hCdef, hBdef]`.

Simplify using `only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_one, Matrix.conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.mul_sub]`. Normalize the expressions using the abelian group laws. Establish `e : C * S * Cᴴ - (1 - Z * Zᴴ) = (C * S - 1) * B * (C * S - 1)ᴴ + (W - Z) * (W - Z)ᴴ`. Establish `hA : (1 - Z * Zᴴ) = C + Cᴴ - B - (W - Z) * (W - Z)ᴴ` using `by rw [h2]; abel`. Rewrite using `[h1, hA]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `(hW.posSemidef.mul_mul_conjTranspose_same _).add (posSemidef_self_mul_conjTranspose _)`.
-/
theorem cross_psd (Z W : Matrix (Fin p) (Fin q) ℂ) (hW : (1 - W * Wᴴ).PosDef) :
    ((1 - Z * Wᴴ) * (1 - W * Wᴴ)⁻¹ * (1 - Z * Wᴴ)ᴴ - (1 - Z * Zᴴ)).PosSemidef := by
  set B := 1 - W * Wᴴ with hBdef
  set C := 1 - Z * Wᴴ with hCdef
  set S := B⁻¹ with hSdef
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.2 hW.det_pos.ne'
  have hSB : S * B = 1 := Matrix.nonsing_inv_mul B hBu
  have hBS : B * S = 1 := Matrix.mul_nonsing_inv B hBu
  have hBh : Bᴴ = B := hW.1
  have hS : Sᴴ = S := by rw [hSdef, Matrix.conjTranspose_nonsing_inv, hBh]
  have h1 : (C * S - 1) * B * (C * S - 1)ᴴ = C * S * Cᴴ - C - Cᴴ + B := by
    have e : (C * S - 1) * B = C - B := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, hSB, Matrix.mul_one, Matrix.one_mul]
    rw [e, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hS, Matrix.conjTranspose_one,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_one,
      ← Matrix.mul_assoc B S, hBS, Matrix.one_mul, Matrix.mul_assoc C S]
    abel
  have h2 : C + Cᴴ - B = (1 - Z * Zᴴ) + (W - Z) * (W - Z)ᴴ := by
    rw [hCdef, hBdef]
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_one,
      Matrix.conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.mul_sub]
    abel
  have e : C * S * Cᴴ - (1 - Z * Zᴴ) = (C * S - 1) * B * (C * S - 1)ᴴ + (W - Z) * (W - Z)ᴴ := by
    have hA : (1 - Z * Zᴴ) = C + Cᴴ - B - (W - Z) * (W - Z)ᴴ := by rw [h2]; abel
    rw [h1, hA]; abel
  rw [e]
  exact (hW.posSemidef.mul_mul_conjTranspose_same _).add (posSemidef_self_mul_conjTranspose _)

/- English proof (translation)
Establish `h` using `hA.det_pos`. Rewrite `h` using `[Complex.lt_def]`. Conclude with `⟨by simpa using h.1, by simpa using h.2.symm⟩`.
-/
theorem det_re_pos_im {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) :
    0 < A.det.re ∧ A.det.im = 0 := by
  have h := hA.det_pos
  rw [Complex.lt_def] at h
  exact ⟨by simpa using h.1, by simpa using h.2.symm⟩

/- English proof (translation)
The claim follows from `Complex.ext (by simp) (by simp [(det_re_pos_im hA).2])`.
-/
theorem det_eq_ofReal {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) :
    A.det = ((A.det.re : ℝ) : ℂ) :=
  Complex.ext (by simp) (by simp [(det_re_pos_im hA).2])

/- English proof (translation)
Establish `hm` using `ReciprocityTheory.L2DbarEstimates.I.maDet p ((1 - Z * Wᴴ) * (1 - W * Wᴴ)⁻¹ * (1 - Z * Wᴴ)ᴴ) (1 - Z * Zᴴ) hZ.posSemidef (cross_psd Z W hW)`. Take `⟨hb, hbi⟩` from `det_re_pos_im hW`. Use `set b := (1 - W * Wᴴ).det.re`. Establish `hdet : ((1 - Z * Wᴴ) * (1 - W * Wᴴ)⁻¹ * (1 - Z * Wᴴ)ᴴ).det = ((Complex.normSq (1 - Z * Wᴴ).det / b : ℝ) : ℂ)`. Rewrite using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, Matrix.det_conjTranspose, Ring.inverse_eq_inv', det_eq_ofReal hW, mul_right_comm, Complex.star_def, Complex.mul_conj]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hm` using `[hdet, Complex.ofReal_re]`. Rewrite `hm` using `[le_div_iff₀ hb]`. Then use the resulting hypothesis.
-/
theorem det_mul_det_le_normSq_det (Z W : Matrix (Fin p) (Fin q) ℂ) (hZ : (1 - Z * Zᴴ).PosDef)
    (hW : (1 - W * Wᴴ).PosDef) :
    (1 - Z * Zᴴ).det.re * (1 - W * Wᴴ).det.re ≤ Complex.normSq (1 - Z * Wᴴ).det := by
  have hm := ReciprocityTheory.L2DbarEstimates.I.maDet p ((1 - Z * Wᴴ) * (1 - W * Wᴴ)⁻¹ * (1 - Z * Wᴴ)ᴴ)
    (1 - Z * Zᴴ) hZ.posSemidef (cross_psd Z W hW)
  obtain ⟨hb, hbi⟩ := det_re_pos_im hW
  set b := (1 - W * Wᴴ).det.re
  have hdet : ((1 - Z * Wᴴ) * (1 - W * Wᴴ)⁻¹ * (1 - Z * Wᴴ)ᴴ).det =
      ((Complex.normSq (1 - Z * Wᴴ).det / b : ℝ) : ℂ) := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, Matrix.det_conjTranspose,
      Ring.inverse_eq_inv', det_eq_ofReal hW, mul_right_comm, Complex.star_def, Complex.mul_conj]
    push_cast; ring
  rw [hdet, Complex.ofReal_re] at hm
  rwa [le_div_iff₀ hb] at hm

/- English proof (translation)
Establish `hm` using `ReciprocityTheory.L2DbarEstimates.I.maDet p 1 (1 - Z * Zᴴ) hZ.posSemidef (by rw [sub_sub_cancel]; exact posSemidef_self_mul_conjTranspose Z)`. Simplify using `using hm`.
-/
theorem det_re_le_one {Z : Matrix (Fin p) (Fin q) ℂ} (hZ : (1 - Z * Zᴴ).PosDef) :
    (1 - Z * Zᴴ).det.re ≤ 1 := by
  have hm := ReciprocityTheory.L2DbarEstimates.I.maDet p 1 (1 - Z * Zᴴ) hZ.posSemidef
    (by rw [sub_sub_cancel]; exact posSemidef_self_mul_conjTranspose Z)
  simpa using hm

end ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB

open Matrix Topology Filter
open scoped ComplexOrder Matrix
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up

/- English proof (translation)
Rewrite using `[← Complex.conj_eq_iff_im]`. Simplify using `only [dotProduct, mulVec, map_sum, map_mul, Pi.star_apply, Complex.star_def, Complex.conj_conj, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `h` using `hA.apply i j`.

Rewrite `h` using `[Complex.star_def]`. Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem quad_im {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.IsHermitian) (x : Fin m → ℂ) :
    (star x ⬝ᵥ (A *ᵥ x)).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  simp only [dotProduct, mulVec, map_sum, map_mul, Pi.star_apply, Complex.star_def,
    Complex.conj_conj, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h := hA.apply i j
  rw [Complex.star_def] at h
  rw [h]; ring

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.PosDefOfRealQuadratic.goal1 .. | (apply Bl.PosDefOfRealQuadratic.goal1 <;> assumption) | (intros; apply Bl.PosDefOfRealQuadratic.goal1 <;> assumption)`.
-/
theorem posDef_eventually {X : Type*} [TopologicalSpace X] {m : ℕ}
    (A : X → Matrix (Fin m) (Fin m) ℂ) (hc : ∀ i j, Continuous fun x => A x i j)
    (hH : ∀ x, (A x).IsHermitian) (x0 : X) (h0 : (A x0).PosDef) :
    ∀ᶠ x in 𝓝 x0, (A x).PosDef := by
  first | exact Bl.PosDefOfRealQuadratic.goal1 .. | (apply Bl.PosDefOfRealQuadratic.goal1 <;> assumption) | (intros; apply Bl.PosDefOfRealQuadratic.goal1 <;> assumption)

/- English proof (translation)
Establish `h : (fun v : V n => v i) = ⇑(EuclideanSpace.proj i : V n →L[ℂ] ℂ)`. Use function extensionality and compare the values at `v`. Simplify using the standard rewrite rules. Rewrite using `[h]`. Conclude with `ContinuousLinearMap.continuous _`.
-/
theorem cont_coord {n : ℕ} (i : Fin n) : Continuous fun v : V n => v i := by
  have h : (fun v : V n => v i) = ⇑(EuclideanSpace.proj i : V n →L[ℂ] ℂ) := by
    funext v; simp
  rw [h]; exact ContinuousLinearMap.continuous _

/- English proof (translation)
The claim follows from `isHermitian_one.sub (isHermitian_mul_conjTranspose_self Z)`.
-/
theorem herm_one_sub {p q : ℕ} (Z : Matrix (Fin p) (Fin q) ℂ) : (1 - Z * Zᴴ).IsHermitian :=
  isHermitian_one.sub (isHermitian_mul_conjTranspose_self Z)

/- English proof (translation)
Simplify using `only [Matrix.sub_apply, Matrix.mul_apply, conjTranspose_apply, Zof, Matrix.of_apply]`. Conclude with `continuous_const.sub (continuous_finsetSum _ fun c _ => (hg _).mul (continuous_star.comp (hg _)))`.
-/
theorem cont_entry {X : Type*} [TopologicalSpace X] {f p q : ℕ} (g : X → V (nD f p q))
    (hg : ∀ i, Continuous fun x => g x i) (k : Fin f) (a b : Fin p) :
    Continuous fun x => (1 - Zof (g x) k * (Zof (g x) k)ᴴ : Matrix (Fin p) (Fin p) ℂ) a b := by
  simp only [Matrix.sub_apply, Matrix.mul_apply, conjTranspose_apply, Zof, Matrix.of_apply]
  exact continuous_const.sub (continuous_finsetSum _ fun c _ =>
    (hg _).mul (continuous_star.comp (hg _)))

/- English proof (translation)
Use `isOpen_iff_mem_nhds.2 fun x0 hx0 => ?_` and prove the remaining obligations. Apply the tactic sequence `exact Filter.eventually_all.2 fun k => posDef_eventually _ (cont_entry g hg k) (fun x => herm_one_sub _) x0 (hx0 k)`.
-/
theorem isOpen_of {X : Type*} [TopologicalSpace X] {f p q : ℕ} (g : X → V (nD f p q))
    (hg : ∀ i, Continuous fun x => g x i) :
    IsOpen {x | ∀ k, (1 - Zof (g x) k * (Zof (g x) k)ᴴ).PosDef} := by
  refine isOpen_iff_mem_nhds.2 fun x0 hx0 => ?_
  exact Filter.eventually_all.2 fun k => posDef_eventually _ (cont_entry g hg k)
    (fun x => herm_one_sub _) x0 (hx0 k)

/- English proof (translation)
Simplify using `[zPart]`.
-/
theorem zPart_apply {f p q N' : ℕ} (v : V (nD f p q + N')) (j : Fin (nD f p q)) :
    zPart v j = v (Fin.castAdd N' j) := by
  simp [zPart]

/- English proof (translation)
Simplify using `[tPart]`.
-/
theorem tPart_apply {f p q N' : ℕ} (v : V (nD f p q + N')) (j : Fin N') :
    tPart v j = v (Fin.natAdd (nD f p q) j) := by
  simp [tPart]

/- English proof (translation)
The claim follows from `isOpen_of (fun v : V (nD f p q) => v) cont_coord`.
-/
theorem isOpen_Dset (f p q : ℕ) : IsOpen (Dset f p q) :=
  isOpen_of (fun v : V (nD f p q) => v) cont_coord

end ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
