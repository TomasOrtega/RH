import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient

open Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory.SiegelNormalForm

variable {g : ℕ}

open Complex Matrix Filter Topology in
open scoped BigOperators Real in
variable {g : ℕ} in

/- English proof (translation)
Rewrite using `[star_mulVec, ← mulVec_transpose, conjTranspose, ← transpose_map, transpose_transpose, dotProduct_comm, dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]`.
-/
theorem _root_.GlobalTheory.SiegelNormalForm.form_pull (P Hm : Matrix (Fin g) (Fin g) ℂ)
    (z w : Fin g → ℂ) :
    (P *ᵥ z) ⬝ᵥ Hm *ᵥ star (P *ᵥ w) = z ⬝ᵥ (Pᵀ * Hm * P.map star) *ᵥ star w := by
  rw [star_mulVec, ← mulVec_transpose, conjTranspose, ← transpose_map, transpose_transpose,
    dotProduct_comm, dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, mulVec_mulVec,
    mulVec_mulVec, Matrix.mul_assoc]

open Complex Matrix Filter Topology in
open scoped BigOperators Real in
variable {g : ℕ} in
/- English proof (translation)
Simplify using `[Pi.star_single]`.
-/
theorem _root_.GlobalTheory.SiegelNormalForm.form_single (Y : Matrix (Fin g) (Fin g) ℂ)
    (i j : Fin g) :
    (Pi.single i 1 : Fin g → ℂ) ⬝ᵥ Y *ᵥ star (Pi.single j 1 : Fin g → ℂ) = Y i j := by
  simp [Pi.star_single]

open Complex Matrix Filter Topology in
open scoped BigOperators Real in
variable {g : ℕ} in
/- English proof (translation)
Rewrite using `[← star_dotProduct_star, star_mulVec, star_star, hH.eq, dotProduct_mulVec]`.
-/
theorem _root_.GlobalTheory.SiegelNormalForm.form_conj {Hm : Matrix (Fin g) (Fin g) ℂ}
    (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    star (z ⬝ᵥ Hm *ᵥ star w) = w ⬝ᵥ Hm *ᵥ star z := by
  rw [← star_dotProduct_star, star_mulVec, star_star, hH.eq, dotProduct_mulVec]

open Complex Matrix Filter Topology in
open scoped BigOperators Real in
variable {g : ℕ} in

/- English proof (translation)
Assume the negation of the conclusion as `hP`. Establish `hdet : P.det = 0`. Rewrite `hP` using `[isUnit_iff_isUnit_det, isUnit_iff_ne_zero]`. Conclude with `not_not.mp hP`. Establish `hYdet : Y.det = 0`.

Establish `h1 : (Y.map ((↑) : ℝ → ℂ)).det = 0`. Rewrite using `[← hY, det_mul, det_mul, det_transpose, hdet]`. Simplify using the standard rewrite rules. Establish `h2 : ((Y.det : ℝ) : ℂ) = (Y.map ((↑) : ℝ → ℂ)).det` using `RingHom.map_det Complex.ofRealHom Y`. Conclude with `h2.trans h1` after adjusting the coercions.

Take `⟨x, hx0, hx⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr hYdet`. Use `set xc : Fin g → ℂ := fun i => (x i : ℂ) with hxc`. Establish `hYx : (Y.map ((↑) : ℝ → ℂ)) *ᵥ xc = 0`. Use extensionality with `i`. Use `congrFun hx i` as an intermediate fact.

Simplify using `only [mulVec, dotProduct, Pi.zero_apply, map_apply, hxc] at this ⊢`. Conclude with `this` after adjusting the coercions. Establish `hstar : star xc = xc`. Use extensionality with `i`. Simplify using `[hxc]`.

Establish `hPx : P *ᵥ xc = 0`. Assume the negation of the conclusion as `hne`. Use `hpos _ hne` as an intermediate fact. Rewrite `this` using `[_root_.GlobalTheory.SiegelNormalForm.form_pull, hY, hstar, hYx]`. Simplify using `at this`.

Establish `hsum : ∀ u : Fin g → ℂ, (P *ᵥ xc) ⬝ᵥ u = ∑ i, xc i * ((P *ᵥ Pi.single i 1) ⬝ᵥ u)`. Introduce `u`. Simplify using `only [mulVec_single_one]`. Simplify using `only [mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul, transpose_apply]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [Matrix.col_apply]`. Expand and normalize the polynomial expressions, which then agree. Apply `hx0` to reduce the goal to its premises. Use extensionality with `j`.

Establish `h` using `congrArg Complex.im (hsum (Hm *ᵥ star (f j)))`. Rewrite `h` using `[hPx, zero_dotProduct, Complex.zero_im, Complex.im_sum]`. Simplify using `only [hxc, Complex.im_ofReal_mul, hf, mul_ite, mul_neg, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h`. Simplify using `using h.symm`.
-/
theorem _root_.GlobalTheory.SiegelNormalForm.isUnit_of_lagrangian (P Hm : Matrix (Fin g) (Fin g) ℂ)
    (f : Fin g → Fin g → ℂ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm *ᵥ (star z)).re)
    (Y : Matrix (Fin g) (Fin g) ℝ) (hY : Pᵀ * Hm * P.map star = Y.map (↑))
    (hf : ∀ i j, ((P *ᵥ Pi.single i 1) ⬝ᵥ Hm *ᵥ star (f j)).im = if i = j then -1 else 0) :
    IsUnit P := by
  by_contra hP
  have hdet : P.det = 0 := by
    rw [isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hP
    exact not_not.mp hP
  have hYdet : Y.det = 0 := by
    have h1 : (Y.map ((↑) : ℝ → ℂ)).det = 0 := by
      rw [← hY, det_mul, det_mul, det_transpose, hdet]
      simp
    have h2 : ((Y.det : ℝ) : ℂ) = (Y.map ((↑) : ℝ → ℂ)).det :=
      RingHom.map_det Complex.ofRealHom Y
    exact_mod_cast h2.trans h1
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hYdet
  set xc : Fin g → ℂ := fun i => (x i : ℂ) with hxc
  have hYx : (Y.map ((↑) : ℝ → ℂ)) *ᵥ xc = 0 := by
    ext i
    have := congrFun hx i
    simp only [mulVec, dotProduct, Pi.zero_apply, map_apply, hxc] at this ⊢
    exact_mod_cast this
  have hstar : star xc = xc := by
    ext i
    simp [hxc]
  have hPx : P *ᵥ xc = 0 := by
    by_contra hne
    have := hpos _ hne
    rw [_root_.GlobalTheory.SiegelNormalForm.form_pull, hY, hstar, hYx] at this
    simp at this
  have hsum : ∀ u : Fin g → ℂ,
      (P *ᵥ xc) ⬝ᵥ u = ∑ i, xc i * ((P *ᵥ Pi.single i 1) ⬝ᵥ u) := by
    intro u
    simp only [mulVec_single_one]
    simp only [mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul, transpose_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.col_apply]
    ring
  apply hx0
  ext j
  have h := congrArg Complex.im (hsum (Hm *ᵥ star (f j)))
  rw [hPx, zero_dotProduct, Complex.zero_im, Complex.im_sum] at h
  simp only [hxc, Complex.im_ofReal_mul, hf, mul_ite, mul_neg, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  simpa using h.symm

open Complex Matrix Filter Topology in
open scoped BigOperators Real in
variable {g : ℕ} in

/- English proof (translation)
Use `set B : Matrix (Fin g) (Fin g) ℝ := τ.map Complex.im with hBdef`. Establish `e1` using `h₁`. Establish `e2` using `h₂`. Simplify using `[mulVec, dotProduct, Complex.im_sum, Pi.single_apply] at e1 e2`. Establish `hsymY : ∀ i j, Y j i = Y i j` using `fun i j => by`.

Simplify using `using hY.isHermitian.apply i j`. Establish `hrow : ∀ a i, ∑ x, Y a x * (τ x i).im = if a = i then 1 else 0`. Introduce `a i`. Use `e1 a i` as an intermediate fact. Apply the tactic sequence `split_ifs at this ⊢ <;> linarith`.

Establish `hYB : Y * B = 1`. Use extensionality with `a i`. Simplify using `only [mul_apply, one_apply, hBdef, map_apply]`. Conclude with `hrow a i`. Establish `hBY : B * Y = 1` using `mul_eq_one_comm.mp hYB`.

Establish `hYt : Yᵀ = Y`. Use extensionality with `i j`. Conclude with `hsymY i j`. Establish `hBt : Bᵀ = B`. Combine the equalities or inequalities in the displayed calculation.

Establish `hsecond : ∀ i j, ∑ x, (τ x i).im * ∑ y, Y x y * (τ y j).re = (τ i j).re`. Introduce `i j`. Repeatedly rewrite using `[Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Establish `h : ∀ y, ∑ x, (τ x i).im * (Y x y * (τ y j).re) = (if y = i then 1 else 0) * (τ y j).re`.

Introduce `y`. Rewrite using `[← hrow y i, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[hsymY y x]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `[h]`. Establish `hre : ∀ i j, (τ j i).re = (τ i j).re`. Introduce `i j`. Use `e2 i j` as an intermediate fact. Simplify using `only [hrow, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, hsecond] at this`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `him : ∀ i j, (τ j i).im = (τ i j).im`. Introduce `i j`. Use `congrFun (congrFun hBt i) j` as an intermediate fact. Simplify `this` using `[hBdef]`.

Use `⟨IsSymm.ext fun i j => Complex.ext (hre i j) (him i j), ?_, hYB⟩` and prove the remaining obligations. Rewrite using `[← Matrix.inv_eq_right_inv hYB]`. Conclude with `hY.inv`.
-/
theorem _root_.GlobalTheory.SiegelNormalForm.siegel_of_relations (Y : Matrix (Fin g) (Fin g) ℝ)
    (hY : Y.PosDef) (τ : Matrix (Fin g) (Fin g) ℂ)
    (h₁ : ∀ i j, ((Pi.single i 1 : Fin g → ℂ) ⬝ᵥ Y.map (↑) *ᵥ star (τ *ᵥ Pi.single j 1)).im =
      if i = j then -1 else 0)
    (h₂ : ∀ i j, ((τ *ᵥ Pi.single i 1) ⬝ᵥ Y.map (↑) *ᵥ star (τ *ᵥ Pi.single j 1)).im = 0) :
    τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ Y * τ.map Complex.im = 1 := by
  set B : Matrix (Fin g) (Fin g) ℝ := τ.map Complex.im with hBdef
  have e1 := h₁
  have e2 := h₂
  simp [mulVec, dotProduct, Complex.im_sum, Pi.single_apply] at e1 e2
  have hsymY : ∀ i j, Y j i = Y i j := fun i j => by
    simpa using hY.isHermitian.apply i j
  have hrow : ∀ a i, ∑ x, Y a x * (τ x i).im = if a = i then 1 else 0 := by
    intro a i
    have := e1 a i
    split_ifs at this ⊢ <;> linarith
  have hYB : Y * B = 1 := by
    ext a i
    simp only [mul_apply, one_apply, hBdef, map_apply]
    exact hrow a i
  have hBY : B * Y = 1 := mul_eq_one_comm.mp hYB
  have hYt : Yᵀ = Y := by
    ext i j
    exact hsymY i j
  have hBt : Bᵀ = B := by
    calc Bᵀ = Bᵀ * (Y * B) := by rw [hYB, Matrix.mul_one]
      _ = (Y * B)ᵀ * B := by rw [transpose_mul, hYt, Matrix.mul_assoc]
      _ = B := by rw [hYB, transpose_one, Matrix.one_mul]
  have hsecond : ∀ i j, ∑ x, (τ x i).im * ∑ y, Y x y * (τ y j).re = (τ i j).re := by
    intro i j
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have h : ∀ y, ∑ x, (τ x i).im * (Y x y * (τ y j).re) =
        (if y = i then 1 else 0) * (τ y j).re := by
      intro y
      rw [← hrow y i, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hsymY y x]
      ring
    simp [h]
  have hre : ∀ i j, (τ j i).re = (τ i j).re := by
    intro i j
    have := e2 i j
    simp only [hrow, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, hsecond] at this
    linarith
  have him : ∀ i j, (τ j i).im = (τ i j).im := by
    intro i j
    have := congrFun (congrFun hBt i) j
    simpa [hBdef] using this
  refine ⟨IsSymm.ext fun i j => Complex.ext (hre i j) (him i j), ?_, hYB⟩
  rw [← Matrix.inv_eq_right_inv hYB]
  exact hY.inv

noncomputable def quad (Y : Matrix (Fin g) (Fin g) ℂ) (c z : Fin g → ℂ) : ℂ :=
  Real.pi / 2 * (z ⬝ᵥ Y *ᵥ z) + c ⬝ᵥ z

open Complex Matrix Filter Topology in
open scoped BigOperators Real in
variable {g : ℕ} in
/- English proof (translation)
Unfold `_root_.GlobalTheory.SiegelNormalForm.quad`. Simplify using `only [dotProduct, mulVec]`. Use `fun_prop`.
-/
theorem _root_.GlobalTheory.SiegelNormalForm.quad_differentiable (Y : Matrix (Fin g) (Fin g) ℂ)
    (c : Fin g → ℂ) : Differentiable ℂ (_root_.GlobalTheory.SiegelNormalForm.quad Y c) := by
  unfold _root_.GlobalTheory.SiegelNormalForm.quad
  simp only [dotProduct, mulVec]
  fun_prop

open Complex Matrix Filter Topology in
open scoped BigOperators Real in
variable {g : ℕ} in
/- English proof (translation)
Establish `hwz : w ⬝ᵥ Y *ᵥ z = z ⬝ᵥ Y *ᵥ w`. Rewrite using `[dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, hY.eq]`. Simplify using `only [_root_.GlobalTheory.SiegelNormalForm.quad, mulVec_add, dotProduct_add, add_dotProduct, hwz]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem _root_.GlobalTheory.SiegelNormalForm.quad_add_sub {Y : Matrix (Fin g) (Fin g) ℂ} (hY : Y.IsSymm)
    (c z w : Fin g → ℂ) :
    _root_.GlobalTheory.SiegelNormalForm.quad Y c (z + w) - _root_.GlobalTheory.SiegelNormalForm.quad Y c z =
      Real.pi * (z ⬝ᵥ Y *ᵥ w) + _root_.GlobalTheory.SiegelNormalForm.quad Y c w := by
  have hwz : w ⬝ᵥ Y *ᵥ z = z ⬝ᵥ Y *ᵥ w := by
    rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, hY.eq]
  simp only [_root_.GlobalTheory.SiegelNormalForm.quad, mulVec_add, dotProduct_add, add_dotProduct, hwz]
  ring

open Complex Matrix Filter Topology in
open scoped BigOperators Real in
variable {g : ℕ} in

/- English proof (translation)
Introduce `g Λ hdisc hspan Hm χ Ef hH hpos hχ hEf hbij`. Use `haveI : IsZLattice ℝ Λ := ⟨hspan⟩`. Establish `hrank : Module.finrank ℤ Λ = 2 * g`. Rewrite using `[ZLattice.rank ℝ Λ, Module.finrank_pi_fintype]`. Simplify using `[Complex.finrank_real_complex]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hreal : ∀ v : Fin g → ℂ, (v ⬝ᵥ Hm *ᵥ star v).im = 0` using `fun v => Complex.conj_eq_iff_im.mp (_root_.GlobalTheory.SiegelNormalForm.form_conj hH v v)`. Establish `halt : (-Ef).IsAlt`. Introduce `l`. Establish `h` using `hEf l l`.

Rewrite `h` using `[hreal]`. Establish `h' : Ef l l = 0` using `by exact_mod_cast h`. Simplify using `[h']`. Take `⟨b, hb⟩` from `_root_.GlobalTheory.exists_isSymplecticBasis_of_finrank halt (_root_.GlobalTheory.bijective_neg_bilinForm hbij) hrank`. Establish `hEll : ∀ i j, Ef (b (Sum.inl i)) (b (Sum.inl j)) = 0` using `fun i j => by`.

Simplify using `using hb.left_left i j`. Establish `hErr : ∀ i j, Ef (b (Sum.inr i)) (b (Sum.inr j)) = 0` using `fun i j => by`. Simplify using `using hb.right_right i j`. Establish `hElr : ∀ i j, (Ef (b (Sum.inl i)) (b (Sum.inr j)) : ℝ) = if i = j then -1 else 0`. Introduce `i j`.

Establish `h` using `hb.left_right i j`. Simplify using `only [LinearMap.neg_apply] at h`. Use `split_ifs at h ⊢ with hij`. Establish `h' : Ef (b (Sum.inl i)) (b (Sum.inr j)) = -1` using `by omega`. Simplify using `[h']`.

Establish `h' : Ef (b (Sum.inl i)) (b (Sum.inr j)) = 0` using `by omega`. Simplify using `[h']`. Take `⟨P, hPdef⟩ : ∃ P : Matrix (Fin g) (Fin g) ℂ, P = Matrix.of fun k i => (b (Sum.inl i) : Fin g → ℂ) k` from `⟨_, rfl⟩`. Take `⟨P', hP'def⟩ : ∃ P' : Matrix (Fin g) (Fin g) ℂ, P' = Matrix.of fun k j => (b (Sum.inr j) : Fin g → ℂ) k` from `⟨_, rfl⟩`. Establish `hPcol : ∀ i, P *ᵥ Pi.single i 1 = (b (Sum.inl i) : Fin g → ℂ)`.

Introduce `i`. Rewrite using `[mulVec_single_one]`. Use extensionality with `k`. Simplify using `[hPdef]`. Establish `hP'col : ∀ j, P' *ᵥ Pi.single j 1 = (b (Sum.inr j) : Fin g → ℂ)`.

Introduce `j`. Rewrite using `[mulVec_single_one]`. Use extensionality with `k`. Simplify using `[hP'def]`. Apply the tactic sequence `have hMentry : ∀ i j, (Pᵀ * Hm * P.map star) i j = (b (Sum.inl i) : Fin g → ℂ) ⬝ᵥ Hm *ᵥ star (b (Sum.inl j) : Fin g → ℂ) := by`.

Introduce `i j`. Rewrite using `[← _root_.GlobalTheory.SiegelNormalForm.form_single (Pᵀ * Hm * P.map star) i j, ← _root_.GlobalTheory.SiegelNormalForm.form_pull, hPcol, hPcol]`. Take `⟨Y, hYdef⟩ : ∃ Y : Matrix (Fin g) (Fin g) ℝ, Y = (Pᵀ * Hm * P.map star).map Complex.re` from `⟨_, rfl⟩`. Establish `hMY : Pᵀ * Hm * P.map star = Y.map (↑)`. Use extensionality with `i j`.

Apply `Complex.ext` to reduce the goal to its premises. Simplify using `[hYdef]`. Rewrite using `[map_apply, Complex.ofReal_im, hMentry, ← hEf, hEll]`. Simplify using the standard rewrite rules. Establish `hunit : IsUnit P`.

Use `_root_.GlobalTheory.SiegelNormalForm.isUnit_of_lagrangian P Hm (fun j => (b (Sum.inr j) : Fin g → ℂ)) hpos Y hMY fun i j => ?_` and prove the remaining obligations. Rewrite using `[hPcol, ← hEf, hElr]`. Establish `hinj : Function.Injective P.mulVec` using `mulVec_injective_iff_isUnit.mpr hunit`. Establish `hrel : ∀ u v : Fin g → ℂ, u ⬝ᵥ Y.map (↑) *ᵥ star v = (P *ᵥ u) ⬝ᵥ Hm *ᵥ star (P *ᵥ v)`. Introduce `u v`.

Rewrite using `[_root_.GlobalTheory.SiegelNormalForm.form_pull, hMY]`. Establish `hYsymm : ∀ i j, Y j i = Y i j`. Introduce `i j`. Simplify using `only [hYdef, map_apply, hMentry]`. Rewrite using `[← _root_.GlobalTheory.SiegelNormalForm.form_conj hH]`.

Simplify using the standard rewrite rules. Establish `hYpos : Y.PosDef`. Rewrite using `[posDef_iff_dotProduct_mulVec]`. Use `⟨IsHermitian.ext fun i j => by simpa using hYsymm i j, fun x hx => ?_⟩` and prove the remaining obligations. Use `set xc : Fin g → ℂ := fun i => (x i : ℂ) with hxc`.

Establish `hxc0 : xc ≠ 0`. Introduce `h`. Apply `hx` to reduce the goal to its premises. Use extensionality with `i`. Simplify `congrFun h i` using `[hxc]`.

Establish `hPx : P *ᵥ xc ≠ 0` using `fun h => hxc0 (hinj (h.trans (mulVec_zero P).symm))`. Establish `h` using `hpos _ hPx`. Rewrite `h` using `[← hrel]`. Establish `hre : (xc ⬝ᵥ Y.map (↑) *ᵥ star xc).re = star x ⬝ᵥ Y *ᵥ x`. Simplify using `[hxc, dotProduct, mulVec, Complex.re_sum]`.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨τ, hτdef⟩ : ∃ τ : Matrix (Fin g) (Fin g) ℂ, τ = P⁻¹ * P'` from `⟨_, rfl⟩`. Establish `hPτ : P * τ = P'`. Rewrite using `[hτdef, ← Matrix.mul_assoc, mul_nonsing_inv _ ((isUnit_iff_isUnit_det P).mp hunit), Matrix.one_mul]`. Establish `hτcol : ∀ j, P *ᵥ (τ *ᵥ Pi.single j 1) = (b (Sum.inr j) : Fin g → ℂ)`.

Introduce `j`. Rewrite using `[mulVec_mulVec, hPτ, hP'col]`. Take `⟨hτsym, hτpos, hYB⟩` from `_root_.GlobalTheory.SiegelNormalForm.siegel_of_relations Y hYpos τ (fun i j => by`. Rewrite using `[hrel, hPcol, hτcol, ← hEf, hElr])`. Use the proof step `(fun i j => by`.

Rewrite using `[hrel, hτcol, hτcol, ← hEf, hErr]`. Use the proof step `simp)`. Establish `hcols : ∀ (A : Matrix (Fin g) (Fin g) ℂ) (v : Fin g → ℂ), A *ᵥ v = ∑ i, v i • (A *ᵥ Pi.single i 1)`. Introduce `A v`. Use extensionality with `k`.

Simplify using `[mulVec, dotProduct, Finset.sum_apply, mul_comm]`. Establish `hχne : ∀ l, χ l ≠ 0` using `fun l h => by simpa [h] using hχ l`. Establish `hYsym' : (Y.map ((↑) : ℝ → ℂ)).IsSymm` using `IsSymm.ext fun i j => by simp [hYsymm]`. Set `φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)` to `P.toLinearEquiv' hunit.invertible`. Establish `hφ : ∀ z, φ z = P *ᵥ z` using `fun z => rfl`.

Set `c : Fin g → ℂ` to `fun i => Complex.log (χ (b (Sum.inl i)))`. Set `Q : (Fin g → ℂ) → ℂ` to `_root_.GlobalTheory.SiegelNormalForm.quad (Y.map (↑)) c`. Establish `hQ : ∀ z w, Q (z + w) - Q z = Real.pi * (z ⬝ᵥ Y.map (↑) *ᵥ w) + Q w` using `fun z w => _root_.GlobalTheory.SiegelNormalForm.quad_add_sub hYsym' c z w`. Establish `hconj_col : ∀ j, (Y.map (↑) : Matrix (Fin g) (Fin g) ℂ) *ᵥ star (τ *ᵥ Pi.single j 1) = (Y.map (↑) : Matrix (Fin g) (Fin g) ℂ) *ᵥ (τ *ᵥ Pi.single j 1) - (2 * I) • Pi.single j 1`. Introduce `j`.

Establish `hv : star (τ *ᵥ Pi.single j 1) = τ *ᵥ Pi.single j 1 - (2 * I) • (fun x => ((τ x j).im : ℂ))`. Use extensionality with `x`. Simplify using `only [mulVec_single_one, Pi.star_apply, transpose_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Apply the tactic sequence `apply Complex.ext <;> simp <;> ring`. Establish `hYim : (Y.map (↑) : Matrix (Fin g) (Fin g) ℂ) *ᵥ (fun x => ((τ x j).im : ℂ)) = Pi.single j 1`.

Use extensionality with `k`. Establish `h` using `congrFun (congrFun hYB k) j`. Simplify using `only [mul_apply, map_apply, one_apply] at h`. Simplify using `only [mulVec, dotProduct, map_apply, Pi.single_apply]`. Establish `h' : ((∑ i, Y k i * (τ i j).im : ℝ) : ℂ) = ((if k = j then 1 else 0 : ℝ) : ℂ)`.

Rewrite using `[h]`. Move the coercions through the operations in `at h'`. Rewrite using `[h']`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[hv, mulVec_sub, mulVec_smul, hYim]`.

Use `⟨φ, τ, Q, fun j => χ (b (Sum.inr j)) * cexp (Real.pi / 2 * ((b (Sum.inr j) : Fin g → ℂ) ⬝ᵥ Hm *ᵥ star (b (Sum.inr j) : Fin g → ℂ)) - Q (τ *ᵥ Pi.single j 1)), hτsym, hτpos, fun z => ?_, _root_.GlobalTheory.SiegelNormalForm.quad_differentiable _ _, by simp [Q, _root_.GlobalTheory.S …` and prove the remaining obligations. Rewrite using `[hφ]`. Prove the components needed by the constructor for the conclusion. Introduce `hz`. Set `l : Λ` to `⟨P *ᵥ z, hz⟩`.

Use `⟨fun i => b.repr l (Sum.inl i), fun j => b.repr l (Sum.inr j), hinj ?_⟩` and prove the remaining obligations. Establish `hl : P *ᵥ z = ((l : Λ) : Fin g → ℂ)` using `rfl`. Rewrite using `[hl, ← b.sum_repr l, Submodule.coe_sum, Fintype.sum_sum_type, mulVec_add, mulVec_mulVec, hPτ, hcols P, hcols P']`. Simplify using `[hPcol, hP'col, Int.cast_smul_eq_zsmul]`. Introduce and unpack `⟨m, n, rfl⟩`.

Rewrite using `[mulVec_add, mulVec_mulVec, hPτ, hcols P, hcols P']`. Use `Λ.add_mem (Λ.sum_mem fun i _ => ?_) (Λ.sum_mem fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[hPcol, Int.cast_smul_eq_zsmul]`. Conclude with `Λ.smul_mem _ (b _).2`. Rewrite using `[hP'col, Int.cast_smul_eq_zsmul]`.

Conclude with `Λ.smul_mem _ (b _).2`. Rewrite `hl` using `[hφ, hPcol]`. Take `rfl : l = b (Sum.inl i)` from `Subtype.ext hl`. Establish `h1 : (P *ᵥ z) ⬝ᵥ Hm *ᵥ star (b (Sum.inl i) : Fin g → ℂ) = z ⬝ᵥ Y.map (↑) *ᵥ Pi.single i 1`. Rewrite using `[← hPcol, ← hrel, Pi.star_single, star_one]`.

Establish `h2 : (b (Sum.inl i) : Fin g → ℂ) ⬝ᵥ Hm *ᵥ star (b (Sum.inl i) : Fin g → ℂ) = Pi.single i 1 ⬝ᵥ Y.map (↑) *ᵥ Pi.single i 1`. Rewrite using `[← hPcol, ← hrel, Pi.star_single, star_one]`. Rewrite using `[hφ, h1, h2, hQ]`. Simplify using `only [Q, _root_.GlobalTheory.SiegelNormalForm.quad, dotProduct_single, mul_one]`. Rewrite using `[← add_assoc, Complex.exp_add _ (c i), Complex.exp_log (hχne _), mul_comm]`.

Rewrite `hl` using `[hφ, hτcol]`. Take `rfl : l = b (Sum.inr j)` from `Subtype.ext hl`. Establish `h1 : (P *ᵥ z) ⬝ᵥ Hm *ᵥ star (b (Sum.inr j) : Fin g → ℂ) = z ⬝ᵥ Y.map (↑) *ᵥ (τ *ᵥ Pi.single j 1) - 2 * I * z j`. Rewrite using `[← hτcol, ← hrel, hconj_col, dotProduct_sub, dotProduct_smul, dotProduct_single, smul_eq_mul, mul_one]`. Rewrite using `[hφ, h1, hQ]`.

Simplify using `only`. Simplify using `only [mul_assoc, ← Complex.exp_add]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem _root_.GlobalTheory.SiegelNormalForm.exists_normal_form : (∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (Ef : LinearMap.BilinForm ℤ Λ), Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ l, ‖χ l‖ = 1) → (∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im) → Function.Bijective Ef → ∃ (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (τ : Matrix (Fin g) (Fin g) ℂ) (Q : (Fin g → ℂ) → ℂ) (b : Fin g → ℂ), τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ (∀ z, φ z ∈ Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) ∧ Differentiable ℂ Q ∧ Q 0 = 0 ∧ (∀ j, b j ≠ 0) ∧ (∀ (i : Fin g) (l : Λ) z, (l : Fin g → ℂ) = φ (Pi.single i 1) → (χ l * cexp (Real.pi * (φ z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) = cexp (Q (z + Pi.single i 1) - Q z)) ∧ (∀ (j : Fin g) (l : Λ) z, (l : Fin g → ℂ) = φ (τ.mulVec (Pi.single j 1)) → (χ l * cexp (Real.pi * (φ z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) = b j * cexp (-(2 * Real.pi * I) * z j) * cexp (Q (z + τ.mulVec (Pi.single j 1)) - Q z))) := by
  intro g Λ hdisc hspan Hm χ Ef hH hpos hχ hEf hbij
  haveI : IsZLattice ℝ Λ := ⟨hspan⟩
  have hrank : Module.finrank ℤ Λ = 2 * g := by
    rw [ZLattice.rank ℝ Λ, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex]
    ring
  have hreal : ∀ v : Fin g → ℂ, (v ⬝ᵥ Hm *ᵥ star v).im = 0 := fun v =>
    Complex.conj_eq_iff_im.mp (_root_.GlobalTheory.SiegelNormalForm.form_conj hH v v)
  have halt : (-Ef).IsAlt := by
    intro l
    have h := hEf l l
    rw [hreal] at h
    have h' : Ef l l = 0 := by exact_mod_cast h
    simp [h']
  obtain ⟨b, hb⟩ := _root_.GlobalTheory.exists_isSymplecticBasis_of_finrank halt (_root_.GlobalTheory.bijective_neg_bilinForm hbij) hrank
  have hEll : ∀ i j, Ef (b (Sum.inl i)) (b (Sum.inl j)) = 0 := fun i j => by
    simpa using hb.left_left i j
  have hErr : ∀ i j, Ef (b (Sum.inr i)) (b (Sum.inr j)) = 0 := fun i j => by
    simpa using hb.right_right i j
  have hElr : ∀ i j, (Ef (b (Sum.inl i)) (b (Sum.inr j)) : ℝ) = if i = j then -1 else 0 := by
    intro i j
    have h := hb.left_right i j
    simp only [LinearMap.neg_apply] at h
    split_ifs at h ⊢ with hij
    · have h' : Ef (b (Sum.inl i)) (b (Sum.inr j)) = -1 := by omega
      simp [h']
    · have h' : Ef (b (Sum.inl i)) (b (Sum.inr j)) = 0 := by omega
      simp [h']
  obtain ⟨P, hPdef⟩ : ∃ P : Matrix (Fin g) (Fin g) ℂ,
      P = Matrix.of fun k i => (b (Sum.inl i) : Fin g → ℂ) k := ⟨_, rfl⟩
  obtain ⟨P', hP'def⟩ : ∃ P' : Matrix (Fin g) (Fin g) ℂ,
      P' = Matrix.of fun k j => (b (Sum.inr j) : Fin g → ℂ) k := ⟨_, rfl⟩
  have hPcol : ∀ i, P *ᵥ Pi.single i 1 = (b (Sum.inl i) : Fin g → ℂ) := by
    intro i
    rw [mulVec_single_one]
    ext k
    simp [hPdef]
  have hP'col : ∀ j, P' *ᵥ Pi.single j 1 = (b (Sum.inr j) : Fin g → ℂ) := by
    intro j
    rw [mulVec_single_one]
    ext k
    simp [hP'def]
  have hMentry : ∀ i j, (Pᵀ * Hm * P.map star) i j =
      (b (Sum.inl i) : Fin g → ℂ) ⬝ᵥ Hm *ᵥ star (b (Sum.inl j) : Fin g → ℂ) := by
    intro i j
    rw [← _root_.GlobalTheory.SiegelNormalForm.form_single (Pᵀ * Hm * P.map star) i j,
      ← _root_.GlobalTheory.SiegelNormalForm.form_pull, hPcol, hPcol]
  obtain ⟨Y, hYdef⟩ : ∃ Y : Matrix (Fin g) (Fin g) ℝ,
      Y = (Pᵀ * Hm * P.map star).map Complex.re := ⟨_, rfl⟩
  have hMY : Pᵀ * Hm * P.map star = Y.map (↑) := by
    ext i j
    apply Complex.ext
    · simp [hYdef]
    · rw [map_apply, Complex.ofReal_im, hMentry, ← hEf, hEll]
      simp
  have hunit : IsUnit P := by
    refine _root_.GlobalTheory.SiegelNormalForm.isUnit_of_lagrangian P Hm (fun j => (b (Sum.inr j) : Fin g → ℂ))
      hpos Y hMY fun i j => ?_
    rw [hPcol, ← hEf, hElr]
  have hinj : Function.Injective P.mulVec := mulVec_injective_iff_isUnit.mpr hunit
  have hrel : ∀ u v : Fin g → ℂ,
      u ⬝ᵥ Y.map (↑) *ᵥ star v = (P *ᵥ u) ⬝ᵥ Hm *ᵥ star (P *ᵥ v) := by
    intro u v
    rw [_root_.GlobalTheory.SiegelNormalForm.form_pull, hMY]
  have hYsymm : ∀ i j, Y j i = Y i j := by
    intro i j
    simp only [hYdef, map_apply, hMentry]
    rw [← _root_.GlobalTheory.SiegelNormalForm.form_conj hH]
    simp
  have hYpos : Y.PosDef := by
    rw [posDef_iff_dotProduct_mulVec]
    refine ⟨IsHermitian.ext fun i j => by simpa using hYsymm i j, fun x hx => ?_⟩
    set xc : Fin g → ℂ := fun i => (x i : ℂ) with hxc
    have hxc0 : xc ≠ 0 := by
      intro h
      apply hx
      ext i
      simpa [hxc] using congrFun h i
    have hPx : P *ᵥ xc ≠ 0 := fun h => hxc0 (hinj (h.trans (mulVec_zero P).symm))
    have h := hpos _ hPx
    rw [← hrel] at h
    have hre : (xc ⬝ᵥ Y.map (↑) *ᵥ star xc).re = star x ⬝ᵥ Y *ᵥ x := by
      simp [hxc, dotProduct, mulVec, Complex.re_sum]
    linarith
  obtain ⟨τ, hτdef⟩ : ∃ τ : Matrix (Fin g) (Fin g) ℂ, τ = P⁻¹ * P' := ⟨_, rfl⟩
  have hPτ : P * τ = P' := by
    rw [hτdef, ← Matrix.mul_assoc, mul_nonsing_inv _ ((isUnit_iff_isUnit_det P).mp hunit),
      Matrix.one_mul]
  have hτcol : ∀ j, P *ᵥ (τ *ᵥ Pi.single j 1) = (b (Sum.inr j) : Fin g → ℂ) := by
    intro j
    rw [mulVec_mulVec, hPτ, hP'col]
  obtain ⟨hτsym, hτpos, hYB⟩ := _root_.GlobalTheory.SiegelNormalForm.siegel_of_relations Y hYpos τ
    (fun i j => by
      rw [hrel, hPcol, hτcol, ← hEf, hElr])
    (fun i j => by
      rw [hrel, hτcol, hτcol, ← hEf, hErr]
      simp)

  have hcols : ∀ (A : Matrix (Fin g) (Fin g) ℂ) (v : Fin g → ℂ),
      A *ᵥ v = ∑ i, v i • (A *ᵥ Pi.single i 1) := by
    intro A v
    ext k
    simp [mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hχne : ∀ l, χ l ≠ 0 := fun l h => by simpa [h] using hχ l
  have hYsym' : (Y.map ((↑) : ℝ → ℂ)).IsSymm := IsSymm.ext fun i j => by simp [hYsymm]
  let φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := P.toLinearEquiv' hunit.invertible
  have hφ : ∀ z, φ z = P *ᵥ z := fun z => rfl
  let c : Fin g → ℂ := fun i => Complex.log (χ (b (Sum.inl i)))
  let Q : (Fin g → ℂ) → ℂ := _root_.GlobalTheory.SiegelNormalForm.quad (Y.map (↑)) c
  have hQ : ∀ z w, Q (z + w) - Q z = Real.pi * (z ⬝ᵥ Y.map (↑) *ᵥ w) + Q w := fun z w =>
    _root_.GlobalTheory.SiegelNormalForm.quad_add_sub hYsym' c z w
  have hconj_col : ∀ j, (Y.map (↑) : Matrix (Fin g) (Fin g) ℂ) *ᵥ star (τ *ᵥ Pi.single j 1) =
      (Y.map (↑) : Matrix (Fin g) (Fin g) ℂ) *ᵥ (τ *ᵥ Pi.single j 1) - (2 * I) • Pi.single j 1 := by
    intro j
    have hv : star (τ *ᵥ Pi.single j 1) =
        τ *ᵥ Pi.single j 1 - (2 * I) • (fun x => ((τ x j).im : ℂ)) := by
      ext x
      simp only [mulVec_single_one, Pi.star_apply, transpose_apply, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul]
      apply Complex.ext <;> simp <;> ring
    have hYim : (Y.map (↑) : Matrix (Fin g) (Fin g) ℂ) *ᵥ (fun x => ((τ x j).im : ℂ)) =
        Pi.single j 1 := by
      ext k
      have h := congrFun (congrFun hYB k) j
      simp only [mul_apply, map_apply, one_apply] at h
      simp only [mulVec, dotProduct, map_apply, Pi.single_apply]
      have h' : ((∑ i, Y k i * (τ i j).im : ℝ) : ℂ) = ((if k = j then 1 else 0 : ℝ) : ℂ) := by
        rw [h]
      push_cast at h'
      rw [h']
      split_ifs <;> simp
    rw [hv, mulVec_sub, mulVec_smul, hYim]
  refine ⟨φ, τ, Q, fun j => χ (b (Sum.inr j)) * cexp (Real.pi / 2 *
      ((b (Sum.inr j) : Fin g → ℂ) ⬝ᵥ Hm *ᵥ star (b (Sum.inr j) : Fin g → ℂ)) -
      Q (τ *ᵥ Pi.single j 1)), hτsym, hτpos, fun z => ?_,
    _root_.GlobalTheory.SiegelNormalForm.quad_differentiable _ _, by simp [Q, _root_.GlobalTheory.SiegelNormalForm.quad],
    fun j => mul_ne_zero (hχne _) (Complex.exp_ne_zero _), fun i l z hl => ?_,
    fun j l z hl => ?_⟩
  · rw [hφ]
    constructor
    · intro hz
      let l : Λ := ⟨P *ᵥ z, hz⟩
      refine ⟨fun i => b.repr l (Sum.inl i), fun j => b.repr l (Sum.inr j), hinj ?_⟩
      have hl : P *ᵥ z = ((l : Λ) : Fin g → ℂ) := rfl
      rw [hl, ← b.sum_repr l, Submodule.coe_sum, Fintype.sum_sum_type, mulVec_add, mulVec_mulVec,
        hPτ, hcols P, hcols P']
      simp [hPcol, hP'col, Int.cast_smul_eq_zsmul]
    · rintro ⟨m, n, rfl⟩
      rw [mulVec_add, mulVec_mulVec, hPτ, hcols P, hcols P']
      refine Λ.add_mem (Λ.sum_mem fun i _ => ?_) (Λ.sum_mem fun j _ => ?_)
      · rw [hPcol, Int.cast_smul_eq_zsmul]
        exact Λ.smul_mem _ (b _).2
      · rw [hP'col, Int.cast_smul_eq_zsmul]
        exact Λ.smul_mem _ (b _).2
  · rw [hφ, hPcol] at hl
    obtain rfl : l = b (Sum.inl i) := Subtype.ext hl
    have h1 : (P *ᵥ z) ⬝ᵥ Hm *ᵥ star (b (Sum.inl i) : Fin g → ℂ) =
        z ⬝ᵥ Y.map (↑) *ᵥ Pi.single i 1 := by
      rw [← hPcol, ← hrel, Pi.star_single, star_one]
    have h2 : (b (Sum.inl i) : Fin g → ℂ) ⬝ᵥ Hm *ᵥ star (b (Sum.inl i) : Fin g → ℂ) =
        Pi.single i 1 ⬝ᵥ Y.map (↑) *ᵥ Pi.single i 1 := by
      rw [← hPcol, ← hrel, Pi.star_single, star_one]
    rw [hφ, h1, h2, hQ]
    simp only [Q, _root_.GlobalTheory.SiegelNormalForm.quad, dotProduct_single, mul_one]
    rw [← add_assoc, Complex.exp_add _ (c i), Complex.exp_log (hχne _), mul_comm]
  · rw [hφ, hτcol] at hl
    obtain rfl : l = b (Sum.inr j) := Subtype.ext hl
    have h1 : (P *ᵥ z) ⬝ᵥ Hm *ᵥ star (b (Sum.inr j) : Fin g → ℂ) =
        z ⬝ᵥ Y.map (↑) *ᵥ (τ *ᵥ Pi.single j 1) - 2 * I * z j := by
      rw [← hτcol, ← hrel, hconj_col, dotProduct_sub, dotProduct_smul, dotProduct_single,
        smul_eq_mul, mul_one]
    rw [hφ, h1, hQ]
    dsimp only
    simp only [mul_assoc, ← Complex.exp_add]
    congr 2
    ring

end GlobalTheory.SiegelNormalForm
