import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultOfNotMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VecMulVecComm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffEqTensorSquareTopCoefficientStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowGrassmannBlockCurvatureSupertraceZeroStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyRevMulCharpolyRevEqOneOfTracePowAddEqZerStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernCurvatureInvOneSubConjMulTransposeAtZeroStatement

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
open scoped Matrix

namespace GlobalTheory.PointChernRel

open GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointChern GlobalTheory.GrassModel MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField

/- English proof (translation)
Substitute `h` using the available equality. Simplify using the standard rewrite rules.
-/
theorem chernPoly_reindex {n m p : ℕ} (h : p = m) (K : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin p) (Fin p) ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) (k : ℕ) :
    chernPoly (fun u => Matrix.reindex (finCongr h) (finCongr h) (K u)) v k = chernPoly K v k := by
  subst h
  simp

/- English proof (translation)
Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using `only [curvPoly, Matrix.of_apply, GlobalTheory.T.chernCurvature_inv_one_sub_conj_mul_transpose_at_zero, Matrix.neg_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, coordVec, PiLp.single_apply, apply_ite star, star_one, star_zero, mul_ite, mul_one, mul_zero, map_neg, map_sum, n …`. Establish `h (x y : Fin n) (c : Fin s) : C (if f j c = y then if g i c = x then (1 : ℂ) else 0 else 0) * X (x, y) = if (g i c, f j c) = (x, y) then X (g i c, f j c) else (0 : MvPolynomial (Fin n × Fin n) ℂ)`. Apply the tactic sequence `by_cases h1 : f j c = y <;> by_cases h2 : g i c = x <;> simp [h1, h2]`. Simplify using `only [h]`.

Rewrite using `[← Fintype.sum_prod_type' (f := fun x y => ∑ c, if (g i c, f j c) = (x, y) then X (g i c, f j c) else 0), Finset.sum_comm]`. Simplify using the standard rewrite rules.
-/
theorem curvPoly_model {n r s : ℕ} (f g : Fin r → Fin s → Fin n) :
    curvPoly (fun u : ReciprocityTheory.L2DbarEstimates.V n =>
      (1 - (Matrix.of fun i j => u (f i j)).map (starRingEnd ℂ) * (Matrix.of fun i j => u (g i j))ᵀ)⁻¹) 0 =
      -Matrix.of fun i j => ∑ c, X (g i c, f j c) := by
  refine Matrix.ext fun i j => ?_
  simp only [curvPoly, Matrix.of_apply, GlobalTheory.T.chernCurvature_inv_one_sub_conj_mul_transpose_at_zero, Matrix.neg_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    coordVec, PiLp.single_apply, apply_ite star, star_one, star_zero, mul_ite, mul_one, mul_zero, map_neg, map_sum,
    neg_mul, Finset.sum_neg_distrib, Finset.sum_mul, neg_inj]
  have h (x y : Fin n) (c : Fin s) : C (if f j c = y then if g i c = x then (1 : ℂ) else 0 else 0) * X (x, y) =
      if (g i c, f j c) = (x, y) then X (g i c, f j c) else (0 : MvPolynomial (Fin n × Fin n) ℂ) := by
    by_cases h1 : f j c = y <;> by_cases h2 : g i c = x <;> simp [h1, h2]
  simp only [h]
  rw [← Fintype.sum_prod_type' (f := fun x y => ∑ c, if (g i c, f j c) = (x, y) then X (g i c, f j c) else 0), Finset.sum_comm]
  simp

/- English proof (translation)
Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p q hp hq => simp [Polynomial.add_comp, hp, hq, mul_add]`. Consider the case `monomial m a`. Rewrite using `[← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_pow_comp, neg_pow, ← mul_assoc, show ((-1 : Polynomial R)) ^ m = Polynomial.C ((-1) ^ m) by simp, ← Polynomial.C_mul, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X_pow]`. Use `split_ifs with h`.

Substitute `h` using the available equality. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.
-/
theorem coeff_comp_neg_X' {R : Type} [CommRing R] (p : Polynomial R) (b : ℕ) :
    (p.comp (-Polynomial.X)).coeff b = (-1) ^ b * p.coeff b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [Polynomial.add_comp, hp, hq, mul_add]
  | monomial m a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_pow_comp, neg_pow,
      ← mul_assoc, show ((-1 : Polynomial R)) ^ m = Polynomial.C ((-1) ^ m) by simp, ← Polynomial.C_mul,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X_pow]
    split_ifs with h
    · subst h; ring
    · simp

/- English proof (translation)
Establish `h : (-M).charpolyRev = M.charpolyRev.comp (-Polynomial.X)`. Rewrite using `[Matrix.charpolyRev, Matrix.charpolyRev, ← Polynomial.coe_compRingHom_apply, RingHom.map_det]`. Use `congr 1`. Use extensionality with `a c : 2`. Apply the tactic sequence `by_cases h : a = c <;> simp [h]`.

Rewrite using `[h, coeff_comp_neg_X']`.
-/
theorem coeff_neg_charpolyRev {R : Type} [CommRing R] {m : ℕ} (M : Matrix (Fin m) (Fin m) R) (b : ℕ) :
    (-M).charpolyRev.coeff b = (-1) ^ b * M.charpolyRev.coeff b := by
  have h : (-M).charpolyRev = M.charpolyRev.comp (-Polynomial.X) := by
    rw [Matrix.charpolyRev, Matrix.charpolyRev, ← Polynomial.coe_compRingHom_apply, RingHom.map_det]
    congr 1
    ext a c : 2
    by_cases h : a = c <;> simp [h]
  rw [h, coeff_comp_neg_X']

/- English proof (translation)
Rewrite using `[Matrix.charpolyRev, Matrix.charpolyRev, ← Polynomial.coe_mapRingHom, RingHom.map_det]`. Use `congr 1`. Use extensionality with `a b : 2`. Apply the tactic sequence `by_cases h : a = b <;> simp [h]`.
-/
theorem charpolyRev_map' {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m : ℕ} (M : Matrix (Fin m) (Fin m) R) :
    M.charpolyRev.map f = (M.map f).charpolyRev := by
  rw [Matrix.charpolyRev, Matrix.charpolyRev, ← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext a b : 2
  by_cases h : a = b <;> simp [h]

/- English proof (translation)
Introduce `E _ _ _ H Dw n ix τ k hk P`. Use `set e : Fin Dw.p × Fin Dw.q → Fin n := fun x => ix.symm (τ, x.1, x.2) with he`. Establish `hL : ∀ j, chernPoly (fun u => modelGram H Dw (coordOf ix u) τ.1) 0 j = (blockPoly e).charpolyRev.coeff j`. Introduce `j`. Establish `h1 : (fun u => modelGram H Dw (coordOf ix u) τ.1) = fun u => Matrix.reindex (finCongr (mult_of_mem Dw τ.2).symm) (finCongr (mult_of_mem Dw τ.2).symm) ((1 - (Matrix.of fun i c => u (e (i, c))).map (starRingEnd ℂ) * (Matrix.of fun i c => u (e (i, c)))ᵀ)⁻¹)`.

Use function extensionality and compare the values at `u`. Simplify using `only [modelGram, dif_pos τ.2]`. Both sides reduce to the same expression. Rewrite using `[h1, chernPoly_reindex, chernPoly, curvPoly_model (fun i c => e (i, c)) (fun i c => e (i, c)), neg_neg]`. Both sides reduce to the same expression.

Establish `hc1 : ¬ conjEmb τ.1 (H.rt : E) = H.rt0` using `GlobalTheory.AllWt.conj_not_mem τ`. Establish `hc2 : conjEmb (conjEmb τ.1) (H.rt : E) = H.rt0` using `by rw [GlobalTheory.AllWt.conjEmb_conjEmb]; exact τ.2`. Establish `hD : ∀ j, chernPoly (fun u => modelGram H Dw (coordOf ix u) (conjEmb τ.1)) 0 j = (blockPolyBar e).charpolyRev.coeff j`. Introduce `j`. Establish `hτ : (⟨conjEmb (conjEmb τ.1), hc2⟩ : GlobalTheory.AllWt.Psi H) = τ` using `Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _)`.

Establish `h1 : (fun u => modelGram H Dw (coordOf ix u) (conjEmb τ.1)) = fun u => Matrix.reindex (finCongr (mult_of_not_mem Dw hc1).symm) (finCongr (mult_of_not_mem Dw hc1).symm) ((1 - (Matrix.of fun b i => u (e (i, b))).map (starRingEnd ℂ) * (Matrix.of fun b i => u (e (i, b)))ᵀ)⁻¹)`. Use function extensionality and compare the values at `u`. Simplify using `only [modelGram, dif_neg hc1, dif_pos hc2, hτ]`. Both sides reduce to the same expression. Rewrite using `[h1, chernPoly_reindex, chernPoly, curvPoly_model (fun b i => e (i, b)) (fun b i => e (i, b)), neg_neg]`.

Both sides reduce to the same expression. Establish `hrel : aeval (fun x : (E →+* ℂ) × ℕ => chernPoly (fun u => modelGram H Dw (coordOf ix u) x.1) 0 x.2) (relPoly τ k) = ((blockPoly e).charpolyRev * (-blockPolyBar e).charpolyRev).coeff k`. Simplify using `only [relPoly, map_sum, map_mul, aeval_X, aeval_C, hL, hD, Polynomial.coeff_mul, coeff_neg_charpolyRev]`. Rewrite using `[Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Simplify using `only [map_pow, map_neg, map_one]`. Expand and normalize the polynomial expressions, which then agree. Establish `hzero : toEven n (((blockPoly e).charpolyRev * (-blockPolyBar e).charpolyRev).coeff k) = 0`. Establish `h2` using `GlobalTheory.T.charpolyRev_mul_eq_one_of_trace_pow_add_eq_zero (K := ℂ) _ _ (GlobalTheory.T.trace_pow_grassmannBlockCurvature_supertrace_zero e)`. Establish `e1 : ((blockPoly e).map (toEven n)).charpolyRev = (blockPoly e).charpolyRev.map (toEven n).toRingHom` using `(charpolyRev_map' _ _).symm`.

Establish `e2 : ((-blockPolyBar e).map (toEven n)).charpolyRev = (-blockPolyBar e).charpolyRev.map (toEven n).toRingHom` using `(charpolyRev_map' _ _).symm`. Rewrite `h2` using `[e1, e2, ← Polynomial.map_mul]`. Establish `h3` using `congrArg (fun f => Polynomial.coeff f k) h2`. Simplify using `only [Polynomial.coeff_map, Polynomial.coeff_one, if_neg (show k ≠ 0 by omega)] at h3`. Conclude with `h3`.

Rewrite using `[chernTop, map_mul, hrel, GlobalTheory.T.topDegreeFormCoeff_eq_tensorSquareTopCoefficient, map_mul, hzero, zero_mul]`. Simplify using the standard rewrite rules.
-/
theorem relation_top_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) {n : ℕ} (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q) (τ : GlobalTheory.AllWt.Psi H) (k : ℕ), 1 ≤ k → ∀ P : MvPolynomial ((E →+* ℂ) × ℕ) ℝ, chernTop (relPoly τ k * P) (fun u => modelGram H Dw (coordOf ix u)) 0 = 0 := by
  intro E _ _ _ H Dw n ix τ k hk P
  set e : Fin Dw.p × Fin Dw.q → Fin n := fun x => ix.symm (τ, x.1, x.2) with he
  have hL : ∀ j, chernPoly (fun u => modelGram H Dw (coordOf ix u) τ.1) 0 j = (blockPoly e).charpolyRev.coeff j := by
    intro j
    have h1 : (fun u => modelGram H Dw (coordOf ix u) τ.1) = fun u =>
        Matrix.reindex (finCongr (mult_of_mem Dw τ.2).symm) (finCongr (mult_of_mem Dw τ.2).symm)
          ((1 - (Matrix.of fun i c => u (e (i, c))).map (starRingEnd ℂ) * (Matrix.of fun i c => u (e (i, c)))ᵀ)⁻¹) := by
      funext u
      simp only [modelGram, dif_pos τ.2]
      rfl
    rw [h1, chernPoly_reindex, chernPoly, curvPoly_model (fun i c => e (i, c)) (fun i c => e (i, c)), neg_neg]
    rfl
  have hc1 : ¬ conjEmb τ.1 (H.rt : E) = H.rt0 := GlobalTheory.AllWt.conj_not_mem τ
  have hc2 : conjEmb (conjEmb τ.1) (H.rt : E) = H.rt0 := by rw [GlobalTheory.AllWt.conjEmb_conjEmb]; exact τ.2
  have hD : ∀ j, chernPoly (fun u => modelGram H Dw (coordOf ix u) (conjEmb τ.1)) 0 j =
      (blockPolyBar e).charpolyRev.coeff j := by
    intro j
    have hτ : (⟨conjEmb (conjEmb τ.1), hc2⟩ : GlobalTheory.AllWt.Psi H) = τ := Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _)
    have h1 : (fun u => modelGram H Dw (coordOf ix u) (conjEmb τ.1)) = fun u =>
        Matrix.reindex (finCongr (mult_of_not_mem Dw hc1).symm) (finCongr (mult_of_not_mem Dw hc1).symm)
          ((1 - (Matrix.of fun b i => u (e (i, b))).map (starRingEnd ℂ) * (Matrix.of fun b i => u (e (i, b)))ᵀ)⁻¹) := by
      funext u
      simp only [modelGram, dif_neg hc1, dif_pos hc2, hτ]
      rfl
    rw [h1, chernPoly_reindex, chernPoly, curvPoly_model (fun b i => e (i, b)) (fun b i => e (i, b)), neg_neg]
    rfl
  have hrel : aeval (fun x : (E →+* ℂ) × ℕ => chernPoly (fun u => modelGram H Dw (coordOf ix u) x.1) 0 x.2) (relPoly τ k) =
      ((blockPoly e).charpolyRev * (-blockPolyBar e).charpolyRev).coeff k := by
    simp only [relPoly, map_sum, map_mul, aeval_X, aeval_C, hL, hD, Polynomial.coeff_mul, coeff_neg_charpolyRev]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [map_pow, map_neg, map_one]
    ring
  have hzero : toEven n (((blockPoly e).charpolyRev * (-blockPolyBar e).charpolyRev).coeff k) = 0 := by
    have h2 := GlobalTheory.T.charpolyRev_mul_eq_one_of_trace_pow_add_eq_zero (K := ℂ) _ _ (GlobalTheory.T.trace_pow_grassmannBlockCurvature_supertrace_zero e)
    have e1 : ((blockPoly e).map (toEven n)).charpolyRev = (blockPoly e).charpolyRev.map (toEven n).toRingHom :=
      (charpolyRev_map' _ _).symm
    have e2 : ((-blockPolyBar e).map (toEven n)).charpolyRev =
        (-blockPolyBar e).charpolyRev.map (toEven n).toRingHom := (charpolyRev_map' _ _).symm
    rw [e1, e2, ← Polynomial.map_mul] at h2
    have h3 := congrArg (fun f => Polynomial.coeff f k) h2
    simp only [Polynomial.coeff_map, Polynomial.coeff_one, if_neg (show k ≠ 0 by omega)] at h3
    exact h3
  rw [chernTop, map_mul, hrel, GlobalTheory.T.topDegreeFormCoeff_eq_tensorSquareTopCoefficient, map_mul, hzero, zero_mul]
  simp

end GlobalTheory.PointChernRel
