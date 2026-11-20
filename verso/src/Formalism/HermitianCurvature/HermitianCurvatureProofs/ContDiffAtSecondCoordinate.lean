import Formalism.HermitianCurvature.HermitianCurvatureProofs.HcoSmulRight

namespace Formalism.FourierDecayAlt.P.PBI.Sm

open Finset Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.Dx2.DF Formalism.FourierDecayAlt.P.PBI
open scoped ComplexConjugate

noncomputable section

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

section generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}

/- English proof (translation)
Simplify `Complex.conjCLE.contDiff.contDiffAt.comp x hf` using `[Function.comp_def]`.
-/
theorem cd_conj {f : E → ℂ} (hf : ContDiffAt ℝ ∞' f x) : ContDiffAt ℝ ∞' (fun y => conj (f y)) x := by
  simpa [Function.comp_def] using Complex.conjCLE.contDiff.contDiffAt.comp x hf

/- English proof (translation)
Simplify `Complex.ofRealCLM.contDiff.contDiffAt.comp x hf` using `[Function.comp_def]`.
-/
theorem cd_ofReal {f : E → ℝ} (hf : ContDiffAt ℝ ∞' f x) : ContDiffAt ℝ ∞' (fun y => ((f y : ℝ) : ℂ)) x := by
  simpa [Function.comp_def] using Complex.ofRealCLM.contDiff.contDiffAt.comp x hf

/- English proof (translation)
The claim follows from `hf.inv h0`.
-/
theorem cd_inv {f : E → ℂ} (hf : ContDiffAt ℝ ∞' f x) (h0 : f x ≠ 0) :
    ContDiffAt ℝ ∞' (fun y => (f y)⁻¹) x := hf.inv h0

/- English proof (translation)
Simplify `hf.mul (cd_inv hg h0)` using `[div_eq_mul_inv]`.
-/
theorem cd_div {f g : E → ℂ} (hf : ContDiffAt ℝ ∞' f x) (hg : ContDiffAt ℝ ∞' g x) (h0 : g x ≠ 0) :
    ContDiffAt ℝ ∞' (fun y => f y / g y) x := by
  simpa [div_eq_mul_inv] using hf.mul (cd_inv hg h0)

/- English proof (translation)
Establish `hre : ContDiffAt ℝ ∞' (fun y => (f y).re) x`. Simplify `Complex.reCLM.contDiff.contDiffAt.comp x hf` using `[Function.comp_def]`. Establish `him : ContDiffAt ℝ ∞' (fun y => (f y).im) x`. Simplify `Complex.imCLM.contDiff.contDiffAt.comp x hf` using `[Function.comp_def]`. Establish `h : (fun y => Complex.normSq (f y)) = fun y => (f y).re * (f y).re + (f y).im * (f y).im`.

Use function extensionality and compare the values at `fun y => Complex.normSq_apply _`. Rewrite using `[h]`. Conclude with `(hre.mul hre).add (him.mul him)`.
-/
theorem cd_normSq {f : E → ℂ} (hf : ContDiffAt ℝ ∞' f x) : ContDiffAt ℝ ∞' (fun y => Complex.normSq (f y)) x := by
  have hre : ContDiffAt ℝ ∞' (fun y => (f y).re) x := by
    simpa [Function.comp_def] using Complex.reCLM.contDiff.contDiffAt.comp x hf
  have him : ContDiffAt ℝ ∞' (fun y => (f y).im) x := by
    simpa [Function.comp_def] using Complex.imCLM.contDiff.contDiffAt.comp x hf
  have h : (fun y => Complex.normSq (f y)) = fun y => (f y).re * (f y).re + (f y).im * (f y).im :=
    funext fun y => Complex.normSq_apply _
  rw [h]
  exact (hre.mul hre).add (him.mul him)

variable {m n : Type*} [Fintype m] [Fintype n]

def MS (f : E → Matrix m n ℂ) (x : E) : Prop := ∀ i j, ContDiffAt ℝ ∞' (fun y => f y i j) x

/- English proof (translation)
Introduce `_ _` and use `contDiffAt_const`.
-/
theorem ms_const (M : Matrix m n ℂ) : MS (fun _ : E => M) x := fun _ _ => contDiffAt_const

/- English proof (translation)
Introduce `i j` and use `by simpa using (hf i j).add (hg i j)`.
-/
theorem ms_add {f g : E → Matrix m n ℂ} (hf : MS f x) (hg : MS g x) : MS (fun y => f y + g y) x := fun i j => by simpa using (hf i j).add (hg i j)

/- English proof (translation)
Introduce `i j` and use `by simpa using (hf i j).sub (hg i j)`.
-/
theorem ms_sub {f g : E → Matrix m n ℂ} (hf : MS f x) (hg : MS g x) : MS (fun y => f y - g y) x := fun i j => by simpa using (hf i j).sub (hg i j)

/- English proof (translation)
Introduce `i j` and use `by simpa using hc.mul (hf i j)`.
-/
theorem ms_smul {c : E → ℂ} {f : E → Matrix m n ℂ} (hc : ContDiffAt ℝ ∞' c x) (hf : MS f x) :
    MS (fun y => c y • f y) x := fun i j => by simpa using hc.mul (hf i j)

/- English proof (translation)
Introduce `i j` and use `by simp only [Matrix.mul_apply] exact ContDiffAt.sum fun l _ => (hf i l).mul (hg l j)`.
-/
theorem ms_mul {l : Type*} [Fintype l] {f : E → Matrix m l ℂ} {g : E → Matrix l n ℂ} (hf : MS f x)
    (hg : MS g x) : MS (fun y => f y * g y) x := fun i j => by
  simp only [Matrix.mul_apply]
  exact ContDiffAt.sum fun l _ => (hf i l).mul (hg l j)

/- English proof (translation)
Introduce `i j` and use `by simpa [Matrix.conjTranspose_apply] using cd_conj (hf j i)`.
-/
theorem ms_conjT {f : E → Matrix m n ℂ} (hf : MS f x) : MS (fun y => (f y)ᴴ) x := fun i j => by simpa [Matrix.conjTranspose_apply] using cd_conj (hf j i)

/- English proof (translation)
Introduce `i j` and use `hf (e1 i) (e2 j)`.
-/
theorem ms_submatrix {m' n' : Type*} [Fintype m'] [Fintype n'] {f : E → Matrix m n ℂ} (hf : MS f x)
    (e1 : m' → m) (e2 : n' → n) : MS (fun y => (f y).submatrix e1 e2) x := fun i j => hf (e1 i) (e2 j)

variable [DecidableEq m]

/- English proof (translation)
Simplify using `only [Matrix.det_apply']`. Use `ContDiffAt.sum fun σ _ => contDiffAt_const.mul ?_` and prove the remaining obligations. Establish `key : ContDiffAt ℝ ∞' (∏ i, fun y => f y (σ i) i) x` using `Finset.prod_induction _ (fun g => ContDiffAt ℝ ∞' g x) (fun a b ha hb => ha.mul hb) contDiffAt_const (fun i _ => hf _ _)`. Rewrite `key` using `[Finset.prod_fn]`. Then use the resulting hypothesis.
-/
theorem cd_det {f : E → Matrix m m ℂ} (hf : MS f x) : ContDiffAt ℝ ∞' (fun y => (f y).det) x := by
  simp only [Matrix.det_apply']
  refine ContDiffAt.sum fun σ _ => contDiffAt_const.mul ?_
  have key : ContDiffAt ℝ ∞' (∏ i, fun y => f y (σ i) i) x :=
    Finset.prod_induction _ (fun g => ContDiffAt ℝ ∞' g x) (fun a b ha hb => ha.mul hb)
      contDiffAt_const (fun i _ => hf _ _)
  rwa [Finset.prod_fn] at key

/- English proof (translation)
Introduce `i k` and use `by by_cases hij : i = j · subst hij simpa [Matrix.updateRow_apply] using (contDiffAt_const : ContDiffAt ℝ ∞' (fun _ : E => v k) x) · simpa [Matrix.updateRow_apply, hij] using hf i k`.
-/
theorem ms_updateRow {f : E → Matrix m m ℂ} (hf : MS f x) (j : m) (v : m → ℂ) :
    MS (fun y => (f y).updateRow j v) x := fun i k => by
  by_cases hij : i = j
  · subst hij
    simpa [Matrix.updateRow_apply] using (contDiffAt_const : ContDiffAt ℝ ∞' (fun _ : E => v k) x)
  · simpa [Matrix.updateRow_apply, hij] using hf i k

/- English proof (translation)
Introduce `i j` and use `by simp only [Matrix.adjugate_apply] exact cd_det (ms_updateRow hf j (Pi.single i 1))`.
-/
theorem ms_adj {f : E → Matrix m m ℂ} (hf : MS f x) : MS (fun y => (f y).adjugate) x := fun i j => by
  simp only [Matrix.adjugate_apply]
  exact cd_det (ms_updateRow hf j (Pi.single i 1))

/- English proof (translation)
Establish `h : (fun y => (f y)⁻¹) = fun y => ((f y).det)⁻¹ • (f y).adjugate`. Use function extensionality and compare the values at `fun y => by rw [Matrix.inv_def, Ring.inverse_eq_inv']`. Rewrite using `[h]`. Conclude with `ms_smul (cd_inv (cd_det hf) h0) (ms_adj hf)`.
-/
theorem ms_inv {f : E → Matrix m m ℂ} (hf : MS f x) (h0 : (f x).det ≠ 0) : MS (fun y => (f y)⁻¹) x := by
  have h : (fun y => (f y)⁻¹) = fun y => ((f y).det)⁻¹ • (f y).adjugate :=
    funext fun y => by rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  exact ms_smul (cd_inv (cd_det hf) h0) (ms_adj hf)

end generic

section specific

variable {r : ℕ} (T T' : ℝ)

/- English proof (translation)
Introduce `i j` and use `(contDiff_apply_apply ℝ ℂ i j).contDiffAt`.
-/
theorem ms_of (Z0 : G.Mat (r + 1)) : MS (fun Z : G.Mat (r + 1) => Matrix.of Z) Z0 := fun i j => (contDiff_apply_apply ℝ ℂ i j).contDiffAt

/- English proof (translation)
Introduce `h`. Establish `h1` using `Complex.normSq_nonneg ((M.submatrix Fin.castSucc Fin.castSucc).det)`. Establish `h2` using `mul_pos hT hT'`. Unfold `gPoly at hU`. Rewrite `hU` using `[h, map_zero]`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem det_ne_of_gPoly (hT : 0 < T) (hT' : 0 < T') {M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ}
    (hU : 0 < gPoly (T * T') M) : M.det ≠ 0 := by
  intro h
  have h1 := Complex.normSq_nonneg ((M.submatrix Fin.castSucc Fin.castSucc).det)
  have h2 := mul_pos hT hT'
  unfold gPoly at hU
  rw [h, map_zero] at hU
  nlinarith

/- English proof (translation)
Unfold `nk`. Assume the negation of the conclusion as `hle`. Use `push_neg at hle`. Establish `hsum : ∑ b, Complex.normSq (kap M b) = 0` using `le_antisymm hle (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _)`. Establish `hz : ∀ b, kap M b = 0` using `fun b => Complex.normSq_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg (kap M i))).mp hsum b (Finset.mem_univ _))`.

Establish `hm` using `congrFun (congrFun (Matrix.mul_adjugate M) (Fin.last r)) (Fin.last r)`. Simplify using `only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at hm`. Establish `h0 : ∑ k, M (Fin.last r) k * M.adjugate k (Fin.last r) = 0` using `Finset.sum_eq_zero fun k _ => by`. Use `hz k` as an intermediate fact. Simplify using `only [kap] at this`.

Rewrite using `[this, mul_zero]`. Conclude with `hdet (hm.symm.trans h0)`.
-/
theorem nk_pos_of_det {M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hdet : M.det ≠ 0) : 0 < nk M := by
  unfold nk
  by_contra hle
  push_neg at hle
  have hsum : ∑ b, Complex.normSq (kap M b) = 0 :=
    le_antisymm hle (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _)
  have hz : ∀ b, kap M b = 0 := fun b =>
    Complex.normSq_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Complex.normSq_nonneg (kap M i))).mp hsum b (Finset.mem_univ _))
  have hm := congrFun (congrFun (Matrix.mul_adjugate M) (Fin.last r)) (Fin.last r)
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at hm
  have h0 : ∑ k, M (Fin.last r) k * M.adjugate k (Fin.last r) = 0 :=
    Finset.sum_eq_zero fun k _ => by
      have := hz k
      simp only [kap] at this
      rw [this, mul_zero]
  exact hdet (hm.symm.trans h0)

variable (Z0 : G.Mat (r + 1)) (hT : 0 < T) (hT' : 0 < T') (hU : 0 < gPoly (T * T') (Matrix.of Z0))
include hT hT' hU

/- English proof (translation)
The claim follows from `cd_det (ms_of Z0)`.
-/
theorem cd_detZ : ContDiffAt ℝ ∞' (fun Z : G.Mat (r + 1) => (Matrix.of Z).det) Z0 := cd_det (ms_of Z0)

/- English proof (translation)
Unfold `kap`. Conclude with `ms_adj (ms_of Z0) b (Fin.last r)`.
-/
theorem cd_kap (b : Fin (r + 1)) : ContDiffAt ℝ ∞' (fun Z : G.Mat (r + 1) => kap (Matrix.of Z) b) Z0 := by
  unfold kap
  exact ms_adj (ms_of Z0) b (Fin.last r)

/- English proof (translation)
Unfold `nk`. Conclude with `ContDiffAt.sum fun b _ => cd_normSq (cd_kap T T' Z0 hT hT' hU b)`.
-/
theorem cd_nk : ContDiffAt ℝ ∞' (fun Z : G.Mat (r + 1) => nk (Matrix.of Z)) Z0 := by
  unfold nk
  exact ContDiffAt.sum fun b _ => cd_normSq (cd_kap T T' Z0 hT hT' hU b)

/- English proof (translation)
Establish `hdet` using `det_ne_of_gPoly T T' hT hT' hU`. Establish `hd` using `cd_detZ T T' Z0 hT hT' hU`. Unfold `ph`. Conclude with `cd_div hd (cd_ofReal (hd.norm ℝ hdet)) (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hdet))`.
-/
theorem cd_ph : ContDiffAt ℝ ∞' (fun Z : G.Mat (r + 1) => ph (Matrix.of Z)) Z0 := by
  have hdet := det_ne_of_gPoly T T' hT hT' hU
  have hd := cd_detZ T T' Z0 hT hT' hU
  unfold ph
  exact cd_div hd (cd_ofReal (hd.norm ℝ hdet))
    (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hdet))

/- English proof (translation)
Unfold `gPoly`. Conclude with `(cd_normSq (cd_detZ T T' Z0 hT hT' hU)).sub (contDiffAt_const.mul (cd_normSq (cd_det (ms_submatrix (ms_of Z0) _ _))))`.
-/
theorem cd_gPoly : ContDiffAt ℝ ∞' (fun Z : G.Mat (r + 1) => gPoly (T * T') (Matrix.of Z)) Z0 := by
  unfold gPoly
  exact (cd_normSq (cd_detZ T T' Z0 hT hT' hU)).sub
    (contDiffAt_const.mul (cd_normSq (cd_det (ms_submatrix (ms_of Z0) _ _))))

/- English proof (translation)
Unfold `sGT`. Conclude with `((cd_gPoly T T' Z0 hT hT' hU).div_const T).sqrt (div_pos hU hT).ne'`.
-/
theorem cd_sGT : ContDiffAt ℝ ∞' (fun Z : G.Mat (r + 1) => sGT T T' (Matrix.of Z)) Z0 := by
  unfold sGT
  exact ((cd_gPoly T T' Z0 hT hT' hU).div_const T).sqrt (div_pos hU hT).ne'

/- English proof (translation)
Unfold `sGT'`. Conclude with `((cd_gPoly T T' Z0 hT hT' hU).div_const T').sqrt (div_pos hU hT').ne'`.
-/
theorem cd_sGT' : ContDiffAt ℝ ∞' (fun Z : G.Mat (r + 1) => sGT' T T' (Matrix.of Z)) Z0 := by
  unfold sGT'
  exact ((cd_gPoly T T' Z0 hT hT' hU).div_const T').sqrt (div_pos hU hT').ne'

/- English proof (translation)
Unfold `al`. Conclude with `(ms_of Z0 (Fin.last r) b).neg.div_const _`.
-/
theorem cd_al (b : Fin (r + 1)) : ContDiffAt ℝ ∞' (fun Z : G.Mat (r + 1) => al T T' (Matrix.of Z) b) Z0 := by
  unfold al
  exact (ms_of Z0 (Fin.last r) b).neg.div_const _

/- English proof (translation)
Establish `hnk : ((nk (Matrix.of Z0) : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.mpr (nk_pos_of_det (det_ne_of_gPoly T T' hT hT' hU)).ne'`. Unfold `be`. Conclude with `((cd_div (cd_conj (cd_kap T T' Z0 hT hT' hU b)) (cd_ofReal (cd_nk T T' Z0 hT hT' hU)) hnk).mul (cd_ofReal (cd_sGT T T' Z0 hT hT' hU))).mul (cd_ph T T' Z0 hT hT' hU)`.
-/
theorem cd_be (b : Fin (r + 1)) : ContDiffAt ℝ ∞' (fun Z : G.Mat (r + 1) => be T T' (Matrix.of Z) b) Z0 := by
  have hnk : ((nk (Matrix.of Z0) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (nk_pos_of_det (det_ne_of_gPoly T T' hT hT' hU)).ne'
  unfold be
  exact ((cd_div (cd_conj (cd_kap T T' Z0 hT hT' hU b)) (cd_ofReal (cd_nk T T' Z0 hT hT' hU)) hnk).mul
    (cd_ofReal (cd_sGT T T' Z0 hT hT' hU))).mul (cd_ph T T' Z0 hT hT' hU)

/- English proof (translation)
Unfold `Heta`. Conclude with `((contDiffAt_const.mul (cd_al T T' Z0 hT hT' hU b)).mul (cd_conj (cd_al T T' Z0 hT hT' hU c))).add ((cd_be T T' Z0 hT hT' hU b).mul (cd_conj (cd_be T T' Z0 hT hT' hU c)))`.
-/
theorem cd_Heta (b c : Fin (r + 1)) :
    ContDiffAt ℝ ∞' (fun Z : G.Mat (r + 1) => Heta T T' (Matrix.of Z) b c) Z0 := by
  unfold Heta
  exact ((contDiffAt_const.mul (cd_al T T' Z0 hT hT' hU b)).mul (cd_conj (cd_al T T' Z0 hT hT' hU c))).add
    ((cd_be T T' Z0 hT hT' hU b).mul (cd_conj (cd_be T T' Z0 hT hT' hU c)))

/- English proof (translation)
Introduce `i j` and use `by simp only [Rm, Matrix.of_apply] exact contDiffAt_const.sub (cd_Heta T T' Z0 hT hT' hU j i)`.
-/
theorem ms_Rm : MS (fun Z : G.Mat (r + 1) => Rm T T' (Matrix.of Z)) Z0 := fun i j => by
  simp only [Rm, Matrix.of_apply]
  exact contDiffAt_const.sub (cd_Heta T T' Z0 hT hT' hU j i)

/- English proof (translation)
Introduce `i j` and use `by have hnk : ((nk (Matrix.of Z0) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (nk_pos_of_det (det_ne_of_gPoly T T' hT hT' hU)).ne' simp only [Qm, Matrix.of_apply] exact cd_div ((cd_kap T T' Z0 hT hT' hU i).mul (cd_conj (cd_kap T T' Z0 hT hT' hU j))) (cd_ofReal (cd_nk T T' Z0 hT h …`.
-/
theorem ms_Qm : MS (fun Z : G.Mat (r + 1) => Qm (Matrix.of Z)) Z0 := fun i j => by
  have hnk : ((nk (Matrix.of Z0) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (nk_pos_of_det (det_ne_of_gPoly T T' hT hT' hU)).ne'
  simp only [Qm, Matrix.of_apply]
  exact cd_div ((cd_kap T T' Z0 hT hT' hU i).mul (cd_conj (cd_kap T T' Z0 hT hT' hU j)))
    (cd_ofReal (cd_nk T T' Z0 hT hT' hU)) hnk

/- English proof (translation)
Unfold `Pm`. Conclude with `ms_sub (ms_const 1) (ms_Qm T T' Z0 hT hT' hU)`.
-/
theorem ms_Pm : MS (fun Z : G.Mat (r + 1) => Pm (Matrix.of Z)) Z0 := by
  unfold Pm
  exact ms_sub (ms_const 1) (ms_Qm T T' Z0 hT hT' hU)

/- English proof (translation)
Establish `hP` using `ms_Pm T T' Z0 hT hT' hU`. Establish `hR` using `ms_Rm T T' Z0 hT hT' hU`. Establish `hQ` using `ms_Qm T T' Z0 hT hT' hU`. Unfold `Km`. Conclude with `ms_add (ms_smul contDiffAt_const (ms_mul (ms_mul hP hR) hP)) (ms_mul (ms_mul hP hR) hQ)`.
-/
theorem ms_Km : MS (fun Z : G.Mat (r + 1) => Km T T' (Matrix.of Z)) Z0 := by
  have hP := ms_Pm T T' Z0 hT hT' hU
  have hR := ms_Rm T T' Z0 hT hT' hU
  have hQ := ms_Qm T T' Z0 hT hT' hU
  unfold Km
  exact ms_add (ms_smul contDiffAt_const (ms_mul (ms_mul hP hR) hP)) (ms_mul (ms_mul hP hR) hQ)

/- English proof (translation)
The claim follows from `ms_conjT (ms_inv (ms_of Z0) (det_ne_of_gPoly T T' hT hT' hU))`.
-/
theorem ms_iH : MS (fun Z : G.Mat (r + 1) => ((Matrix.of Z)⁻¹)ᴴ) Z0 := ms_conjT (ms_inv (ms_of Z0) (det_ne_of_gPoly T T' hT hT' hU))

/- English proof (translation)
Unfold `Mf`. Conclude with `ms_mul (ms_iH T T' Z0 hT hT' hU) (ms_Km T T' Z0 hT hT' hU)`.
-/
theorem ms_Mf : MS (fun Z : G.Mat (r + 1) => Mf T T' (Matrix.of Z)) Z0 := by
  unfold Mf
  exact ms_mul (ms_iH T T' Z0 hT hT' hU) (ms_Km T T' Z0 hT hT' hU)

end specific

section co

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E} {r : ℕ}

/- English proof (translation)
The claim follows from `(contDiffAt_pi.mpr h1).prodMk ((contDiffAt_pi.mpr h2).prodMk (h3.prodMk h4))`.
-/
theorem cd_co {c : E → Co r} (h1 : ∀ a, ContDiffAt ℝ ∞' (fun y => (c y).1 a) x)
    (h2 : ∀ a, ContDiffAt ℝ ∞' (fun y => (c y).2.1 a) x) (h3 : ContDiffAt ℝ ∞' (fun y => (c y).2.2.1) x)
    (h4 : ContDiffAt ℝ ∞' (fun y => (c y).2.2.2) x) : ContDiffAt ℝ ∞' c x := (contDiffAt_pi.mpr h1).prodMk ((contDiffAt_pi.mpr h2).prodMk (h3.prodMk h4))

/- English proof (translation)
The claim follows from `contDiffAt_pi.mp hc.fst a`.
-/
theorem contDiffAt_first_coordinate {c : E → Co r} (hc : ContDiffAt ℝ ∞' c x) (a : Fin r) :
    ContDiffAt ℝ ∞' (fun y => (c y).1 a) x := contDiffAt_pi.mp hc.fst a

/- English proof (translation)
The claim follows from `contDiffAt_pi.mp hc.snd.fst a`.
-/
theorem contDiffAt_second_coordinate {c : E → Co r} (hc : ContDiffAt ℝ ∞' c x) (a : Fin r) :
    ContDiffAt ℝ ∞' (fun y => (c y).2.1 a) x := contDiffAt_pi.mp hc.snd.fst a

/- English proof (translation)
The claim follows from `hc.snd.snd.fst`.
-/
theorem contDiffAt_third_coordinate {c : E → Co r} (hc : ContDiffAt ℝ ∞' c x) : ContDiffAt ℝ ∞' (fun y => (c y).2.2.1) x := hc.snd.snd.fst

/- English proof (translation)
The claim follows from `hc.snd.snd.snd`.
-/
theorem contDiffAt_fourth_coordinate {c : E → Co r} (hc : ContDiffAt ℝ ∞' c x) : ContDiffAt ℝ ∞' (fun y => (c y).2.2.2) x := hc.snd.snd.snd

/- English proof (translation)
Unfold `hco`. Conclude with `(((ContDiffAt.sum fun a _ => (contDiffAt_first_coordinate hc a).mul (cd_conj (contDiffAt_second_coordinate hd a))).add (ContDiffAt.sum fun a _ => (contDiffAt_second_coordinate hc a).mul (cd_conj (contDiffAt_first_coordinate hd a)))).sub ((contDiffAt_const.mul (contDiffAt_third_co …`.
-/
theorem cd_hco (T' : ℝ) {c d : E → Co r} (hc : ContDiffAt ℝ ∞' c x) (hd : ContDiffAt ℝ ∞' d x) :
    ContDiffAt ℝ ∞' (fun y => hco T' (c y) (d y)) x := by
  unfold hco
  exact (((ContDiffAt.sum fun a _ => (contDiffAt_first_coordinate hc a).mul (cd_conj (contDiffAt_second_coordinate hd a))).add
    (ContDiffAt.sum fun a _ => (contDiffAt_second_coordinate hc a).mul (cd_conj (contDiffAt_first_coordinate hd a)))).sub
    ((contDiffAt_const.mul (contDiffAt_third_coordinate hc)).mul (cd_conj (contDiffAt_third_coordinate hd)))).add
    ((contDiffAt_fourth_coordinate hc).mul (cd_conj (contDiffAt_fourth_coordinate hd)))

/- English proof (translation)
Establish `h : ContDiff ℝ ∞' (fun p : ℂ × F => p.1 • p.2)` using `(contDiff_smul (𝕜 := ℂ) (F := F)).restrict_scalars ℝ`. Conclude with `h.contDiffAt.comp x (hc.prodMk hv)`.
-/
private theorem contDiffAt_smul_of_contDiffAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {c : E → ℂ}
    {v : E → F} (hc : ContDiffAt ℝ ∞' c x) (hv : ContDiffAt ℝ ∞' v x) :
    ContDiffAt ℝ ∞' (fun y => c y • v y) x := by
  have h : ContDiff ℝ ∞' (fun p : ℂ × F => p.1 • p.2) :=
    (contDiff_smul (𝕜 := ℂ) (F := F)).restrict_scalars ℝ
  exact h.contDiffAt.comp x (hc.prodMk hv)

/- English proof (translation)
Unfold `cvec`. Simplify using `only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Conclude with `(((ContDiffAt.sum fun a _ => (contDiffAt_first_coordinate hc a).mul contDiffAt_const).add (ContDiffAt.sum fun a _ => (contDiffAt_second_coordinate hc a).mul contDiffAt_const)).add ((contDiffAt_third_coordinate hc).mul contDiffAt_const)).add ((contDiffAt_fourth_coordinate hc).mul …`.
-/
theorem cd_cvec {k : ℕ} (z' ν' : Fin (2 * r + k + 1) → ℂ) {c : E → Co r} (hc : ContDiffAt ℝ ∞' c x)
    (l : Fin (2 * r + k + 1)) : ContDiffAt ℝ ∞' (fun y => cvec k z' ν' (c y) l) x := by
  unfold cvec
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact (((ContDiffAt.sum fun a _ => (contDiffAt_first_coordinate hc a).mul contDiffAt_const).add
    (ContDiffAt.sum fun a _ => (contDiffAt_second_coordinate hc a).mul contDiffAt_const)).add
    ((contDiffAt_third_coordinate hc).mul contDiffAt_const)).add ((contDiffAt_fourth_coordinate hc).mul contDiffAt_const)

end co

section coSpecific

variable {r : ℕ} (T T' : ℝ) (Z0 : G.Mat (r + 1)) (hT : 0 < T) (hT' : 0 < T')
  (hU : 0 < gPoly (T * T') (Matrix.of Z0))
include hT hT' hU

/- English proof (translation)
Use `cd_co (fun a => ?_) (fun a => ?_) ?_ ?_` and prove the remaining obligations. Conclude with `ms_Mf T T' Z0 hT hT' hU a.castSucc b`. Conclude with `ms_of Z0 a.castSucc b`. Conclude with `cd_al T T' Z0 hT hT' hU b`. Conclude with `cd_be T T' Z0 hT hT' hU b`.
-/
theorem cd_xco (b : Fin (r + 1)) : ContDiffAt ℝ ∞' (fun Z : G.Mat (r + 1) => xco T T' (Matrix.of Z) b) Z0 := by
  refine cd_co (fun a => ?_) (fun a => ?_) ?_ ?_
  · exact ms_Mf T T' Z0 hT hT' hU a.castSucc b
  · exact ms_of Z0 a.castSucc b
  · exact cd_al T T' Z0 hT hT' hU b
  · exact cd_be T T' Z0 hT hT' hU b

/- English proof (translation)
Unfold `y0`. Conclude with `ContDiffAt.sum fun a _ => contDiffAt_smul_of_contDiffAt (ms_iH T T' Z0 hT hT' hU a b.castSucc) contDiffAt_const`.
-/
theorem contDiffAt_dual_coordinates (b : Fin r) : ContDiffAt ℝ ∞' (fun Z : G.Mat (r + 1) => y0 T T' (Matrix.of Z) b) Z0 := by
  unfold y0
  exact ContDiffAt.sum fun a _ => contDiffAt_smul_of_contDiffAt (ms_iH T T' Z0 hT hT' hU a b.castSucc) contDiffAt_const

/- English proof (translation)
Unfold `ysco`. Conclude with `(contDiffAt_dual_coordinates T T' Z0 hT hT' hU b).sub (contDiffAt_smul_of_contDiffAt contDiffAt_const (ContDiffAt.sum fun c _ => contDiffAt_smul_of_contDiffAt (cd_hco T' (contDiffAt_dual_coordinates T T' Z0 hT hT' hU b) (contDiffAt_dual_coordinates T T' Z0 hT hT' hU c)) (cd_xco T …`.
-/
theorem cd_ysco (b : Fin r) : ContDiffAt ℝ ∞' (fun Z : G.Mat (r + 1) => ysco T T' (Matrix.of Z) b) Z0 := by
  unfold ysco
  exact (contDiffAt_dual_coordinates T T' Z0 hT hT' hU b).sub (contDiffAt_smul_of_contDiffAt contDiffAt_const (ContDiffAt.sum fun c _ =>
    contDiffAt_smul_of_contDiffAt (cd_hco T' (contDiffAt_dual_coordinates T T' Z0 hT hT' hU b) (contDiffAt_dual_coordinates T T' Z0 hT hT' hU c))
      (cd_xco T T' Z0 hT hT' hU c.castSucc)))

/- English proof (translation)
Unfold `cofco`. Conclude with `ContDiffAt.sum fun a _ => contDiffAt_smul_of_contDiffAt (cd_conj (ms_adj (ms_of Z0) (Fin.last r) a)) contDiffAt_const`.
-/
theorem cd_cofco : ContDiffAt ℝ ∞' (fun Z : G.Mat (r + 1) => cofco T T' (Matrix.of Z)) Z0 := by
  unfold cofco
  exact ContDiffAt.sum fun a _ =>
    contDiffAt_smul_of_contDiffAt (cd_conj (ms_adj (ms_of Z0) (Fin.last r) a)) contDiffAt_const

/- English proof (translation)
Establish `hc` using `cd_cofco T T' Z0 hT hT' hU`. Establish `hx` using `cd_xco T T' Z0 hT hT' hU`. Establish `hy` using `cd_ysco T T' Z0 hT hT' hU`. Unfold `pco`. Conclude with `((hc.sub (ContDiffAt.sum fun c _ => contDiffAt_smul_of_contDiffAt (cd_hco T' hc (hy c)) (hx c.castSucc))).sub (ContDiffAt.sum fun b _ => contDiffAt_smul_of_contDiffAt (cd_hco T' hc (hx b.castSucc)) (hy b))).add (contDiffAt_smul_of_contDiffAt ((cd_hco T' hc (hx (Fin.last r))).div_ …`.
-/
theorem cd_pco : ContDiffAt ℝ ∞' (fun Z : G.Mat (r + 1) => pco T T' (Matrix.of Z)) Z0 := by
  have hc := cd_cofco T T' Z0 hT hT' hU
  have hx := cd_xco T T' Z0 hT hT' hU
  have hy := cd_ysco T T' Z0 hT hT' hU
  unfold pco
  exact ((hc.sub (ContDiffAt.sum fun c _ => contDiffAt_smul_of_contDiffAt (cd_hco T' hc (hy c)) (hx c.castSucc))).sub
    (ContDiffAt.sum fun b _ => contDiffAt_smul_of_contDiffAt (cd_hco T' hc (hx b.castSucc)) (hy b))).add
    (contDiffAt_smul_of_contDiffAt ((cd_hco T' hc (hx (Fin.last r))).div_const _) (hx (Fin.last r)))

/- English proof (translation)
Establish `hs : ((sGT' T T' (Matrix.of Z0) : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (div_pos hU hT')).ne'`. Unfold `nco`. Conclude with `contDiffAt_smul_of_contDiffAt (cd_div (cd_ph T T' Z0 hT hT' hU) (cd_ofReal (cd_sGT' T T' Z0 hT hT' hU)) hs) (cd_pco T T' Z0 hT hT' hU)`.
-/
theorem cd_nco : ContDiffAt ℝ ∞' (fun Z : G.Mat (r + 1) => nco T T' (Matrix.of Z)) Z0 := by
  have hs : ((sGT' T T' (Matrix.of Z0) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (div_pos hU hT')).ne'
  unfold nco
  exact contDiffAt_smul_of_contDiffAt (cd_div (cd_ph T T' Z0 hT hT' hU) (cd_ofReal (cd_sGT' T T' Z0 hT hT' hU)) hs)
    (cd_pco T T' Z0 hT hT' hU)

/- English proof (translation)
Break down `i with (b | b) | j` into its components or cases. Simplify using `only [Yv]`. Conclude with `cd_cvec z' ν' (cd_xco T T' Z0 hT hT' hU b.castSucc) l`. Simplify using `only [Yv]`. Conclude with `cd_cvec z' ν' (cd_ysco T T' Z0 hT hT' hU b) l`.

Use `fin_cases j`. Simplify using `only [Yv]`. Conclude with `cd_cvec z' ν' (cd_xco T T' Z0 hT hT' hU (Fin.last r)) l`. Simplify using `only [Yv]`. Conclude with `cd_cvec z' ν' (cd_nco T T' Z0 hT hT' hU) l`.
-/
theorem cd_Yv {k : ℕ} (z' ν' : Fin (2 * r + k + 1) → ℂ) (i : (Fin r ⊕ Fin r) ⊕ Fin 2)
    (l : Fin (2 * r + k + 1)) :
    ContDiffAt ℝ ∞' (fun Z : G.Mat (r + 1) => Yv z' ν' T T' (Matrix.of Z) i l) Z0 := by
  rcases i with (b | b) | j
  · simp only [Yv]
    exact cd_cvec z' ν' (cd_xco T T' Z0 hT hT' hU b.castSucc) l
  · simp only [Yv]
    exact cd_cvec z' ν' (cd_ysco T T' Z0 hT hT' hU b) l
  · fin_cases j
    · simp only [Yv]
      exact cd_cvec z' ν' (cd_xco T T' Z0 hT hT' hU (Fin.last r)) l
    · simp only [Yv]
      exact cd_cvec z' ν' (cd_nco T T' Z0 hT hT' hU) l

/- English proof (translation)
Unfold `secM`. Simplify using `only [Formalism.FourierDecayAlt.P.Dx2.DF.smat, Formalism.FourierDecayAlt.P.Dx2.DF.smap]`. Use `ms_mul (ms_const m₀) fun a b => ?_` and prove the remaining obligations. Simplify using `only [Matrix.of_apply, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]`. Conclude with `contDiffAt_const.add (ContDiffAt.sum fun i _ => contDiffAt_const.mul ((cd_Yv T T' Z0 hT hT' hU z' ν' i a).sub contDiffAt_const))`.
-/
theorem ms_secM {k : ℕ} (z' ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) :
    MS (fun Z : G.Mat (r + 1) => secM z' ν' m₀ T T' (Matrix.of Z)) Z0 := by
  unfold secM
  simp only [Formalism.FourierDecayAlt.P.Dx2.DF.smat, Formalism.FourierDecayAlt.P.Dx2.DF.smap]
  refine ms_mul (ms_const m₀) fun a b => ?_
  simp only [Matrix.of_apply, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  exact contDiffAt_const.add (ContDiffAt.sum fun i _ =>
    contDiffAt_const.mul ((cd_Yv T T' Z0 hT hT' hU z' ν' i a).sub contDiffAt_const))

end coSpecific

end

end Formalism.FourierDecayAlt.P.PBI.Sm

namespace Formalism.FourierDecayAlt.P.PBI

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBI.Sm

/- English proof (translation)
Introduce `Z hZ`. Establish `hU : 0 < gPoly (T * T') (Matrix.of Z)` using `hZ`. Apply `ContDiffAt.contDiffWithinAt` to reduce the goal to its premises. Establish `h` using `Sm.ms_secM T T' Z hT hT' hU z' ν' m₀`. Rewrite using `[contDiffAt_pi]`.

Introduce `i`. Rewrite using `[contDiffAt_pi]`. Introduce `j`. Conclude with `h i j`.
-/
theorem secM_contDiffOn {k r : ℕ} (z' ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (T T' : ℝ)
    (hT : 0 < T) (hT' : 0 < T') :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun Z : G.Mat (r + 1) => (Matrix.of.symm (secM z' ν' m₀ T T' (Matrix.of Z)) : Mt k r))
      {Z | 0 < gPoly (T * T') (Matrix.of Z)} := by
  intro Z hZ
  have hU : 0 < gPoly (T * T') (Matrix.of Z) := hZ
  apply ContDiffAt.contDiffWithinAt
  have h := Sm.ms_secM T T' Z hT hT' hU z' ν' m₀
  rw [contDiffAt_pi]
  intro i
  rw [contDiffAt_pi]
  intro j
  exact h i j

end Formalism.FourierDecayAlt.P.PBI
