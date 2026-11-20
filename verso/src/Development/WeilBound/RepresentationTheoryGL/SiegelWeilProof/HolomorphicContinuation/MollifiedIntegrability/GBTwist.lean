import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Lagr

noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.WR.K.GB

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR

namespace TW

variable {n : ℕ}

/- English proof (translation)
Unfold `dirC`. Rewrite using `[fderiv_fun_mul hf hg]`. Simplify using `only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dirC_mul {f g : E n → ℂ} {y : E n} (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y)
    (w : Fin n → Fin n → ℂ) : dirC (fun x => f x * g x) w y = f y * dirC g w y + g y * dirC f w y := by
  unfold dirC
  rw [fderiv_fun_mul hf hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Unfold `dirC`. Rewrite using `[(hf.hasFDerivAt.const_mul a).fderiv]`. Simplify using `only [ContinuousLinearMap.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dirC_const_mul {f : E n → ℂ} {y : E n} (hf : DifferentiableAt ℝ f y) (a : ℂ)
    (w : Fin n → Fin n → ℂ) : dirC (fun x => a * f x) w y = a * dirC f w y := by
  unfold dirC
  rw [(hf.hasFDerivAt.const_mul a).fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Unfold `dirC`. Rewrite using `[(HasFDerivAt.fun_sum (fun i hi => (h i hi).hasFDerivAt)).fderiv]`. Simplify using `only [ContinuousLinearMap.sum_apply]`. Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`.
-/
theorem dirC_sum {ι : Type*} (s : Finset ι) {A : ι → E n → ℂ} {y : E n}
    (h : ∀ i ∈ s, DifferentiableAt ℝ (A i) y) (w : Fin n → Fin n → ℂ) :
    dirC (fun x => ∑ i ∈ s, A i x) w y = ∑ i ∈ s, dirC (A i) w y := by
  unfold dirC
  rw [(HasFDerivAt.fun_sum (fun i hi => (h i hi).hasFDerivAt)).fderiv]
  simp only [ContinuousLinearMap.sum_apply]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]

/- English proof (translation)
Unfold `dirC`. Rewrite using `[hg.hasFDerivAt.cexp.fderiv]`. Simplify using `only [ContinuousLinearMap.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dirC_exp {g : E n → ℂ} {y : E n} (hg : DifferentiableAt ℝ g y) (w : Fin n → Fin n → ℂ) :
    dirC (fun x => Complex.exp (g x)) w y = Complex.exp (g y) * dirC g w y := by
  unfold dirC
  rw [hg.hasFDerivAt.cexp.fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Simplify using `[dirC]`.
-/
theorem dirC_zero (w : Fin n → Fin n → ℂ) (y : E n) : dirC (0 : E n → ℂ) w y = 0 := by
  simp [dirC]

/- English proof (translation)
The claim follows from `(contDiff_infty_iff_fderiv.1 hf).1 y`.
-/
theorem diff_of {f : E n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (y : E n) : DifferentiableAt ℝ f y :=
  (contDiff_infty_iff_fderiv.1 hf).1 y

/- English proof (translation)
Establish `h1` using `(contDiff_infty_iff_fderiv.1 hf).2`. Unfold `dirC`. Conclude with `(h1.clm_apply contDiff_const).add (contDiff_const.mul (h1.clm_apply contDiff_const))`.
-/
theorem contDiff_dirC {f : E n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (w : Fin n → Fin n → ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => dirC f w y) := by
  have h1 := (contDiff_infty_iff_fderiv.1 hf).2
  unfold dirC
  exact (h1.clm_apply contDiff_const).add (contDiff_const.mul (h1.clm_apply contDiff_const))

/- English proof (translation)
The claim follows from `contDiff_dirC hf _`.
-/
theorem contDiff_Dkl {f : E n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k l : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (Dkl k l f) := contDiff_dirC hf _

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [conjTranspose_apply, herm]`. Apply the tactic sequence `apply Complex.ext <;> simp <;> ring`.
-/
theorem herm_isHermitian (y : E n) : (herm y).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, herm]
  apply Complex.ext <;> simp <;> ring

/- English proof (translation)
Establish `hH` using `herm_isHermitian y`. Establish `h1 : (1 + herm y * herm y).PosDef`. Use `(Matrix.PosDef.one (n := Fin n) (R := ℂ)).add_posSemidef (posSemidef_conjTranspose_mul_self (herm y))` as an intermediate fact. Rewrite `this` using `[hH.eq]`. Then use the resulting hypothesis. Conclude with `(Complex.pos_iff.1 h1.det_pos).1`.
-/
theorem dP_pos (y : E n) : 0 < dP y := by
  have hH := herm_isHermitian y
  have h1 : (1 + herm y * herm y).PosDef := by
    have := (Matrix.PosDef.one (n := Fin n) (R := ℂ)).add_posSemidef
      (posSemidef_conjTranspose_mul_self (herm y))
    rwa [hH.eq] at this
  exact (Complex.pos_iff.1 h1.det_pos).1

/- English proof (translation)
The claim follows from `(contDiff_apply ℝ ℝ b).comp (contDiff_apply ℝ (Fin n → ℝ) a)`.
-/
theorem contDiff_coord (a b : Fin n) : ContDiff ℝ (⊤ : ℕ∞) (fun y : E n => y a b) :=
  (contDiff_apply ℝ ℝ b).comp (contDiff_apply ℝ (Fin n → ℝ) a)

/- English proof (translation)
Establish `h1 : ContDiff ℝ (⊤ : ℕ∞) (fun y : E n => ((y i j + y j i : ℝ) : ℂ))` using `Complex.ofRealCLM.contDiff.comp ((contDiff_coord i j).add (contDiff_coord j i))`. Establish `h2 : ContDiff ℝ (⊤ : ℕ∞) (fun y : E n => ((y i j - y j i : ℝ) : ℂ))` using `Complex.ofRealCLM.contDiff.comp ((contDiff_coord i j).sub (contDiff_coord j i))`. Simplify using `only [herm]`. Conclude with `(h1.div_const 2).add ((contDiff_const.mul h2).div_const 2)`.
-/
theorem contDiff_herm_entry (i j : Fin n) : ContDiff ℝ (⊤ : ℕ∞) (fun y : E n => herm y i j) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun y : E n => ((y i j + y j i : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_coord i j).add (contDiff_coord j i))
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun y : E n => ((y i j - y j i : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_coord i j).sub (contDiff_coord j i))
  simp only [herm]
  exact (h1.div_const 2).add ((contDiff_const.mul h2).div_const 2)

/- English proof (translation)
Establish `hM : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun y : E n => (1 + herm y * herm y) i j)`. Introduce `i j`. Simplify using `only [Matrix.add_apply, Matrix.mul_apply]`. Apply the tactic sequence `exact contDiff_const.add (ContDiff.sum fun k _ => (contDiff_herm_entry i k).mul (contDiff_herm_entry k j))`. Simplify using `only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]`.

Conclude with `ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hM (σ i) i)`.
-/
theorem contDiff_dPc : ContDiff ℝ (⊤ : ℕ∞) (fun y : E n => (1 + herm y * herm y).det) := by
  have hM : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun y : E n => (1 + herm y * herm y) i j) := by
    intro i j
    simp only [Matrix.add_apply, Matrix.mul_apply]
    exact contDiff_const.add (ContDiff.sum fun k _ => (contDiff_herm_entry i k).mul (contDiff_herm_entry k j))
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hM (σ i) i)

/- English proof (translation)
Unfold `dP`. Conclude with `Complex.reCLM.contDiff.comp contDiff_dPc`.
-/
theorem contDiff_dP : ContDiff ℝ (⊤ : ℕ∞) (fun y : E n => dP y) := by
  unfold dP
  exact Complex.reCLM.contDiff.comp contDiff_dPc

def Lc (y : E n) : ℂ := ((Real.log (dP y) : ℝ) : ℂ)

/- English proof (translation)
The claim follows from `Complex.ofRealCLM.contDiff.comp (contDiff_dP.log fun y => (dP_pos y).ne')`.
-/
theorem contDiff_Lc : ContDiff ℝ (⊤ : ℕ∞) (Lc (n := n)) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_dP.log fun y => (dP_pos y).ne')

def W (z : ℂ) (y : E n) : ℂ := Complex.exp (-z * Lc y)

/- English proof (translation)
The claim follows from `(contDiff_const.mul contDiff_Lc).cexp`.
-/
theorem contDiff_W_apply (z : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (W (n := n) z) :=
  (contDiff_const.mul contDiff_Lc).cexp

/- English proof (translation)
Establish `hp` using `dP_pos y`. Rewrite using `[Complex.cpow_def_of_ne_zero (by exact_mod_cast hp.ne'), ← Complex.ofReal_log hp.le]`. Unfold `W Lc`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cpow_eq (z : ℂ) (y : E n) : ((dP y : ℝ) : ℂ) ^ (-z) = W z y := by
  have hp := dP_pos y
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hp.ne'), ← Complex.ofReal_log hp.le]
  unfold W Lc
  congr 1
  ring

def om (k l : Fin n) : E n → ℂ := Dkl k l Lc

/- English proof (translation)
The claim follows from `contDiff_Dkl contDiff_Lc k l`.
-/
theorem contDiff_om (k l : Fin n) : ContDiff ℝ (⊤ : ℕ∞) (om k l) := contDiff_Dkl contDiff_Lc k l

def sh (c : ℕ → E n → ℂ) : ℕ → E n → ℂ
  | 0 => fun _ => 0
  | j + 1 => c j

def TD (k l : Fin n) (c : ℕ → E n → ℂ) : ℕ → E n → ℂ :=
  fun j y => Dkl k l (c j) y - om k l y * sh c j y

/- English proof (translation)
Consider the cases of `j with`. Consider the case `zero => exact contDiff_const`. Consider the case `succ j => exact hc j`.
-/
theorem contDiff_sh {c : ℕ → E n → ℂ} (hc : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (c j)) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (sh c j) := by
  cases j with
  | zero => exact contDiff_const
  | succ j => exact hc j

/- English proof (translation)
The claim follows from `(contDiff_Dkl (hc j) k l).sub ((contDiff_om k l).mul (contDiff_sh hc j))`.
-/
theorem TD_smooth {c : ℕ → E n → ℂ} (hc : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (c j)) (k l : Fin n) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (TD k l c j) :=
  (contDiff_Dkl (hc j) k l).sub ((contDiff_om k l).mul (contDiff_sh hc j))

/- English proof (translation)
Introduce `j hj`. Use function extensionality and compare the values at `y`. Take `⟨i, rfl⟩ : ∃ i, j = i + 1` from `⟨j - 1, by omega⟩`. Establish `h1 : c (i + 1) = 0` using `hM _ (by omega)`. Establish `h2 : c i = 0` using `hM _ (by omega)`.

Simplify using `only [TD, sh, h1, h2, Dkl, dirC_zero, Pi.zero_apply, mul_zero, sub_zero]`.
-/
theorem TD_supp {c : ℕ → E n → ℂ} {M : ℕ} (hM : ∀ j, M ≤ j → c j = 0) (k l : Fin n) :
    ∀ j, M + 1 ≤ j → TD k l c j = 0 := by
  intro j hj
  funext y
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have h1 : c (i + 1) = 0 := hM _ (by omega)
  have h2 : c i = 0 := hM _ (by omega)
  simp only [TD, sh, h1, h2, Dkl, dirC_zero, Pi.zero_apply, mul_zero, sub_zero]

/- English proof (translation)
Use function extensionality and compare the values at `y`. Establish `hd : ∀ j, DifferentiableAt ℝ (c j) y` using `fun j => diff_of (hc j) y`. Establish `hdz : ∀ j, DifferentiableAt ℝ (fun x => z ^ j * c j x) y` using `fun j => (hd j).const_mul _`. Establish `hS : DifferentiableAt ℝ (fun x => ∑ j ∈ Finset.range M, z ^ j * c j x) y` using `DifferentiableAt.fun_sum fun j _ => hdz j`. Establish `hL : DifferentiableAt ℝ (Lc (n` using `n)) y := diff_of contDiff_Lc y`.

Establish `hW : dirC (W z) (vkl k l) y = W z y * (-z * om k l y)`. Unfold `W`. Rewrite using `[dirC_exp (hL.const_mul _), dirC_const_mul hL]`. Both sides reduce to the same expression. Establish `hcM : dirC (c M) (vkl k l) y = 0` using `by rw [hM M le_rfl]; exact dirC_zero _ _`.

Unfold `Dkl`. Rewrite using `[dirC_mul (diff_of (contDiff_W_apply z) y) hS, dirC_sum _ (fun j _ => hdz j), hW]`. Simplify using `only [TD, mul_sub, Finset.sum_sub_distrib]`. Rewrite using `[Finset.sum_range_succ, Finset.sum_range_succ']`. Simplify using `only [sh, mul_zero, Dkl, hcM, add_zero, pow_zero, one_mul]`.

Establish `e1 : ∀ j ∈ Finset.range M, dirC (fun x => z ^ j * c j x) (vkl k l) y = z ^ j * dirC (c j) (vkl k l) y` using `fun j _ => dirC_const_mul (hd j) _ _`. Rewrite using `[Finset.sum_congr rfl e1]`. Establish `key : ∑ j ∈ Finset.range M, z ^ (j + 1) * (om k l y * c j y) = z * om k l y * ∑ j ∈ Finset.range M, z ^ j * c j y`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`.

Rewrite using `[key]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem step (z : ℂ) (k l : Fin n) (c : ℕ → E n → ℂ) (M : ℕ) (hc : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (c j))
    (hM : ∀ j, M ≤ j → c j = 0) :
    Dkl k l (fun y => W z y * ∑ j ∈ Finset.range M, z ^ j * c j y) =
      fun y => W z y * ∑ j ∈ Finset.range (M + 1), z ^ j * TD k l c j y := by
  funext y
  have hd : ∀ j, DifferentiableAt ℝ (c j) y := fun j => diff_of (hc j) y
  have hdz : ∀ j, DifferentiableAt ℝ (fun x => z ^ j * c j x) y := fun j => (hd j).const_mul _
  have hS : DifferentiableAt ℝ (fun x => ∑ j ∈ Finset.range M, z ^ j * c j x) y :=
    DifferentiableAt.fun_sum fun j _ => hdz j
  have hL : DifferentiableAt ℝ (Lc (n := n)) y := diff_of contDiff_Lc y
  have hW : dirC (W z) (vkl k l) y = W z y * (-z * om k l y) := by
    unfold W
    rw [dirC_exp (hL.const_mul _), dirC_const_mul hL]
    rfl
  have hcM : dirC (c M) (vkl k l) y = 0 := by rw [hM M le_rfl]; exact dirC_zero _ _
  unfold Dkl
  rw [dirC_mul (diff_of (contDiff_W_apply z) y) hS, dirC_sum _ (fun j _ => hdz j), hW]
  simp only [TD, mul_sub, Finset.sum_sub_distrib]
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  simp only [sh, mul_zero, Dkl, hcM, add_zero, pow_zero, one_mul]
  have e1 : ∀ j ∈ Finset.range M, dirC (fun x => z ^ j * c j x) (vkl k l) y = z ^ j * dirC (c j) (vkl k l) y :=
    fun j _ => dirC_const_mul (hd j) _ _
  rw [Finset.sum_congr rfl e1]
  have key : ∑ j ∈ Finset.range M, z ^ (j + 1) * (om k l y * c j y) =
      z * om k l y * ∑ j ∈ Finset.range M, z ^ j * c j y := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [key]
  ring

/- English proof (translation)
The claim follows from `| [], c, hc => hc | a :: l, c, hc => TD_smooth (foldr_smooth f l c hc) a (f a)`.
-/
theorem foldr_smooth (f : Fin n → Fin n) : ∀ (l : List (Fin n)) (c : ℕ → E n → ℂ),
    (∀ j, ContDiff ℝ (⊤ : ℕ∞) (c j)) → ∀ j, ContDiff ℝ (⊤ : ℕ∞) ((l.foldr (fun k c' => TD k (f k) c') c) j)
  | [], c, hc => hc
  | a :: l, c, hc => TD_smooth (foldr_smooth f l c hc) a (f a)

/- English proof (translation)
The claim follows from `| [], c, M, hM => by simpa using hM | a :: l, c, M, hM => by intro j hj simp only [List.foldr_cons] exact TD_supp (M := M + l.length) (foldr_supp f l c M hM) a (f a) j (by simp only [List.length_cons] at hj; omega)`.
-/
theorem foldr_supp (f : Fin n → Fin n) : ∀ (l : List (Fin n)) (c : ℕ → E n → ℂ) (M : ℕ),
    (∀ j, M ≤ j → c j = 0) → ∀ j, M + l.length ≤ j → (l.foldr (fun k c' => TD k (f k) c') c) j = 0
  | [], c, M, hM => by simpa using hM
  | a :: l, c, M, hM => by
      intro j hj
      simp only [List.foldr_cons]
      exact TD_supp (M := M + l.length) (foldr_supp f l c M hM) a (f a) j
        (by simp only [List.length_cons] at hj; omega)

/- English proof (translation)
The claim follows from `| [], c, M, _, _ => by simp | a :: l, c, M, hc, hM => by rw [List.foldr_cons, word z f l c M hc hM, List.foldr_cons, List.length_cons, ← add_assoc] exact step z a (f a) _ (M + l.length) (foldr_smooth f l c hc) (foldr_supp f l c M hM)`.
-/
theorem word (z : ℂ) (f : Fin n → Fin n) : ∀ (l : List (Fin n)) (c : ℕ → E n → ℂ) (M : ℕ),
    (∀ j, ContDiff ℝ (⊤ : ℕ∞) (c j)) → (∀ j, M ≤ j → c j = 0) →
    l.foldr (fun k g => Dkl k (f k) g) (fun y => W z y * ∑ j ∈ Finset.range M, z ^ j * c j y) =
      fun y => W z y * ∑ j ∈ Finset.range (M + l.length), z ^ j * (l.foldr (fun k c' => TD k (f k) c') c) j y
  | [], c, M, _, _ => by simp
  | a :: l, c, M, hc, hM => by
      rw [List.foldr_cons, word z f l c M hc hM, List.foldr_cons, List.length_cons, ← add_assoc]
      exact step z a (f a) _ (M + l.length) (foldr_smooth f l c hc) (foldr_supp f l c M hM)

def TDelta (c : ℕ → E n → ℂ) : ℕ → E n → ℂ := fun j y =>
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((List.finRange n).foldr (fun k c' => TD k (σ k) c') c) j y

/- English proof (translation)
The claim follows from `ContDiff.sum fun σ _ => contDiff_const.mul (foldr_smooth σ _ c hc j)`.
-/
theorem TDelta_smooth {c : ℕ → E n → ℂ} (hc : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (c j)) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (TDelta c j) :=
  ContDiff.sum fun σ _ => contDiff_const.mul (foldr_smooth σ _ c hc j)

/- English proof (translation)
Introduce `j hj`. Use function extensionality and compare the values at `y`. Simplify using `only [TDelta, Pi.zero_apply]`. Use `Finset.sum_eq_zero fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[foldr_supp σ (List.finRange n) c M hM j (by simpa using hj)]`.

Simplify using the standard rewrite rules.
-/
theorem TDelta_supp {c : ℕ → E n → ℂ} {M : ℕ} (hM : ∀ j, M ≤ j → c j = 0) :
    ∀ j, M + n ≤ j → TDelta c j = 0 := by
  intro j hj
  funext y
  simp only [TDelta, Pi.zero_apply]
  refine Finset.sum_eq_zero fun σ _ => ?_
  rw [foldr_supp σ (List.finRange n) c M hM j (by simpa using hj)]
  simp

/- English proof (translation)
Use function extensionality and compare the values at `y`. Unfold `Delta`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Simplify using `only [word z _ (List.finRange n) c M hc hM, List.length_finRange]`. Simplify using `only [TDelta, Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun σ _ => by ring`.
-/
theorem delta_step (z : ℂ) (c : ℕ → E n → ℂ) (M : ℕ) (hc : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (c j))
    (hM : ∀ j, M ≤ j → c j = 0) :
    Delta (fun y => W z y * ∑ j ∈ Finset.range M, z ^ j * c j y) =
      fun y => W z y * ∑ j ∈ Finset.range (M + n), z ^ j * TDelta c j y := by
  funext y
  unfold Delta
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [word z _ (List.finRange n) c M hc hM, List.length_finRange]
  simp only [TDelta, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun σ _ => by ring

/- English proof (translation)
The claim follows from `| 0, _, hc => hc | N + 1, c, hc => by rw [Function.iterate_succ_apply] exact iter_smooth N (TDelta_smooth hc)`.
-/
theorem iter_smooth : ∀ (N : ℕ) {c : ℕ → E n → ℂ}, (∀ j, ContDiff ℝ (⊤ : ℕ∞) (c j)) →
    ∀ j, ContDiff ℝ (⊤ : ℕ∞) ((TDelta^[N] c) j)
  | 0, _, hc => hc
  | N + 1, c, hc => by
      rw [Function.iterate_succ_apply]
      exact iter_smooth N (TDelta_smooth hc)

/- English proof (translation)
The claim follows from `| 0, c, M, _, _ => by simp | N + 1, c, M, hc, hM => by rw [Function.iterate_succ_apply, delta_step z c M hc hM, iter z N (TDelta c) (M + n) (TDelta_smooth hc) (TDelta_supp hM), Function.iterate_succ_apply, show M + n + n * N = M + n * (N + 1) by ring]`.
-/
theorem iter (z : ℂ) : ∀ (N : ℕ) (c : ℕ → E n → ℂ) (M : ℕ), (∀ j, ContDiff ℝ (⊤ : ℕ∞) (c j)) →
    (∀ j, M ≤ j → c j = 0) →
    Delta^[N] (fun y => W z y * ∑ j ∈ Finset.range M, z ^ j * c j y) =
      fun y => W z y * ∑ j ∈ Finset.range (M + n * N), z ^ j * (TDelta^[N] c) j y
  | 0, c, M, _, _ => by simp
  | N + 1, c, M, hc, hM => by
      rw [Function.iterate_succ_apply, delta_step z c M hc hM,
        iter z N (TDelta c) (M + n) (TDelta_smooth hc) (TDelta_supp hM), Function.iterate_succ_apply,
        show M + n + n * N = M + n * (N + 1) by ring]

end TW

open TW in
/- English proof (translation)
Introduce `n H hH N`. Set `c0 : ℕ → E n → ℂ` to `fun j => if j = 0 then H else 0`. Establish `hc0 : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (c0 j)`. Introduce `j`. Distinguish the cases in `h : j = 0`.

Simplify using `only [c0, h, if_true]`. Conclude with `hH`. Simplify using `only [c0, h, if_false]`. Conclude with `contDiff_const`. Establish `hc0s : ∀ j, 1 ≤ j → c0 j = 0`.

Introduce `j hj`. Simplify using `only [c0, show j ≠ 0 by omega, if_false]`. Use `⟨TDelta^[N] c0, iter_smooth N hc0, ?_⟩` and prove the remaining obligations. Introduce `z y`. Establish `h0 : (fun y => ((dP y : ℝ) : ℂ) ^ (-z) * H y) = fun y => W z y * ∑ j ∈ Finset.range 1, z ^ j * c0 j y`.

Use function extensionality and compare the values at `y`. Simplify using `[c0, cpow_eq]`. Rewrite using `[h0, iter z N c0 1 hc0 hc0s, cpow_eq, add_comm 1 (n * N)]`.
-/
theorem twist : Twist := by
  intro n H hH N
  let c0 : ℕ → E n → ℂ := fun j => if j = 0 then H else 0
  have hc0 : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (c0 j) := by
    intro j
    by_cases h : j = 0
    · simp only [c0, h, if_true]; exact hH
    · simp only [c0, h, if_false]; exact contDiff_const
  have hc0s : ∀ j, 1 ≤ j → c0 j = 0 := by
    intro j hj
    simp only [c0, show j ≠ 0 by omega, if_false]
  refine ⟨TDelta^[N] c0, iter_smooth N hc0, ?_⟩
  intro z y
  have h0 : (fun y => ((dP y : ℝ) : ℂ) ^ (-z) * H y) =
      fun y => W z y * ∑ j ∈ Finset.range 1, z ^ j * c0 j y := by
    funext y
    simp [c0, cpow_eq]
  rw [h0, iter z N c0 1 hc0 hc0s, cpow_eq, add_comm 1 (n * N)]

end PositivityTheory.Rg.Sw.WR.K.GB
