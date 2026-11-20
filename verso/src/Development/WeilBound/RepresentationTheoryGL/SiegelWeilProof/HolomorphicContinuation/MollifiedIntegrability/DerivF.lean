import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.DerivFA
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ContinuousEvXI
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ContinuousEvX

noncomputable section

open MeasureTheory Filter Topology

namespace PositivityTheory.Rg.Sw.WR.D

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR

variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem FP_eq_integral_Fi (P : PX m n) (y : E n) : FP ε c t P y = ∫ x, Fi ε c t P y x := rfl

/- English proof (translation)
Rewrite using `[(hasFDerivAt_FP hI hq hc P y).fderiv, ContinuousLinearMap.integral_apply (integrable_Fd hI hq hc P y)]`. Use `integral_congr_ae (ae_of_all _ fun x => ?_)` and prove the remaining obligations. Simplify using `only [Fd, ContinuousLinearMap.smul_apply, Lc_apply, smul_eq_mul, Fi]`.
-/
theorem fderiv_FP_apply (hI : IntG) (hq : Continuous (qX (n := n) ε)) (hc : 0 < c) (P : PX m n) (y w : E n) :
    fderiv ℝ (FP ε c t P) y w = ∫ x, Fi ε c t P y x * (Complex.I * t) * ((ip w (qX ε x) : ℝ) : ℂ) := by
  rw [(hasFDerivAt_FP hI hq hc P y).fderiv, ContinuousLinearMap.integral_apply (integrable_Fd hI hq hc P y)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [Fd, ContinuousLinearMap.smul_apply, Lc_apply, smul_eq_mul, Fi]

/- English proof (translation)
Establish `h` using `(integrable_Fd (t := t) hI hq hc P y).apply_continuousLinearMap w`. Use `h.congr (ae_of_all _ fun x => ?_)` and prove the remaining obligations. Simplify using `only [Fd, ContinuousLinearMap.smul_apply, Lc_apply, smul_eq_mul, Fi]`.
-/
theorem integrable_Fi_mul (hI : IntG) (hq : Continuous (qX (n := n) ε)) (hc : 0 < c) (P : PX m n) (y w : E n) :
    Integrable fun x => Fi ε c t P y x * (Complex.I * t) * ((ip w (qX ε x) : ℝ) : ℂ) := by
  have h := (integrable_Fd (t := t) hI hq hc P y).apply_continuousLinearMap w
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only [Fd, ContinuousLinearMap.smul_apply, Lc_apply, smul_eq_mul, Fi]

/- English proof (translation)
Unfold `dirC`. Rewrite using `[fderiv_FP_apply hI hq hc, fderiv_FP_apply hI hq hc, ← integral_const_mul, ← integral_add (integrable_Fi_mul hI hq hc P y _) ((integrable_Fi_mul hI hq hc P y _).const_mul _)]`. Use `integral_congr_ae (ae_of_all _ fun x => ?_)` and prove the remaining obligations. Establish `e : ∀ a b, v a b = ((v a b).re : ℂ) + Complex.I * ((v a b).im : ℂ)` using `fun a b => by`. Rewrite using `[mul_comm]`.

Conclude with `(Complex.re_add_im (v a b)).symm`. Simplify using `only [ip, Complex.ofReal_sum, Complex.ofReal_mul]`. Use `conv_rhs => rw [show (∑ a, ∑ b, v a b * (qX ε x a b : ℂ)) = ∑ a, ∑ b, (((v a b).re : ℂ) + Complex.I * ((v a b).im : ℂ)) * (qX ε x a b : ℂ) from Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [← e]]`. Simplify using `only [add_mul, Finset.sum_add_distrib, mul_add, Finset.mul_sum]`. Put the polynomial expressions in normal form.
-/
theorem dirC_FP (hI : IntG) (hq : Continuous (qX (n := n) ε)) (hc : 0 < c) (P : PX m n)
    (v : Fin n → Fin n → ℂ) (y : E n) :
    dirC (FP ε c t P) v y =
      ∫ x, Fi ε c t P y x * (Complex.I * t) * ∑ a, ∑ b, v a b * (qX ε x a b : ℂ) := by
  unfold dirC
  rw [fderiv_FP_apply hI hq hc, fderiv_FP_apply hI hq hc, ← integral_const_mul,
    ← integral_add (integrable_Fi_mul hI hq hc P y _) ((integrable_Fi_mul hI hq hc P y _).const_mul _)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  have e : ∀ a b, v a b = ((v a b).re : ℂ) + Complex.I * ((v a b).im : ℂ) := fun a b => by
    rw [mul_comm]; exact (Complex.re_add_im (v a b)).symm
  simp only [ip, Complex.ofReal_sum, Complex.ofReal_mul]
  conv_rhs => rw [show (∑ a, ∑ b, v a b * (qX ε x a b : ℂ)) =
    ∑ a, ∑ b, (((v a b).re : ℂ) + Complex.I * ((v a b).im : ℂ)) * (qX ε x a b : ℂ) from
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [← e]]
  simp only [add_mul, Finset.sum_add_distrib, mul_add, Finset.mul_sum]
  ring_nf

/- English proof (translation)
Rewrite using `[Finset.sum_eq_single k, Finset.sum_eq_single l]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[hb]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`. Introduce `a _ ha`. Simplify using `[ha]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem sum_ite_pair (k l : Fin n) (α : ℂ) (f : Fin n → Fin n → ℂ) :
    ∑ a, ∑ b, (if a = k ∧ b = l then α else 0) * f a b = α * f k l := by
  rw [Finset.sum_eq_single k, Finset.sum_eq_single l]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro a _ ha; simp [ha]
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Establish `h` using `congrFun (congrFun ((hA m n ε).2.1 x) k) l`. Establish `g : gramX ε x k l = evX (Qp ε k l) x` using `rfl`. Rewrite using `[← g, ← h]`. Simplify using `only [vkl, add_mul, Finset.sum_add_distrib]`. Rewrite using `[sum_ite_pair k l _ (fun a b => (qX ε x a b : ℂ)), sum_ite_pair l k _ (fun a b => (qX ε x a b : ℂ))]`.

Simplify using `only [herm]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_vkl (hA : AlgA) (k l : Fin n) (x : Fin m → Fin n → ℂ) :
    ∑ a, ∑ b, vkl k l a b * (qX ε x a b : ℂ) = evX (Qp ε k l) x := by
  have h := congrFun (congrFun ((hA m n ε).2.1 x) k) l
  have g : gramX ε x k l = evX (Qp ε k l) x := rfl
  rw [← g, ← h]
  simp only [vkl, add_mul, Finset.sum_add_distrib]
  rw [sum_ite_pair k l _ (fun a b => (qX ε x a b : ℂ)), sum_ite_pair l k _ (fun a b => (qX ε x a b : ℂ))]
  simp only [herm]
  push_cast
  ring

/- English proof (translation)
Establish `hq` using `(hA m n ε).2.2.2.2`. Use function extensionality and compare the values at `y`. Unfold `Dkl`. Rewrite using `[dirC_FP hI hq hc]`. Unfold `FP`.

Use `integral_congr_ae (ae_of_all _ fun x => ?_)` and prove the remaining obligations. Simplify using `only`. Rewrite using `[sum_vkl hA]`. Simplify using `only [Fi, evX, map_mul, MvPolynomial.eval_C]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Dkl_FP (hI : IntG) (hA : AlgA) (hc : 0 < c) (P : PX m n) (k l : Fin n) :
    Dkl k l (FP ε c t P) = FP ε c t (MvPolynomial.C (Complex.I * t) * Qp ε k l * P) := by
  have hq := (hA m n ε).2.2.2.2
  funext y
  unfold Dkl
  rw [dirC_FP hI hq hc]
  unfold FP
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  dsimp only
  rw [sum_vkl hA]
  simp only [Fi, evX, map_mul, MvPolynomial.eval_C]
  ring

/- English proof (translation)
Establish `hq` using `(hA m n ε).2.2.2.2`. Use function extensionality and compare the values at `y`. Simplify using `only [Pi.add_apply]`. Rewrite using `[FP_eq_integral_Fi, FP_eq_integral_Fi, FP_eq_integral_Fi, ← integral_add (integrable_Fi hI hq hc P y) (integrable_Fi hI hq hc Q y)]`. Use `integral_congr_ae (ae_of_all _ fun x => ?_)` and prove the remaining obligations.

Simplify using `only [Fi, evX, map_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem FP_add (hI : IntG) (hA : AlgA) (hc : 0 < c) (P Q : PX m n) :
    FP ε c t (P + Q) = FP ε c t P + FP ε c t Q := by
  have hq := (hA m n ε).2.2.2.2
  funext y
  simp only [Pi.add_apply]
  rw [FP_eq_integral_Fi, FP_eq_integral_Fi, FP_eq_integral_Fi,
    ← integral_add (integrable_Fi hI hq hc P y) (integrable_Fi hI hq hc Q y)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [Fi, evX, map_add]; ring

/- English proof (translation)
Use function extensionality and compare the values at `y`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Rewrite using `[FP_eq_integral_Fi, FP_eq_integral_Fi, ← integral_const_mul]`. Use `integral_congr_ae (ae_of_all _ fun x => ?_)` and prove the remaining obligations. Simplify using `only [Fi, evX, map_mul, MvPolynomial.eval_C]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem FP_C_mul (a : ℂ) (P : PX m n) :
    FP ε c t (MvPolynomial.C a * P) = a • FP ε c t P := by
  funext y
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [FP_eq_integral_Fi, FP_eq_integral_Fi, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [Fi, evX, map_mul, MvPolynomial.eval_C]; ring

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Use function extensionality and compare the values at `y`. Simplify using `only [Finset.sum_empty, Finset.sum_apply, Pi.zero_apply]`. Rewrite using `[FP_eq_integral_Fi]`.

Simplify using `[Fi, evX]`. Consider the case `insert i s hi ih`. Rewrite using `[Finset.sum_insert hi, Finset.sum_insert hi, FP_add hI hA hc, ih]`.
-/
theorem FP_sum (hI : IntG) (hA : AlgA) (hc : 0 < c) {ι : Type*} (s : Finset ι) (f : ι → PX m n) :
    FP ε c t (∑ i ∈ s, f i) = ∑ i ∈ s, FP ε c t (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    funext y
    simp only [Finset.sum_empty, Finset.sum_apply, Pi.zero_apply]
    rw [FP_eq_integral_Fi]
    simp [Fi, evX]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, FP_add hI hA hc, ih]

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => simp`. Consider the case `cons k L ih`. Rewrite using `[List.foldr_cons, ih, Dkl_FP hI hA hc, List.map_cons, List.prod_cons]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem foldr_FP (hI : IntG) (hA : AlgA) (hc : 0 < c) (σ : Equiv.Perm (Fin n)) (L : List (Fin n)) (P : PX m n) :
    L.foldr (fun k g => Dkl k (σ k) g) (FP ε c t P) =
      FP ε c t ((L.map fun k => MvPolynomial.C (Complex.I * t) * Qp ε k (σ k)).prod * P) := by
  induction L with
  | nil => simp
  | cons k L ih =>
    rw [List.foldr_cons, ih, Dkl_FP hI hA hc, List.map_cons, List.prod_cons]
    congr 1; ring

/- English proof (translation)
Establish `hprod : ∀ σ : Equiv.Perm (Fin n), ((List.finRange n).map fun k => MvPolynomial.C (Complex.I * t) * Qp ε k (σ k)).prod = MvPolynomial.C ((Complex.I * t) ^ n) * ∏ k, Qp ε k (σ k)`. Introduce `σ`. Rewrite using `[← Fin.prod_univ_def, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, map_pow]`. Simplify using `only [hprod]`. Rewrite using `[detQ, ← Matrix.det_transpose, Matrix.det_apply', Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Simplify using `only [Matrix.transpose_apply, Matrix.of_apply]`. Rewrite using `[show (MvPolynomial.C (((Equiv.Perm.sign σ : ℤ) : ℂ)) : PX m n) = (((Equiv.Perm.sign σ : ℤ) : PX m n)) by simp]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_perm_eq_det :
    ∑ σ : Equiv.Perm (Fin n), MvPolynomial.C ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      (((List.finRange n).map fun k => MvPolynomial.C (Complex.I * t) * Qp ε k (σ k)).prod)
      = MvPolynomial.C ((Complex.I * t) ^ n) * detQ ε := by
  have hprod : ∀ σ : Equiv.Perm (Fin n),
      ((List.finRange n).map fun k => MvPolynomial.C (Complex.I * t) * Qp ε k (σ k)).prod =
        MvPolynomial.C ((Complex.I * t) ^ n) * ∏ k, Qp ε k (σ k) := by
    intro σ
    rw [← Fin.prod_univ_def, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      map_pow]
  simp only [hprod]
  rw [detQ, ← Matrix.det_transpose, Matrix.det_apply', Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Matrix.transpose_apply, Matrix.of_apply]
  rw [show (MvPolynomial.C (((Equiv.Perm.sign σ : ℤ) : ℂ)) : PX m n) = (((Equiv.Perm.sign σ : ℤ) : PX m n)) by
    simp]
  ring

/- English proof (translation)
Unfold `Delta`. Simplify using `only [foldr_FP hI hA hc]`. Rewrite using `[← sum_perm_eq_det (ε := ε) (t := t), Finset.sum_mul, FP_sum hI hA hc]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, FP_C_mul]`.
-/
theorem Delta_FP (hI : IntG) (hA : AlgA) (hc : 0 < c) (P : PX m n) :
    Delta (FP ε c t P) = FP ε c t (MvPolynomial.C ((Complex.I * t) ^ n) * detQ ε * P) := by
  unfold Delta
  simp only [foldr_FP hI hA hc]
  rw [← sum_perm_eq_det (ε := ε) (t := t), Finset.sum_mul, FP_sum hI hA hc]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [mul_assoc, FP_C_mul]

/- English proof (translation)
Introduce `m n ε c t hc P N`. Establish `hq` using `(hA m n ε).2.2.2.2`. Use `⟨continuous_iff_continuousAt.2 fun y => (hasFDerivAt_FP hI hq hc P y).continuousAt, ?_⟩` and prove the remaining obligations. Proceed by induction on `N with`. Consider the case `zero => simp`.

Consider the case `succ N ih`. Rewrite using `[Function.iterate_succ_apply', ih, Delta_FP hI hA hc, pow_succ]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem derivF_of (hI : IntG) (hA : AlgA) : DerivF := by
  intro m n ε c t hc P N
  have hq := (hA m n ε).2.2.2.2
  refine ⟨continuous_iff_continuousAt.2 fun y => (hasFDerivAt_FP hI hq hc P y).continuousAt, ?_⟩
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Function.iterate_succ_apply', ih, Delta_FP hI hA hc, pow_succ]
    congr 1; ring

/- English proof (translation)
The claim follows from `derivF_of intG algA`.
-/
theorem derivF : DerivF := derivF_of intG algA

end PositivityTheory.Rg.Sw.WR.D
