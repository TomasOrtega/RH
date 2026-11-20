import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LamF
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealSymplecticFormAlternatingInvariantDefinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieAlgebrasAtPlaceActFockVectorsByFockOperators
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockTransl.Jet

open Complex

variable {D : D7}

/- English proof (translation)
Establish `h1 : M.adjugate.map f = (M.map f).adjugate`. Use `RingHom.map_adjugate f M` as an intermediate fact. Simplify `this` using `[RingHom.mapMatrix_apply]`. Establish `h2 : (M.map f).det = f M.det`. Use `RingHom.map_det f M` as an intermediate fact.

Simplify `this.symm` using `[RingHom.mapMatrix_apply]`. Rewrite using `[Matrix.inv_def, Matrix.inv_def, Matrix.map_smul' _ _ _ (map_mul f), h1, h2, Ring.inverse_eq_inv', Ring.inverse_eq_inv', map_inv₀]`.
-/
theorem map_inv_ringHom {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    (M⁻¹).map f = (M.map f)⁻¹ := by
  have h1 : M.adjugate.map f = (M.map f).adjugate := by
    have := RingHom.map_adjugate f M; simpa [RingHom.mapMatrix_apply] using this
  have h2 : (M.map f).det = f M.det := by
    have := RingHom.map_det f M; simpa [RingHom.mapMatrix_apply] using this.symm
  rw [Matrix.inv_def, Matrix.inv_def, Matrix.map_smul' _ _ _ (map_mul f), h1, h2, Ring.inverse_eq_inv',
    Ring.inverse_eq_inv', map_inv₀]

/- English proof (translation)
Unfold `GlobalTheory.OrientedHeis.formAt GlobalTheory.VacUnique.omAt GlobalTheory.VacUnique.hAt`. Use `congr 3`. Rewrite using `[gramAt, gramAt, ← map_inv_ringHom]`. Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.conjTranspose_apply, Finset.sum_mul, RCLike.star_def]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm]`. Use `conv_rhs => rw [Finset.sum_comm]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`.
-/
theorem formAt_eq_omAt (S T : HSp D) (τ : D.what₂.Tau) (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    GlobalTheory.OrientedHeis.formAt S T τ x y = GlobalTheory.VacUnique.omAt S T τ x y := by
  unfold GlobalTheory.OrientedHeis.formAt GlobalTheory.VacUnique.omAt GlobalTheory.VacUnique.hAt
  congr 3
  rw [gramAt, gramAt, ← map_inv_ringHom]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul, RCLike.star_def]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]

/- English proof (translation)
Rewrite using `[GlobalTheory.VacUnique.omO_apply]`. Conclude with `Finset.sum_congr rfl fun τ _ => formAt_eq_omAt S T τ _ _`.
-/
theorem omF_eq {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z e : VCx D.what₂.Tau S.rank T.rank) :
    omF A B z e = GlobalTheory.VacUnique.omO S T (fmR A B z) (fmR A B e) := by
  rw [GlobalTheory.VacUnique.omO_apply]
  exact Finset.sum_congr rfl fun τ _ => formAt_eq_omAt S T τ _ _

/- English proof (translation)
Simplify using `only [cplxO, Matrix.mul_smul, Matrix.smul_mul]`. Conclude with `smul_comm _ _ _`.
-/
theorem cplxO_smulC' {m n : ℕ} (s : Matrix (Fin n) (Fin n) ℂ) (t : Matrix (Fin m) (Fin m) ℂ) (c : ℂ)
    (x : Matrix (Fin m) (Fin n) ℂ) : cplxO s t (c • x) = c • cplxO s t x := by
  simp only [cplxO, Matrix.mul_smul, Matrix.smul_mul]
  exact smul_comm _ _ _

/- English proof (translation)
Simplify using `only [cplxO, Matrix.mul_sum, Matrix.sum_mul, Finset.smul_sum]`.
-/
theorem cplxO_sum' {m n p q : ℕ} (s : Matrix (Fin n) (Fin n) ℂ) (t : Matrix (Fin m) (Fin m) ℂ)
    (x : Fin p → Fin q → Matrix (Fin m) (Fin n) ℂ) :
    cplxO s t (∑ i, ∑ j, x i j) = ∑ i, ∑ j, cplxO s t (x i j) := by
  simp only [cplxO, Matrix.mul_sum, Matrix.sum_mul, Finset.smul_sum]

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Use `show fockMat A B τ ((I • z) τ) = cplxO (A.cart τ) (B.cart τ) (fockMat A B τ (z τ))`. Establish `hs` using `(GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A τ).1`. Establish `ht` using `(GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv B τ).1`. Unfold `fockMat`.

Rewrite using `[cplxO_sum']`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.VacUnique.cplxO_add, cplxO_smulC', cplxO_smulC', GlobalTheory.RealSymplForm.cplxO_cplxO hs ht]`. Establish `e1 : ((I • z) τ i j).re = -(z τ i j).im` using `by simp`. Establish `e2 : ((I • z) τ i j).im = (z τ i j).re` using `by simp`.

Rewrite using `[e1, e2]`. Simplify using `only [smul_neg, Complex.ofReal_neg, neg_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem fmR_I {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z : VCx D.what₂.Tau S.rank T.rank) :
    fmR A B (I • z) = GlobalTheory.VacUnique.jO S T A.cart B.cart (fmR A B z) := by
  funext τ
  show fockMat A B τ ((I • z) τ) = cplxO (A.cart τ) (B.cart τ) (fockMat A B τ (z τ))
  have hs := (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A τ).1
  have ht := (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv B τ).1
  unfold fockMat
  rw [cplxO_sum']
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [GlobalTheory.VacUnique.cplxO_add, cplxO_smulC', cplxO_smulC', GlobalTheory.RealSymplForm.cplxO_cplxO hs ht]
  have e1 : ((I • z) τ i j).re = -(z τ i j).im := by simp
  have e2 : ((I • z) τ i j).im = (z τ i j).re := by simp
  rw [e1, e2]
  simp only [smul_neg, Complex.ofReal_neg, neg_smul]
  abel

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Use `show fockMat A B τ (z τ + w τ) = fockMat A B τ (z τ) + fockMat A B τ (w τ)`. Simplify using `only [fockMat, Pi.add_apply, Complex.add_re, Complex.add_im, Complex.ofReal_add, add_smul, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Normalize the expressions using the abelian group laws.
-/
theorem fmR_add {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z w : VCx D.what₂.Tau S.rank T.rank) :
    fmR A B (z + w) = fmR A B z + fmR A B w := by
  funext τ
  show fockMat A B τ (z τ + w τ) = fockMat A B τ (z τ) + fockMat A B τ (w τ)
  simp only [fockMat, Pi.add_apply, Complex.add_re, Complex.add_im, Complex.ofReal_add, add_smul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  abel

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Use `show fockMat A B τ (c • z τ) = c • fockMat A B τ (z τ)`. Simplify using `only [fockMat, Pi.smul_apply, Complex.smul_re, Complex.smul_im, smul_eq_mul, Complex.ofReal_mul, mul_smul, Finset.smul_sum, smul_add]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [Complex.coe_smul]`.
-/
theorem fmR_smul {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (c : ℝ) (z : VCx D.what₂.Tau S.rank T.rank) :
    fmR A B (c • z) = c • fmR A B z := by
  funext τ
  show fockMat A B τ (c • z τ) = c • fockMat A B τ (z τ)
  simp only [fockMat, Pi.smul_apply, Complex.smul_re, Complex.smul_im, smul_eq_mul, Complex.ofReal_mul,
    mul_smul, Finset.smul_sum, smul_add]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.coe_smul]

/- English proof (translation)
Rewrite using `[omF_eq, omF_eq, omF_eq, fmR_add, map_add, LinearMap.add_apply]`.
-/
theorem omF_add {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z w e : VCx D.what₂.Tau S.rank T.rank) :
    omF A B (z + w) e = omF A B z e + omF A B w e := by
  rw [omF_eq, omF_eq, omF_eq, fmR_add, map_add, LinearMap.add_apply]

/- English proof (translation)
Rewrite using `[omF_eq, omF_eq, fmR_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]`.
-/
theorem omF_smul {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (c : ℝ) (z e : VCx D.what₂.Tau S.rank T.rank) :
    omF A B (c • z) e = c * omF A B z e := by
  rw [omF_eq, omF_eq, fmR_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]

/- English proof (translation)
Take `⟨hJJ, -, hinv, -⟩` from `GlobalTheory.RealSymplForm.form_alt_inv_def D S T A.cart B.cart (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A) (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv B)`. Rewrite using `[omF_eq, omF_eq, fmR_I, fmR_I]`. Use `set J := GlobalTheory.VacUnique.jO S T A.cart B.cart`. Use `set x := fmR A B z`. Use `set y := fmR A B e`.

Establish `hy : y = -J (J y)` using `by rw [hJJ, neg_neg]`. Use `conv_lhs => rw [hy]`. Rewrite using `[map_neg, hinv]`.
-/
theorem omF_I {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z e : VCx D.what₂.Tau S.rank T.rank) :
    omF A B (I • z) e = -omF A B z (I • e) := by
  obtain ⟨hJJ, -, hinv, -⟩ := GlobalTheory.RealSymplForm.form_alt_inv_def D S T A.cart B.cart
    (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A) (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv B)
  rw [omF_eq, omF_eq, fmR_I, fmR_I]
  set J := GlobalTheory.VacUnique.jO S T A.cart B.cart
  set x := fmR A B z
  set y := fmR A B e
  have hy : y = -J (J y) := by rw [hJJ, neg_neg]
  conv_lhs => rw [hy]
  rw [map_neg, hinv]

/- English proof (translation)
Rewrite using `[omF_I, smul_smul, I_mul_I, neg_one_smul, omF_eq, omF_eq]`. Establish `: fmR A B (-e) = -fmR A B e`. Establish `h` using `fmR_smul A B (-1) e`. Rewrite `h` using `[neg_one_smul, neg_one_smul]`. Conclude with `h`.

Rewrite using `[this, map_neg, neg_neg]`.
-/
theorem omF_I_I {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z e : VCx D.what₂.Tau S.rank T.rank) :
    omF A B (I • z) (I • e) = omF A B z e := by
  rw [omF_I, smul_smul, I_mul_I, neg_one_smul, omF_eq, omF_eq]
  have : fmR A B (-e) = -fmR A B e := by
    have h := fmR_smul A B (-1) e
    rw [neg_one_smul, neg_one_smul] at h
    exact h
  rw [this, map_neg, neg_neg]

variable {ι : Type} [Fintype ι] {a b : ℕ}

/- English proof (translation)
Simplify using `only [gD, Pi.add_apply, add_mul, Complex.add_re, mul_add, Finset.sum_add_distrib]`.
-/
theorem gD_add (c : ι → ℝ) (z w e : VCx ι a b) : gD c (z + w) e = gD c z e + gD c w e := by
  simp only [gD, Pi.add_apply, add_mul, Complex.add_re, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [gD, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, Complex.real_smul, mul_assoc, Complex.re_ofReal_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gD_smul (c : ι → ℝ) (r : ℝ) (z e : VCx ι a b) : gD c (r • z) e = r * gD c z e := by
  simp only [gD, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, Complex.real_smul, mul_assoc, Complex.re_ofReal_mul]
  ring

/- English proof (translation)
Simplify using `only [gD, ← mul_neg, ← Finset.sum_neg_distrib]`. Use `congr 1`. Use `Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gD_I (c : ι → ℝ) (z e : VCx ι a b) : gD c (I • z) e = -gD c z (I • e) := by
  simp only [gD, ← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im]
  ring

/- English proof (translation)
Simplify using `only [gD]`. Use `congr 1`. Use `Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gD_I_I (c : ι → ℝ) (z e : VCx ι a b) : gD c (I • z) (I • e) = gD c z e := by
  simp only [gD]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im]
  ring

end GlobalTheory.FockTransl.Jet

namespace GlobalTheory.FockTransl.Jet

open Complex

variable {D : D7}

/- English proof (translation)
Simplify using `only [lamF, omF_add, gD_add]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lamF_add {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank)
    (z w : VCx D.what₂.Tau S.rank T.rank) : lamF A B l (z + w) = lamF A B l z + lamF A B l w := by
  simp only [lamF, omF_add, gD_add]
  push_cast
  ring

/- English proof (translation)
Simplify using `only [lamF, omF_smul, gD_smul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lamF_smul {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank)
    (r : ℝ) (z : VCx D.what₂.Tau S.rank T.rank) : lamF A B l (r • z) = r * lamF A B l z := by
  simp only [lamF, omF_smul, gD_smul]
  push_cast
  ring

/- English proof (translation)
Simplify using `only [lamF]`. Rewrite using `[omF_I_I, omF_I, gD_I_I, gD_I]`. Use `push_cast`. Take the linear combination `(-(1 / 2 : ℂ) * (Real.pi : ℂ) * (omF A B z (Formalism.L2.Ker.coordX l) : ℂ) + (1 / 4 : ℂ) * (gD (fw D) z (I • Formalism.L2.Ker.coordX l) : ℂ)) * Complex.I_sq`.
-/
theorem lamF_I {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank)
    (z : VCx D.what₂.Tau S.rank T.rank) : lamF A B l (I • z) = -I * lamF A B l z := by
  simp only [lamF]
  rw [omF_I_I, omF_I, gD_I_I, gD_I]
  push_cast
  linear_combination (-(1 / 2 : ℂ) * (Real.pi : ℂ) * (omF A B z (Formalism.L2.Ker.coordX l) : ℂ) +
    (1 / 4 : ℂ) * (gD (fw D) z (I • Formalism.L2.Ker.coordX l) : ℂ)) * Complex.I_sq

/- English proof (translation)
Introduce `D S T A B l`. Use `⟨fun a b => lamF_add A B l a b, fun t a => ?_⟩` and prove the remaining obligations. Establish `e : t • a = (t.re : ℝ) • a + (t.im : ℝ) • (I • a)`. Use function extensionality and compare the values at `τ i j`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]`.

Use `conv_lhs => rw [← Complex.re_add_im t]`. Expand and normalize the polynomial expressions, which then agree. Apply the tactic sequence `have hc : conj t = (t.re : ℂ) - t.im * I := by apply Complex.ext <;> simp`. Rewrite using `[e, lamF_add, lamF_smul, lamF_smul, lamF_I, hc]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lamF_antilinear : ∀ (D : D7) (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank), (∀ a b, GlobalTheory.FockTransl.Jet.lamF A B l (a + b) = GlobalTheory.FockTransl.Jet.lamF A B l a + GlobalTheory.FockTransl.Jet.lamF A B l b) ∧ ∀ (t : ℂ) a, GlobalTheory.FockTransl.Jet.lamF A B l (t • a) = conj t * GlobalTheory.FockTransl.Jet.lamF A B l a := by
  intro D S T A B l
  refine ⟨fun a b => lamF_add A B l a b, fun t a => ?_⟩
  have e : t • a = (t.re : ℝ) • a + (t.im : ℝ) • (I • a) := by
    funext τ i j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im t]
    ring
  have hc : conj t = (t.re : ℂ) - t.im * I := by apply Complex.ext <;> simp
  rw [e, lamF_add, lamF_smul, lamF_smul, lamF_I, hc]
  ring

end GlobalTheory.FockTransl.Jet

end
