import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Model

open Matrix
open scoped ComplexOrder

/- English proof (translation)
Simplify using `[gramOf]`.
-/
theorem gramOf_one {N : ℕ} (hd : Fin N → ℝ) : gramOf hd 1 = diagonal (fun i => (hd i : ℂ)) := by
  simp [gramOf]

/- English proof (translation)
Use `⟨by simp, ?_⟩` and prove the remaining obligations. Establish `: -gramHead (sigForm N j) (N - j) (1 : Matrix (Fin N) (Fin N) ℂ) = 1`. Use extensionality with `a b`. Simplify using `only [gramHead, gramOf_one, Matrix.neg_apply, submatrix_apply, diagonal_apply, Matrix.one_apply, sigForm]`. Distinguish the cases in `h : a = b`.

Substitute `h` using the available equality. Simplify using `[a.2]`. Establish `: a.1 ≠ b.1` using `fun e => h (Subtype.ext e)`. Simplify using `[h, this]`. Rewrite using `[this]`.

Conclude with `PosDef.one`.
-/
theorem inFlagDomain_one' (N j : ℕ) : InFlagDomain N j 1 := by
  refine ⟨by simp, ?_⟩
  have : -gramHead (sigForm N j) (N - j) (1 : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    ext a b
    simp only [gramHead, gramOf_one, Matrix.neg_apply, submatrix_apply, diagonal_apply, Matrix.one_apply, sigForm]
    by_cases h : a = b
    · subst h; simp [a.2]
    · have : a.1 ≠ b.1 := fun e => h (Subtype.ext e)
      simp [h, this]
  rw [this]; exact PosDef.one

instance uniq1 : Unique {a : Fin 2 // (a : ℕ) < 1} where
  default := ⟨0, by simp⟩
  uniq := by rintro ⟨a, ha⟩; apply Subtype.ext; apply Fin.ext; simp only [Fin.val_zero]; omega

def eqv2 : {a : Fin 2 // (a : ℕ) < 2} ≃ Fin 2 := Equiv.subtypeUnivEquiv (fun a => a.2)

/- English proof (translation)
Rewrite using `[det_unique]`. Both sides reduce to the same expression.
-/
theorem det_head_one (hd : Fin 2 → ℝ) (g : Matrix (Fin 2) (Fin 2) ℂ) :
    (gramHead hd 1 g).det = gramOf hd g 0 0 := by
  rw [det_unique]; rfl

/- English proof (translation)
Rewrite using `[← det_submatrix_equiv_self eqv2 (gramOf hd g)]`. Both sides reduce to the same expression.
-/
theorem det_head_two (hd : Fin 2 → ℝ) (g : Matrix (Fin 2) (Fin 2) ℂ) :
    (gramHead hd 2 g).det = (gramOf hd g).det := by
  rw [← det_submatrix_equiv_self eqv2 (gramOf hd g)]; rfl

/- English proof (translation)
Use `haveI : IsEmpty {a : Fin N // (a : ℕ) < 0} := ⟨fun a => by have := a.2; omega⟩`. Conclude with `det_isEmpty`.
-/
theorem det_head_zero {N : ℕ} (hd : Fin N → ℝ) (g : Matrix (Fin N) (Fin N) ℂ) :
    (gramHead hd 0 g).det = 1 := by
  haveI : IsEmpty {a : Fin N // (a : ℕ) < 0} := ⟨fun a => by have := a.2; omega⟩
  exact det_isEmpty

/- English proof (translation)
Simplify using `[gramOf, sigForm, Matrix.mul_apply, Fin.sum_univ_two, diagonal_apply, Complex.conj_mul']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gram_signature_two_one_entry_zero_zero (z : ℂ) : gramOf (sigForm 2 1) !![1, 0; z, 1] 0 0 = -((1 - ‖z‖ ^ 2 : ℝ) : ℂ) := by
  simp [gramOf, sigForm, Matrix.mul_apply, Fin.sum_univ_two, diagonal_apply, Complex.conj_mul']
  ring

/- English proof (translation)
Simplify using `[gramOf, sigForm, det_conjTranspose, det_fin_two_of, Fin.prod_univ_two]`.
-/
theorem gram_signature_two_one_det (z : ℂ) : (gramOf (sigForm 2 1) !![1, 0; z, 1]).det = -1 := by
  simp [gramOf, sigForm, det_conjTranspose, det_fin_two_of, Fin.prod_univ_two]

/- English proof (translation)
Establish `h : -gramHead (sigForm 2 1) (2 - 1) !![1, 0; z, 1] = diagonal (fun _ : {a : Fin 2 // (a : ℕ) < 1} => ((1 - ‖z‖ ^ 2 : ℝ) : ℂ))`. Use extensionality with `a b`. Establish `ha : a = default` using `Subsingleton.elim (α := {a : Fin 2 // (a : ℕ) < 1}) _ _`. Establish `hb : b = default` using `Subsingleton.elim (α := {a : Fin 2 // (a : ℕ) < 1}) _ _`. Substitute `ha` using the available equality.

Rewrite using `[hb]`. Rewrite using `[diagonal_apply_eq, Matrix.neg_apply]`. Express the relevant statement in the definitionally equal form `-(gramOf (sigForm 2 1) !![1, 0; z, 1] 0 0) = _`. Rewrite using `[gram_signature_two_one_entry_zero_zero, neg_neg]`. Unfold `InFlagDomain`.

Rewrite using `[h, posDef_diagonal_iff]`. Establish `hu : IsUnit (!![1, 0; z, 1] : Matrix (Fin 2) (Fin 2) ℂ).det` using `by simp [det_fin_two_of]`. Simplify using `only [hu, true_and, Complex.zero_lt_real, forall_const]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Use polynomial arithmetic with `[norm_nonneg z]`. Introduce `h`. Use polynomial arithmetic with `[norm_nonneg z]`.
-/
theorem inFlagDomain_disc (z : ℂ) : InFlagDomain 2 1 !![1, 0; z, 1] ↔ ‖z‖ < 1 := by
  have h : -gramHead (sigForm 2 1) (2 - 1) !![1, 0; z, 1]
      = diagonal (fun _ : {a : Fin 2 // (a : ℕ) < 1} => ((1 - ‖z‖ ^ 2 : ℝ) : ℂ)) := by
    ext a b
    have ha : a = default := Subsingleton.elim (α := {a : Fin 2 // (a : ℕ) < 1}) _ _
    have hb : b = default := Subsingleton.elim (α := {a : Fin 2 // (a : ℕ) < 1}) _ _
    subst ha; rw [hb]
    rw [diagonal_apply_eq, Matrix.neg_apply]
    change -(gramOf (sigForm 2 1) !![1, 0; z, 1] 0 0) = _
    rw [gram_signature_two_one_entry_zero_zero, neg_neg]
  unfold InFlagDomain
  rw [h, posDef_diagonal_iff]
  have hu : IsUnit (!![1, 0; z, 1] : Matrix (Fin 2) (Fin 2) ℂ).det := by simp [det_fin_two_of]
  simp only [hu, true_and, Complex.zero_lt_real, forall_const]
  constructor
  · intro h; nlinarith [norm_nonneg z]
  · intro h; nlinarith [norm_nonneg z]

/- English proof (translation)
Establish `hp : 0 ≤ 1 - ‖z‖ ^ 2` using `by nlinarith [norm_nonneg z]`. Establish `: stepPot 2 1 0 !![1, 0; z, 1] = gramLog (sigForm 2 1) 2 !![1, 0; z, 1] - gramLog (sigForm 2 1) 1 !![1, 0; z, 1]`. Simplify using `[stepPot]`. Rewrite using `[this, gramLog, gramLog, det_head_one, det_head_two, gram_signature_two_one_entry_zero_zero, gram_signature_two_one_det, norm_neg, norm_neg, Complex.norm_real, Real.norm_of_nonneg hp]`. Simplify using the standard rewrite rules.
-/
theorem stepPot_disc_zero (z : ℂ) (hz : ‖z‖ < 1) :
    stepPot 2 1 0 !![1, 0; z, 1] = -(1 / 2) * Real.log (1 - ‖z‖ ^ 2) := by
  have hp : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have : stepPot 2 1 0 !![1, 0; z, 1]
      = gramLog (sigForm 2 1) 2 !![1, 0; z, 1] - gramLog (sigForm 2 1) 1 !![1, 0; z, 1] := by
    simp [stepPot]
  rw [this, gramLog, gramLog, det_head_one, det_head_two, gram_signature_two_one_entry_zero_zero, gram_signature_two_one_det, norm_neg, norm_neg,
    Complex.norm_real, Real.norm_of_nonneg hp]
  simp

/- English proof (translation)
Establish `: stepPot 2 1 1 !![1, 0; z, 1] = gramLog (sigForm 2 1) 2 !![1, 0; z, 1]`. Simplify using `[stepPot]`. Rewrite using `[this, gramLog, det_head_two, gram_signature_two_one_det]`. Simplify using the standard rewrite rules.
-/
theorem stepPot_disc_one (z : ℂ) : stepPot 2 1 1 !![1, 0; z, 1] = 0 := by
  have : stepPot 2 1 1 !![1, 0; z, 1] = gramLog (sigForm 2 1) 2 !![1, 0; z, 1] := by
    simp [stepPot]
  rw [this, gramLog, det_head_two, gram_signature_two_one_det]
  simp

/- English proof (translation)
Establish `: stepPot 2 2 0 !![1, 0; z, 1] = gramLog (sigForm 2 2) 1 !![1, 0; z, 1] - gramLog (sigForm 2 2) 0 !![1, 0; z, 1]`. Simplify using `[stepPot]`. Establish `h : gramOf (sigForm 2 2) !![1, 0; z, 1] 0 0 = ((1 + ‖z‖ ^ 2 : ℝ) : ℂ)`. Simplify using `[gramOf, sigForm, Matrix.mul_apply, Fin.sum_univ_two, diagonal_apply, Complex.conj_mul']`. Rewrite using `[this, gramLog, gramLog, det_head_one, det_head_zero, h, Complex.norm_real, Real.norm_of_nonneg (by positivity)]`.

Simplify using the standard rewrite rules.
-/
theorem stepPot_pos_zero (z : ℂ) :
    stepPot 2 2 0 !![1, 0; z, 1] = (1 / 2) * Real.log (1 + ‖z‖ ^ 2) := by
  have : stepPot 2 2 0 !![1, 0; z, 1]
      = gramLog (sigForm 2 2) 1 !![1, 0; z, 1] - gramLog (sigForm 2 2) 0 !![1, 0; z, 1] := by
    simp [stepPot]
  have h : gramOf (sigForm 2 2) !![1, 0; z, 1] 0 0 = ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) := by
    simp [gramOf, sigForm, Matrix.mul_apply, Fin.sum_univ_two, diagonal_apply, Complex.conj_mul']
  rw [this, gramLog, gramLog, det_head_one, det_head_zero, h, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  simp

/- English proof (translation)
Establish `: stepPot 2 0 0 !![1, 0; z, 1] = gramLog (sigForm 2 0) 1 !![1, 0; z, 1]`. Simplify using `[stepPot]`. Establish `h : gramOf (sigForm 2 0) !![1, 0; z, 1] 0 0 = -((1 + ‖z‖ ^ 2 : ℝ) : ℂ)`. Simplify using `[gramOf, sigForm, Matrix.mul_apply, Fin.sum_univ_two, diagonal_apply, Complex.conj_mul']`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, gramLog, det_head_one, h, norm_neg, Complex.norm_real, Real.norm_of_nonneg (by positivity)]`.
-/
theorem stepPot_neg_zero (z : ℂ) :
    stepPot 2 0 0 !![1, 0; z, 1] = (1 / 2) * Real.log (1 + ‖z‖ ^ 2) := by
  have : stepPot 2 0 0 !![1, 0; z, 1] = gramLog (sigForm 2 0) 1 !![1, 0; z, 1] := by
    simp [stepPot]
  have h : gramOf (sigForm 2 0) !![1, 0; z, 1] 0 0 = -((1 + ‖z‖ ^ 2 : ℝ) : ℂ) := by
    simp [gramOf, sigForm, Matrix.mul_apply, Fin.sum_univ_two, diagonal_apply, Complex.conj_mul']
    ring
  rw [this, gramLog, det_head_one, h, norm_neg, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]

/- English proof (translation)
Simplify using `[herm2, dotProduct, mulVec, Fin.sum_univ_two]`.
-/
theorem hermitian_two_form_eq (G : Matrix (Fin 2) (Fin 2) ℂ) (a b : ℂ) :
    herm2 G ![1, a] ![1, b] = G 0 0 + G 0 1 * b + (starRingEnd ℂ a) * (G 1 0 + G 1 1 * b) := by
  simp [herm2, dotProduct, mulVec, Fin.sum_univ_two]

/- English proof (translation)
Establish `: herm2 1 ![1, a] ![1, a] = ((1 + ‖a‖ ^ 2 : ℝ) : ℂ)`. Rewrite using `[hermitian_two_form_eq]`. Simplify using `[Complex.conj_mul']`. Rewrite using `[xiPot, this, Complex.ofReal_re]`. Simplify using the standard rewrite rules.
-/
theorem xiPot_one (a : ℂ) : xiPot 1 a = -Real.log (1 + ‖a‖ ^ 2) := by
  have : herm2 1 ![1, a] ![1, a] = ((1 + ‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [hermitian_two_form_eq]; simp [Complex.conj_mul']
  rw [xiPot, this, Complex.ofReal_re]; simp

/- English proof (translation)
Use `hG.dotProduct_mulVec_pos (x := ![1, a]) (by intro h; simpa using congrFun h 0)` as an intermediate fact. Conclude with `(Complex.lt_def.mp this).1`.
-/
theorem hermitian_two_form_re_pos {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) (a : ℂ) :
    0 < (herm2 G ![1, a] ![1, a]).re := by
  have := hG.dotProduct_mulVec_pos (x := ![1, a]) (by intro h; simpa using congrFun h 0)
  exact (Complex.lt_def.mp this).1

/- English proof (translation)
Establish `ha` using `hermitian_two_form_re_pos hG a`. Establish `hb` using `hermitian_two_form_re_pos hG b`. Establish `hd : 0 < G.det.re` using `(Complex.lt_def.mp hG.det_pos).1`. Establish `h10 : G 1 0 = starRingEnd ℂ (G 0 1)` using `(hG.1.apply 1 0).symm`. Establish `h00 : (G 0 0).im = 0` using `Complex.conj_eq_iff_im.mp (hG.1.apply 0 0)`.

Establish `h11 : (G 1 1).im = 0` using `Complex.conj_eq_iff_im.mp (hG.1.apply 1 1)`. Establish `key : (herm2 G ![1, a] ![1, a]).re * (herm2 G ![1, b] ![1, b]).re - ‖herm2 G ![1, a] ![1, b]‖ ^ 2 = ‖a - b‖ ^ 2 * G.det.re`. Rewrite using `[Complex.sq_norm, Complex.sq_norm, det_fin_two]`. Simplify using `only [hermitian_two_form_eq, h10, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im, h00, h11]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hn : 0 < ‖a - b‖` using `norm_pos_iff.mpr (sub_ne_zero.mpr hab)`. Establish `e : 1 - ‖herm2 G ![1, a] ![1, b]‖ ^ 2 / ((herm2 G ![1, a] ![1, a]).re * (herm2 G ![1, b] ![1, b]).re) = ‖a - b‖ ^ 2 * G.det.re / ((herm2 G ![1, a] ![1, a]).re * (herm2 G ![1, b] ![1, b]).re)`. Rewrite using `[← key]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[logSin, e, Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) hd.ne', Real.log_mul ha.ne' hb.ne', Real.log_pow, xiPot, xiPot]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem logSin_eq {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) {a b : ℂ} (hab : a ≠ b) :
    logSin G a b = Real.log ‖a - b‖ + (xiPot G a + xiPot G b) / 2 := by
  have ha := hermitian_two_form_re_pos hG a
  have hb := hermitian_two_form_re_pos hG b
  have hd : 0 < G.det.re := (Complex.lt_def.mp hG.det_pos).1
  have h10 : G 1 0 = starRingEnd ℂ (G 0 1) := (hG.1.apply 1 0).symm
  have h00 : (G 0 0).im = 0 := Complex.conj_eq_iff_im.mp (hG.1.apply 0 0)
  have h11 : (G 1 1).im = 0 := Complex.conj_eq_iff_im.mp (hG.1.apply 1 1)
  have key : (herm2 G ![1, a] ![1, a]).re * (herm2 G ![1, b] ![1, b]).re - ‖herm2 G ![1, a] ![1, b]‖ ^ 2
      = ‖a - b‖ ^ 2 * G.det.re := by
    rw [Complex.sq_norm, Complex.sq_norm, det_fin_two]
    simp only [hermitian_two_form_eq, h10, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im, h00, h11]
    ring
  have hn : 0 < ‖a - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  have e : 1 - ‖herm2 G ![1, a] ![1, b]‖ ^ 2 /
      ((herm2 G ![1, a] ![1, a]).re * (herm2 G ![1, b] ![1, b]).re)
      = ‖a - b‖ ^ 2 * G.det.re / ((herm2 G ![1, a] ![1, a]).re * (herm2 G ![1, b] ![1, b]).re) := by
    rw [← key]; field_simp
  rw [logSin, e, Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) hd.ne',
    Real.log_mul ha.ne' hb.ne', Real.log_pow, xiPot, xiPot]
  push_cast; ring

/- English proof (translation)
Set `e : {a : Fin N // (a : ℕ) < k} → {a : Fin N // (a : ℕ) < N - j}` to `fun a => ⟨a.1, lt_of_lt_of_le a.2 hk⟩`. Establish `he : Function.Injective e` using `fun a b h => Subtype.ext (congrArg Subtype.val h : (e a).1 = (e b).1)`. Establish `h1 : (-gramHead (sigForm N j) k g).PosDef`. Establish `h0 : -gramHead (sigForm N j) k g = (-gramHead (sigForm N j) (N - j) g).submatrix e e`. Use extensionality with `a b`.

Simplify using `only [gramHead, Matrix.neg_apply, submatrix_apply, e]`. Rewrite using `[h0]`. Conclude with `Matrix.PosDef.submatrix hg.2 he`. Establish `h2` using `h1.det_pos.ne'`. Rewrite `h2` using `[det_neg]`.

Conclude with `right_ne_zero_of_mul h2`.
-/
theorem det_gramHead_ne_zero {N j k : ℕ} {g : Matrix (Fin N) (Fin N) ℂ} (hg : InFlagDomain N j g)
    (hk : k ≤ N - j) : (gramHead (sigForm N j) k g).det ≠ 0 := by
  let e : {a : Fin N // (a : ℕ) < k} → {a : Fin N // (a : ℕ) < N - j} := fun a => ⟨a.1, lt_of_lt_of_le a.2 hk⟩
  have he : Function.Injective e := fun a b h => Subtype.ext (congrArg Subtype.val h : (e a).1 = (e b).1)
  have h1 : (-gramHead (sigForm N j) k g).PosDef := by
    have h0 : -gramHead (sigForm N j) k g = (-gramHead (sigForm N j) (N - j) g).submatrix e e := by
      ext a b; simp only [gramHead, Matrix.neg_apply, submatrix_apply, e]
    rw [h0]; exact Matrix.PosDef.submatrix hg.2 he
  have h2 := h1.det_pos.ne'
  rw [det_neg] at h2
  exact right_ne_zero_of_mul h2

/- English proof (translation)
Establish `h : (gramHead (sigForm N j) N g).det = (gramOf (sigForm N j) g).det`. Rewrite using `[← det_submatrix_equiv_self (Equiv.subtypeUnivEquiv (p := fun a : Fin N => (a : ℕ) < N) (fun a => a.2)) (gramOf (sigForm N j) g)]`. Both sides reduce to the same expression. Establish `h2 : ‖∏ i : Fin N, ((sigForm N j i : ℝ) : ℂ)‖ = 1`. Rewrite using `[norm_prod]`.

Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `unfold sigForm; split_ifs <;> simp`. Rewrite using `[gramLog, h, gramOf, det_mul, det_mul, det_diagonal, det_conjTranspose, norm_mul, norm_mul, h2, norm_star, mul_one, ← sq, Real.log_pow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gramLog_top (N j : ℕ) (g : Matrix (Fin N) (Fin N) ℂ) :
    gramLog (sigForm N j) N g = Real.log ‖g.det‖ := by
  have h : (gramHead (sigForm N j) N g).det = (gramOf (sigForm N j) g).det := by
    rw [← det_submatrix_equiv_self (Equiv.subtypeUnivEquiv (p := fun a : Fin N => (a : ℕ) < N) (fun a => a.2))
      (gramOf (sigForm N j) g)]; rfl
  have h2 : ‖∏ i : Fin N, ((sigForm N j i : ℝ) : ℂ)‖ = 1 := by
    rw [norm_prod]
    refine Finset.prod_eq_one fun i _ => ?_
    unfold sigForm; split_ifs <;> simp
  rw [gramLog, h, gramOf, det_mul, det_mul, det_diagonal, det_conjTranspose, norm_mul, norm_mul, h2, norm_star,
    mul_one, ← sq, Real.log_pow]
  push_cast; ring

end GlobalTheory.CompanionTheory.Ar.PB.Model
