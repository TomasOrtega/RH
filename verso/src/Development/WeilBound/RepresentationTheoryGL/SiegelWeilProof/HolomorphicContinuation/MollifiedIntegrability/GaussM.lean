import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GaussS

noncomputable section

open MeasureTheory Matrix MvPolynomial
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.WR.G

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

namespace GM

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `apply Complex.ext <;> simp [herm] <;> ring`.
-/
theorem herm_isHermitian (y : E n) : (herm y).IsHermitian := by
  ext i j
  apply Complex.ext <;> simp [herm] <;> ring

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [gramX, Qp, Qb, evX, conjTranspose_apply, map_sub, map_sum, map_mul, eval_X, star_sub, star_sum, star_mul', star_star]`. Simplify using `only [if_true, Bool.false_eq_true, if_false]`. Apply the tactic sequence `congr 1 <;> (refine Finset.sum_congr rfl fun a _ => ?_; rw [star_star, mul_comm])`.
-/
theorem gramX_isHermitian (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) : (gramX ε x).IsHermitian := by
  ext i j
  simp only [gramX, Qp, Qb, evX, conjTranspose_apply, map_sub, map_sum, map_mul, eval_X, star_sub, star_sum,
    star_mul', star_star]
  simp only [if_true, Bool.false_eq_true, if_false]
  congr 1 <;> (refine Finset.sum_congr rfl fun a _ => ?_; rw [star_star, mul_comm])

/- English proof (translation)
Establish `h : star (b * Q).trace = (b * Q).trace`. Rewrite using `[← Matrix.trace_conjTranspose, conjTranspose_mul, hb.eq, hQ.eq, Matrix.trace_mul_comm]`. Use `congrArg Complex.im h` as an intermediate fact. Simplify using `only [Complex.star_def, Complex.conj_im] at this`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem trace_im_zero {b Q : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) (hQ : Q.IsHermitian) :
    (b * Q).trace.im = 0 := by
  have h : star (b * Q).trace = (b * Q).trace := by
    rw [← Matrix.trace_conjTranspose, conjTranspose_mul, hb.eq, hQ.eq, Matrix.trace_mul_comm]
  have := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at this
  linarith

/- English proof (translation)
Rewrite using `[Complex.norm_exp]`. Establish `h0` using `trace_im_zero hb (gramX_isHermitian ε x)`. Establish `: (Complex.I * t * (b * gramX ε x).trace).re = 0`. Simplify using `[Complex.mul_re, h0]`. Rewrite using `[this, Real.exp_zero]`.
-/
theorem norm_phase {ε : Fin m → Bool} {t : ℝ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian)
    (x : Fin m → Fin n → ℂ) : ‖Complex.exp (Complex.I * t * (b * gramX ε x).trace)‖ = 1 := by
  rw [Complex.norm_exp]
  have h0 := trace_im_zero hb (gramX_isHermitian ε x)
  have : (Complex.I * t * (b * gramX ε x).trace).re = 0 := by
    simp [Complex.mul_re, h0]
  rw [this, Real.exp_zero]

/- English proof (translation)
Unfold `evX`. Use `(MvPolynomial.continuous_eval P).comp (continuous_pi fun k => ?_)` and prove the remaining obligations. Use `split_ifs`. Conclude with `continuous_star.comp ((continuous_apply _).comp (continuous_apply _))`. Conclude with `(continuous_apply _).comp (continuous_apply _)`.
-/
theorem continuous_evX (P : PX m n) : Continuous fun x : Fin m → Fin n → ℂ => evX P x := by
  unfold evX
  refine (MvPolynomial.continuous_eval P).comp (continuous_pi fun k => ?_)
  split_ifs
  · exact continuous_star.comp ((continuous_apply _).comp (continuous_apply _))
  · exact (continuous_apply _).comp (continuous_apply _)

/- English proof (translation)
Use `(hI m n c hc P).mono ?_ (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Use `(hI m n c hc P).aestronglyMeasurable.mul (Continuous.aestronglyMeasurable ?_)` and prove the remaining obligations. Use `Complex.continuous_exp.comp (continuous_const.mul ?_)` and prove the remaining obligations. Use `(continuous_const.matrix_mul ?_).matrix_trace` and prove the remaining obligations. Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations.

Conclude with `continuous_evX _`. Rewrite using `[norm_mul, norm_phase hb, mul_one]`.
-/
theorem integ_sec (hI : IntegP) {ε : Fin m → Bool} {c t : ℝ} (hc : 0 < c) {b : Matrix (Fin n) (Fin n) ℂ}
    (hb : b.IsHermitian) (P : PX m n) :
    Integrable fun x => evX P x * gs c x * Complex.exp (Complex.I * t * (b * gramX ε x).trace) := by
  refine (hI m n c hc P).mono ?_ (Filter.Eventually.of_forall fun x => ?_)
  · refine (hI m n c hc P).aestronglyMeasurable.mul (Continuous.aestronglyMeasurable ?_)
    refine Complex.continuous_exp.comp (continuous_const.mul ?_)
    refine (continuous_const.matrix_mul ?_).matrix_trace
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact continuous_evX _
  · rw [norm_mul, norm_phase hb, mul_one]

/- English proof (translation)
Unfold `secN`. Rewrite using `[← integral_add (integ_sec hI hc hb P) (integ_sec hI hc hb Q)]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `[evX]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem sec_add (hI : IntegP) {ε : Fin m → Bool} {c t : ℝ} (hc : 0 < c) {b : Matrix (Fin n) (Fin n) ℂ}
    (hb : b.IsHermitian) (P Q : PX m n) : secN ε c t (P + Q) b = secN ε c t P b + secN ε c t Q b := by
  unfold secN
  rw [← integral_add (integ_sec hI hc hb P) (integ_sec hI hc hb Q)]
  congr 1; funext x; simp [evX]; ring

/- English proof (translation)
Unfold `secN`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `[evX, smul_eq_C_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem sec_smul {ε : Fin m → Bool} {c t : ℝ} {b : Matrix (Fin n) (Fin n) ℂ} (r : ℂ) (P : PX m n) :
    secN ε c t (r • P) b = r * secN ε c t P b := by
  unfold secN
  rw [← integral_const_mul]
  congr 1; funext x; simp [evX, smul_eq_C_mul]; ring

/- English proof (translation)
Simplify using `[secN, evX]`.
-/
theorem sec_zero {ε : Fin m → Bool} {c t : ℝ} {b : Matrix (Fin n) (Fin n) ℂ} : secN ε c t (0 : PX m n) b = 0 := by
  simp [secN, evX]

/- English proof (translation)
Establish `h1 : star (star v ⬝ᵥ (b *ᵥ v)) = star (b *ᵥ v) ⬝ᵥ v`. Simplify using `only [dotProduct, star_sum, star_mul', star_star, Pi.star_apply]`. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`. Establish `h2 : star (b *ᵥ v) = star v ᵥ* b` using `by rw [star_mulVec, hb.eq]`. Rewrite using `[h1, h2, dotProduct_mulVec]`.
-/
theorem star_dot_herm {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) (v : Fin n → ℂ) :
    star (star v ⬝ᵥ (b *ᵥ v)) = star v ⬝ᵥ (b *ᵥ v) := by
  have h1 : star (star v ⬝ᵥ (b *ᵥ v)) = star (b *ᵥ v) ⬝ᵥ v := by
    simp only [dotProduct, star_sum, star_mul', star_star, Pi.star_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h2 : star (b *ᵥ v) = star v ᵥ* b := by rw [star_mulVec, hb.eq]
  rw [h1, h2, dotProduct_mulVec]

/- English proof (translation)
Introduce `h`. Take `⟨v, hv, hMv⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr h`. Establish `e1 : v = (Complex.I * r) • (b *ᵥ v)`. Rewrite `hMv` using `[sub_mulVec, one_mulVec, smul_mulVec]`. Conclude with `sub_eq_zero.mp hMv`.

Establish `e2 : star v ⬝ᵥ v = (Complex.I * r) * (star v ⬝ᵥ (b *ᵥ v))`. Combine the equalities or inequalities in the displayed calculation. Establish `hq : (star v ⬝ᵥ (b *ᵥ v)).im = 0`. Use `congrArg Complex.im (star_dot_herm hb v)` as an intermediate fact. Simplify using `only [Complex.star_def, Complex.conj_im] at this`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hs : (star v ⬝ᵥ v).im = 0`. Establish `: star (star v ⬝ᵥ v) = star v ⬝ᵥ v`. Simplify using `only [dotProduct, star_sum, star_mul', star_star, Pi.star_apply]`. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`.

Use `congrArg Complex.im this` as an intermediate fact. Simplify using `only [Complex.star_def, Complex.conj_im] at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hr : (star v ⬝ᵥ v).re = 0`. Rewrite using `[e2]`.

Simplify using `[Complex.mul_re, hq]`. Conclude with `hv (dotProduct_star_self_eq_zero.mp (Complex.ext (by simpa using hr) (by simpa using hs)))`.
-/
theorem det_ne_zero {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) (r : ℝ) :
    (1 - (Complex.I * r) • b).det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have e1 : v = (Complex.I * r) • (b *ᵥ v) := by
    rw [sub_mulVec, one_mulVec, smul_mulVec] at hMv
    exact sub_eq_zero.mp hMv
  have e2 : star v ⬝ᵥ v = (Complex.I * r) * (star v ⬝ᵥ (b *ᵥ v)) := by
    calc star v ⬝ᵥ v = star v ⬝ᵥ ((Complex.I * r) • (b *ᵥ v)) := by rw [← e1]
      _ = _ := by rw [dotProduct_smul, smul_eq_mul]
  have hq : (star v ⬝ᵥ (b *ᵥ v)).im = 0 := by
    have := congrArg Complex.im (star_dot_herm hb v)
    simp only [Complex.star_def, Complex.conj_im] at this
    linarith
  have hs : (star v ⬝ᵥ v).im = 0 := by
    have : star (star v ⬝ᵥ v) = star v ⬝ᵥ v := by
      simp only [dotProduct, star_sum, star_mul', star_star, Pi.star_apply]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have := congrArg Complex.im this
    simp only [Complex.star_def, Complex.conj_im] at this
    linarith
  have hr : (star v ⬝ᵥ v).re = 0 := by
    rw [e2]; simp [Complex.mul_re, hq]
  exact hv (dotProduct_star_self_eq_zero.mp (Complex.ext (by simpa using hr) (by simpa using hs)))

def sR (ε : Fin m → Bool) (a : Fin m) : ℝ := if ε a then 1 else -1

/- English proof (translation)
Apply the tactic sequence `unfold sgn sR; split_ifs <;> simp`.
-/
theorem sgn_eq (ε : Fin m → Bool) (a : Fin m) : sgn ε a = ((sR ε a : ℝ) : ℂ) := by
  unfold sgn sR; split_ifs <;> simp

def Mm (ε : Fin m → Bool) (s : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (a : Fin m) : Matrix (Fin n) (Fin n) ℂ :=
  1 - (Complex.I * ((s * sR ε a : ℝ) : ℂ)) • b

/- English proof (translation)
Unfold `Amat Mm`. Rewrite using `[transpose_sub, transpose_one, transpose_smul, smul_sub, smul_smul, sgn_eq]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem amat_eq (ε : Fin m → Bool) (c s : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (a : Fin m) :
    Amat ε c (s * c) b a = (c : ℂ) • (Mm ε s b a)ᵀ := by
  unfold Amat Mm
  rw [transpose_sub, transpose_one, transpose_smul, smul_sub, smul_smul, sgn_eq]
  congr 2
  push_cast; ring

/- English proof (translation)
Establish `hM : IsUnit (Mm ε s b a).det` using `isUnit_iff_ne_zero.mpr (det_ne_zero hb _)`. Establish `hinv : (Amat ε c (s * c) b a)⁻¹ = (c : ℂ)⁻¹ • ((Mm ε s b a)⁻¹)ᵀ`. Rewrite using `[amat_eq]`. Use `Matrix.inv_eq_left_inv ?_` and prove the remaining obligations. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hc), one_smul, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hM, transpose_one]`.

Rewrite using `[hinv]`. Simplify using the standard rewrite rules.
-/
theorem amat_inv_apply (ε : Fin m → Bool) {c : ℝ} (hc : c ≠ 0) (s : ℝ) {b : Matrix (Fin n) (Fin n) ℂ}
    (hb : b.IsHermitian) (a : Fin m) (i j : Fin n) :
    (Amat ε c (s * c) b a)⁻¹ j i = (c : ℂ)⁻¹ * ((Mm ε s b a)⁻¹) i j := by
  have hM : IsUnit (Mm ε s b a).det := isUnit_iff_ne_zero.mpr (det_ne_zero hb _)
  have hinv : (Amat ε c (s * c) b a)⁻¹ = (c : ℂ)⁻¹ • ((Mm ε s b a)⁻¹)ᵀ := by
    rw [amat_eq]
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hc), one_smul,
      ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hM, transpose_one]
  rw [hinv]; simp

/- English proof (translation)
Establish `hM` using `det_ne_zero hb (s * sR ε a)`. Rewrite using `[amat_eq, det_smul, det_transpose, Matrix.det_nonsing_inv, Fintype.card_fin, Ring.inverse_eq_inv']`. Establish `hc' : (c : ℂ) ≠ 0` using `by exact_mod_cast hc`. Unfold `Mm at hM ⊢`. Rewrite using `[div_pow]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem amat_det (ε : Fin m → Bool) {c : ℝ} (hc : c ≠ 0) (s : ℝ) {b : Matrix (Fin n) (Fin n) ℂ}
    (hb : b.IsHermitian) (a : Fin m) :
    (Real.pi : ℂ) ^ n / (Amat ε c (s * c) b a).det = ((Real.pi : ℂ) / c) ^ n * ((Mm ε s b a)⁻¹).det := by
  have hM := det_ne_zero hb (s * sR ε a)
  rw [amat_eq, det_smul, det_transpose, Matrix.det_nonsing_inv, Fintype.card_fin, Ring.inverse_eq_inv']
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  unfold Mm at hM ⊢
  rw [div_pow]
  field_simp

end GM

/- English proof (translation)
Unfold `GM.Mm GM.sR uM vM`. Use `split_ifs with h`. Use `push_cast`. Rewrite using `[mul_one]`. Use `push_cast`.

Use `congr 1`. Rewrite using `[show Complex.I * ((s : ℂ) * -1) = -(Complex.I * s) by ring, neg_smul, sub_neg_eq_add]`.
-/
theorem mm_inv (ε : Fin m → Bool) (s : ℝ) (y : E n) (a : Fin m) :
    (GM.Mm ε s (herm y) a)⁻¹ = if ε a then uM (s : ℂ) y else vM (s : ℂ) y := by
  unfold GM.Mm GM.sR uM vM
  split_ifs with h
  · push_cast; rw [mul_one]
  · push_cast
    congr 1
    rw [show Complex.I * ((s : ℂ) * -1) = -(Complex.I * s) by ring, neg_smul, sub_neg_eq_add]

open GM in
/- English proof (translation)
Set `S : Submodule ℂ (PX m n)` to `{ carrier := {P | ∃ R : MvPolynomial (Bool × Fin n × Fin n) ℂ, ∀ y : E n, secN ε c (s * c) P (herm y) = secN ε c (s * c) 1 (herm y) * evUV (s : ℂ) R y} add_mem' := by`. Introduce and unpack `P Q ⟨R1, h1⟩ ⟨R2, h2⟩`. Use `⟨R1 + R2, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[sec_add hI hc (herm_isHermitian y), h1, h2]`. Simplify using `[evUV, map_add]`.

Expand and normalize the polynomial expressions, which then agree. Use the proof step `zero_mem' := ⟨0, fun y => by simp [sec_zero, evUV]⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `r P ⟨R1, h1⟩`. Use `⟨MvPolynomial.C r * R1, fun y => ?_⟩` and prove the remaining obligations.

Rewrite using `[sec_smul, h1]`. Simplify using `[evUV]`. Use `ring }`. Establish `hmono : ∀ N : ℕ, ∀ d : (Fin m × Fin n × Bool) →₀ ℕ, d.sum (fun _ e => e) = N → monomial d (1 : ℂ) ∈ S`. Introduce `N`.

Proceed by induction on `N using Nat.strong_induction_on with`. Consider the case `_ N ih`. Introduce `d hd`. Distinguish the cases in `ht : ∃ k : Fin m × Fin n × Bool, k.2.2 = true ∧ d k ≠ 0`. Take `⟨⟨a, i, bb⟩, hk, hdk⟩` from `ht`.

Simplify using `only at hk`. Substitute `hk` using the available equality. Use `set k : Fin m × Fin n × Bool := (a, i, true) with hkdef`. Use `set d' := d - Finsupp.single k 1 with hd'`. Establish `hdd : d = Finsupp.single k 1 + d'`.

Rewrite using `[hd', add_comm, tsub_add_cancel_of_le]`. Introduce `j`. Distinguish the cases in `hj : j = k`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. Simplify using `[Finsupp.single_apply, Ne.symm hj]`. Establish `hsum' : d'.sum (fun _ e => e) + 1 = N`. Rewrite using `[← hd, hdd, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]`. Simplify using `[Finsupp.sum_single_index]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hmul : monomial d (1 : ℂ) = X k * monomial d' 1`. Rewrite using `[hdd, X, monomial_mul, one_mul]`. Establish `hder : ∀ j : Fin n, pderiv ((a, j, false) : Fin m × Fin n × Bool) (monomial d' (1 : ℂ)) ∈ S`. Introduce `j`.

Rewrite using `[pderiv_monomial]`. Distinguish the cases in `h0 : d' (a, j, false) = 0`. Rewrite using `[h0]`. Simplify using the standard rewrite rules. Rewrite using `[show (monomial (d' - Finsupp.single (a, j, false) 1)) ((1 : ℂ) * ↑(d' (a, j, false))) = ((d' (a, j, false) : ℂ)) • monomial (d' - Finsupp.single (a, j, false) 1) (1 : ℂ) by`.

Rewrite using `[smul_monomial, smul_eq_mul, one_mul, mul_one]]`. Use `S.smul_mem _ (ih _ ?_ _ rfl)` and prove the remaining obligations. Establish `hle : Finsupp.single ((a, j, false) : Fin m × Fin n × Bool) 1 ≤ d'`. Introduce `l`. Distinguish the cases in `hl : l = (a, j, false)`.

Substitute `hl` using the available equality. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Simplify using `[Finsupp.single_apply, Ne.symm hl]`. Establish `e2 : d' = Finsupp.single ((a, j, false) : Fin m × Fin n × Bool) 1 + (d' - Finsupp.single (a, j, false) 1)` using `by rw [add_comm, tsub_add_cancel_of_le hle]`.

Establish `: (d' - Finsupp.single (a, j, false) 1).sum (fun _ e => e) + 1 = d'.sum (fun _ e => e)` using `by conv_rhs => rw [e2]`. Rewrite using `[Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]`. Simplify using `[Finsupp.sum_single_index]`. Expand and normalize the polynomial expressions, which then agree. Use linear arithmetic over natural numbers and integers.

Use `choose R hR using hder`. Use `⟨∑ j, MvPolynomial.C ((c : ℂ)⁻¹) * MvPolynomial.X (if ε a then ((false, i, j) : Bool × Fin n × Fin n) else (true, i, j)) * R j, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[hmul, hW m n ε c (s * c) hc _ (herm_isHermitian y)]`. Repeatedly rewrite using `[hR]`. Simplify using `only [evUV, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[amat_inv_apply ε hc.ne' s (herm_isHermitian y), mm_inv]`. Apply the tactic sequence `by_cases h : ε a = true <;> simp [h] <;> ring`. Use `push_neg at ht`. Distinguish the cases in `hd0 : d = 0`.

Substitute `hd0` using the available equality. Conclude with `⟨1, fun y => by simp [evUV]⟩`. Use `⟨0, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[hR m n ε c (s * c) hc _ (herm_isHermitian y) d (fun k hk => ht k hk) hd0]`. Simplify using `[evUV]`.

Introduce `P`. Establish `hP : P ∈ S`. Rewrite using `[P.as_sum]`. Use `Submodule.sum_mem _ fun d _ => ?_` and prove the remaining obligations. Rewrite using `[show monomial d (P.coeff d) = P.coeff d • monomial d (1 : ℂ) by rw [smul_monomial, smul_eq_mul, mul_one]]`.

Conclude with `S.smul_mem _ (hmono _ d rfl)`. Conclude with `hP`.
-/
theorem key (hI : IntegP) (hW : Wick) (hR : Rot) (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) (s : ℝ) :
    ∀ P : PX m n, ∃ R : MvPolynomial (Bool × Fin n × Fin n) ℂ, ∀ y : E n,
      secN ε c (s * c) P (herm y) = secN ε c (s * c) 1 (herm y) * evUV (s : ℂ) R y := by

  let S : Submodule ℂ (PX m n) :=
    { carrier := {P | ∃ R : MvPolynomial (Bool × Fin n × Fin n) ℂ, ∀ y : E n,
        secN ε c (s * c) P (herm y) = secN ε c (s * c) 1 (herm y) * evUV (s : ℂ) R y}
      add_mem' := by
        rintro P Q ⟨R1, h1⟩ ⟨R2, h2⟩
        refine ⟨R1 + R2, fun y => ?_⟩
        rw [sec_add hI hc (herm_isHermitian y), h1, h2]
        simp [evUV, map_add]; ring
      zero_mem' := ⟨0, fun y => by simp [sec_zero, evUV]⟩
      smul_mem' := by
        rintro r P ⟨R1, h1⟩
        refine ⟨MvPolynomial.C r * R1, fun y => ?_⟩
        rw [sec_smul, h1]
        simp [evUV]; ring }
  have hmono : ∀ N : ℕ, ∀ d : (Fin m × Fin n × Bool) →₀ ℕ, d.sum (fun _ e => e) = N → monomial d (1 : ℂ) ∈ S := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro d hd
      by_cases ht : ∃ k : Fin m × Fin n × Bool, k.2.2 = true ∧ d k ≠ 0
      · obtain ⟨⟨a, i, bb⟩, hk, hdk⟩ := ht
        simp only at hk
        subst hk
        set k : Fin m × Fin n × Bool := (a, i, true) with hkdef
        set d' := d - Finsupp.single k 1 with hd'
        have hdd : d = Finsupp.single k 1 + d' := by
          rw [hd', add_comm, tsub_add_cancel_of_le]
          intro j
          by_cases hj : j = k
          · subst hj; simp; omega
          · simp [Finsupp.single_apply, Ne.symm hj]
        have hsum' : d'.sum (fun _ e => e) + 1 = N := by
          rw [← hd, hdd, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
          simp [Finsupp.sum_single_index]; ring
        have hmul : monomial d (1 : ℂ) = X k * monomial d' 1 := by
          rw [hdd, X, monomial_mul, one_mul]

        have hder : ∀ j : Fin n, pderiv ((a, j, false) : Fin m × Fin n × Bool) (monomial d' (1 : ℂ)) ∈ S := by
          intro j
          rw [pderiv_monomial]
          by_cases h0 : d' (a, j, false) = 0
          · rw [h0]; simp
          · rw [show (monomial (d' - Finsupp.single (a, j, false) 1)) ((1 : ℂ) * ↑(d' (a, j, false))) =
                ((d' (a, j, false) : ℂ)) • monomial (d' - Finsupp.single (a, j, false) 1) (1 : ℂ) by
                rw [smul_monomial, smul_eq_mul, one_mul, mul_one]]
            refine S.smul_mem _ (ih _ ?_ _ rfl)
            have hle : Finsupp.single ((a, j, false) : Fin m × Fin n × Bool) 1 ≤ d' := by
              intro l; by_cases hl : l = (a, j, false)
              · subst hl; simp; omega
              · simp [Finsupp.single_apply, Ne.symm hl]
            have e2 : d' = Finsupp.single ((a, j, false) : Fin m × Fin n × Bool) 1 +
                (d' - Finsupp.single (a, j, false) 1) := by rw [add_comm, tsub_add_cancel_of_le hle]
            have : (d' - Finsupp.single (a, j, false) 1).sum (fun _ e => e) + 1 = d'.sum (fun _ e => e) := by
              conv_rhs => rw [e2]
              rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
              simp [Finsupp.sum_single_index]; ring
            omega
        choose R hR using hder
        refine ⟨∑ j, MvPolynomial.C ((c : ℂ)⁻¹) *
          MvPolynomial.X (if ε a then ((false, i, j) : Bool × Fin n × Fin n) else (true, i, j)) * R j, fun y => ?_⟩
        rw [hmul, hW m n ε c (s * c) hc _ (herm_isHermitian y)]
        simp_rw [hR]
        simp only [evUV, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [amat_inv_apply ε hc.ne' s (herm_isHermitian y), mm_inv]
        by_cases h : ε a = true <;> simp [h] <;> ring
      · push_neg at ht
        by_cases hd0 : d = 0
        · subst hd0
          exact ⟨1, fun y => by simp [evUV]⟩
        · refine ⟨0, fun y => ?_⟩
          rw [hR m n ε c (s * c) hc _ (herm_isHermitian y) d (fun k hk => ht k hk) hd0]
          simp [evUV]
  intro P
  have hP : P ∈ S := by
    rw [P.as_sum]
    refine Submodule.sum_mem _ fun d _ => ?_
    rw [show monomial d (P.coeff d) = P.coeff d • monomial d (1 : ℂ) by rw [smul_monomial, smul_eq_mul, mul_one]]
    exact S.smul_mem _ (hmono _ d rfl)
  exact hP

/- English proof (translation)
Introduce `m n ε c t hc _ P`. Establish `e : (t / c) * c = t` using `by field_simp`. Take `⟨R, hR⟩` from `key hI hW hR ε hc (t / c) P`. Use `⟨MvPolynomial.C (((Real.pi : ℂ) / c) ^ (n * m)) * R, fun y => ?_⟩` and prove the remaining obligations. Establish `hy` using `hR y`.

Rewrite `hy` using `[e]`. Establish `hA : ∀ a, (Real.pi : ℂ) ^ n / (Amat ε c t (herm y) a).det = ((Real.pi : ℂ) / c) ^ n * (if ε a then uM ((t / c : ℝ) : ℂ) y else vM ((t / c : ℝ) : ℂ) y).det`. Introduce `a`. Use `GM.amat_det ε hc.ne' (t / c) (GM.herm_isHermitian y) a` as an intermediate fact. Rewrite `this` using `[e, mm_inv]`.

Conclude with `this`. Rewrite using `[hy, hB m n ε c t hc _ (GM.herm_isHermitian y)]`. Repeatedly rewrite using `[hA]`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Simplify using `only [apply_ite Matrix.det]`.

Rewrite using `[Finset.prod_ite]`. Simplify using `only [Finset.prod_const]`. Unfold `cls`. Simplify using `only [neg_zero, Complex.cpow_zero, one_mul, evUV, map_mul, MvPolynomial.eval_C]`. Rewrite using `[← pow_mul, mul_comm n m]`.

Establish `hf : (Finset.univ.filter fun a => ¬ ε a = true) = Finset.univ.filter fun a => ε a = false`. Use extensionality with `a`. Simplify using the standard rewrite rules. Rewrite using `[hf]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gauss_of (hI : IntegP) (hW : Wick) (hR : Rot) (hB : Base) : Gauss := by
  intro m n ε c t hc _ P
  have e : (t / c) * c = t := by field_simp
  obtain ⟨R, hR⟩ := key hI hW hR ε hc (t / c) P
  refine ⟨MvPolynomial.C (((Real.pi : ℂ) / c) ^ (n * m)) * R, fun y => ?_⟩
  have hy := hR y
  rw [e] at hy
  have hA : ∀ a, (Real.pi : ℂ) ^ n / (Amat ε c t (herm y) a).det =
      ((Real.pi : ℂ) / c) ^ n * (if ε a then uM ((t / c : ℝ) : ℂ) y else vM ((t / c : ℝ) : ℂ) y).det := by
    intro a
    have := GM.amat_det ε hc.ne' (t / c) (GM.herm_isHermitian y) a
    rw [e, mm_inv] at this
    exact this
  rw [hy, hB m n ε c t hc _ (GM.herm_isHermitian y)]
  simp_rw [hA]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp only [apply_ite Matrix.det]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  unfold cls
  simp only [neg_zero, Complex.cpow_zero, one_mul, evUV, map_mul, MvPolynomial.eval_C]
  rw [← pow_mul, mul_comm n m]
  have hf : (Finset.univ.filter fun a => ¬ ε a = true) = Finset.univ.filter fun a => ε a = false := by
    ext a; simp
  rw [hf]
  ring

end PositivityTheory.Rg.Sw.WR.G
