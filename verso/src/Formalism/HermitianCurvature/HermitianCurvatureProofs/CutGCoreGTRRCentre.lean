import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRotCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

namespace RRCentre

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

variable {k r : ℕ}

def genW (k r : ℕ) (w : Fin (k + 1) → ℝ) : Q.Mx k r :=
  Matrix.diagonal fun i =>
    if h : r ≤ i.val ∧ i.val ≤ r + k then Complex.I * ((w ⟨i.val - r, by omega⟩ : ℝ) : ℂ) else 0

def dW (k : ℕ) (w : Fin (k + 1) → ℝ) (t : ℝ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  Matrix.diagonal fun j => Complex.exp (Complex.I * ((t * w j : ℝ) : ℂ))

/- English proof (translation)
Unfold `genW`. Rewrite using `[← Matrix.diagonal_smul, Matrix.exp_diagonal]`. Use extensionality with `i j`. Unfold `dW B2.embWb`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Distinguish the cases in `h : r ≤ i.val ∧ i.val ≤ r + k`. Rewrite using `[dif_pos ⟨h, h⟩, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]`. Simplify using `only [Pi.coe_exp, Pi.smul_apply, dif_pos h, smul_eq_mul]`. Rewrite using `[← Complex.exp_eq_exp_ℂ]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[dif_neg (fun h' => h h'.1), if_pos ⟨rfl, h⟩, Matrix.diagonal_apply_eq]`. Simplify using `only [Pi.coe_exp, Pi.smul_apply, dif_neg h, smul_zero]`.

Conclude with `NormedSpace.exp_zero`. Rewrite using `[Matrix.diagonal_apply_ne _ hij]`. Distinguish the cases in `h1 : (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)`. Rewrite using `[dif_pos h1, Matrix.diagonal_apply_ne]`. Introduce `he`.

Apply `hij` to reduce the goal to its premises. Use `ext`. Use `congrArg Fin.val he` as an intermediate fact. Simplify using `only at this`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[dif_neg h1, if_neg (fun h2 => hij h2.1)]`.
-/
theorem exp_genW (w : Fin (k + 1) → ℝ) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • genW k r w) = B2.embWb k r (dW k w t) := by
  unfold genW
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal]
  ext i j
  unfold dW B2.embWb
  by_cases hij : i = j
  · subst hij
    by_cases h : r ≤ i.val ∧ i.val ≤ r + k
    · rw [dif_pos ⟨h, h⟩, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
      simp only [Pi.coe_exp, Pi.smul_apply, dif_pos h, smul_eq_mul]
      rw [← Complex.exp_eq_exp_ℂ]
      congr 1
      push_cast
      ring
    · rw [dif_neg (fun h' => h h'.1), if_pos ⟨rfl, h⟩, Matrix.diagonal_apply_eq]
      simp only [Pi.coe_exp, Pi.smul_apply, dif_neg h, smul_zero]
      exact NormedSpace.exp_zero
  · rw [Matrix.diagonal_apply_ne _ hij]
    by_cases h1 : (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)
    · rw [dif_pos h1, Matrix.diagonal_apply_ne]
      intro he
      apply hij
      ext
      have := congrArg Fin.val he
      simp only at this
      omega
    · rw [dif_neg h1, if_neg (fun h2 => hij h2.1)]

/- English proof (translation)
Use `show Matrix.conjTranspose (dW k w t) * Hb k * dW k w t = Hb k`. Unfold `dW Hb`. Rewrite using `[Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `j`.

Establish `h : star (Complex.exp (Complex.I * ((t * w j : ℝ) : ℂ))) * Complex.exp (Complex.I * ((t * w j : ℝ) : ℂ)) = 1`. Rewrite using `[Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_I, Complex.conj_ofReal]`. Simplify using the standard rewrite rules. Simplify using `only [Pi.star_apply]`. Take the linear combination `(if j = Fin.last k then (-1 : ℂ) else 1) * h`.
-/
theorem dW_uh (w : Fin (k + 1) → ℝ) (t : ℝ) : dW k w t ∈ UH (Hb k) := by
  show Matrix.conjTranspose (dW k w t) * Hb k * dW k w t = Hb k
  unfold dW Hb
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext j
  have h : star (Complex.exp (Complex.I * ((t * w j : ℝ) : ℂ))) * Complex.exp (Complex.I * ((t * w j : ℝ) : ℂ)) = 1 := by
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
    simp
  simp only [Pi.star_apply]
  linear_combination (if j = Fin.last k then (-1 : ℂ) else 1) * h

/- English proof (translation)
Rewrite using `[exp_genW]`. Take `⟨μ, hμ, rfl⟩` from `(TwoByOneBlock.UWb_iff g).1 (NFRadRedA.glev_uwb hg)`. Rewrite using `[← TwoByOneBlock.emb_mul]`. Conclude with `NFRadRedA.uwb_glev (TwoByOneBlock.emb_mem_UWb (TwoByOneBlock.UH_mul hμ (dW_uh w t)))`.
-/
theorem glev_mul_exp {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r)) (w : Fin (k + 1) → ℝ) (t : ℝ) :
    g * NormedSpace.exp ((t : ℂ) • genW k r w) ∈ Q.Glev k r (Fin.last r) := by
  rw [exp_genW]
  obtain ⟨μ, hμ, rfl⟩ := (TwoByOneBlock.UWb_iff g).1 (NFRadRedA.glev_uwb hg)
  rw [← TwoByOneBlock.emb_mul]
  exact NFRadRedA.uwb_glev (TwoByOneBlock.emb_mem_UWb (TwoByOneBlock.UH_mul hμ (dW_uh w t)))

/- English proof (translation)
Establish `hγ : HasDerivAt (fun t : ℝ => (x.1, x.2 * NormedSpace.exp ((t : ℂ) • genW k r w))) ((0 : Fin r → ℂ), x.2 * genW k r w) 0` using `(hasDerivAt_const (0 : ℝ) x.1).prodMk (hasDerivAt_mul_exp_smul_zero x.2 _)`. Establish `hγ0 : (fun t : ℝ => (x.1, x.2 * NormedSpace.exp ((t : ℂ) • genW k r w))) 0 = x`. Simplify using `[NormedSpace.exp_zero]`. Establish `hd : DifferentiableAt ℝ F x` using `(hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)`. Establish `hcomp` using `hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm`.

Use `hcomp.congr_of_eventuallyEq ?_` and prove the remaining obligations. Establish `hc : Filter.Tendsto (fun t : ℝ => (x.1, x.2 * NormedSpace.exp ((t : ℂ) • genW k r w))) (nhds 0) (nhds x)`. Establish `h` using `hγ.continuousAt.tendsto`. Apply the tactic sequence `first | (rw [hγ0] at h; exact h) | exact hγ0 ▸ h | (simp only [hγ0] at h; exact h)`. Use `filter_upwards [hc (hU.mem_nhds hx)] with t ht`.

Conclude with `he _ ht (glev_mul_exp hxG w t)`.
-/
theorem hasDerivAt_genW {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {Φ : (Fin r → ℂ) → Q.Mx k r → E} {U : Set ((Fin r → ℂ) × Q.Mx k r)} {F : (Fin r → ℂ) × Q.Mx k r → E}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (he : ∀ y ∈ U, y.2 ∈ Q.Glev k r (Fin.last r) → Φ y.1 y.2 = F y)
    {x : (Fin r → ℂ) × Q.Mx k r} (hx : x ∈ U) (hxG : x.2 ∈ Q.Glev k r (Fin.last r)) (w : Fin (k + 1) → ℝ) :
    HasDerivAt (fun t : ℝ => Φ x.1 (x.2 * NormedSpace.exp ((t : ℂ) • genW k r w)))
      (fderiv ℝ F x ((0 : Fin r → ℂ), x.2 * genW k r w)) 0 := by
  have hγ : HasDerivAt (fun t : ℝ => (x.1, x.2 * NormedSpace.exp ((t : ℂ) • genW k r w)))
      ((0 : Fin r → ℂ), x.2 * genW k r w) 0 :=
    (hasDerivAt_const (0 : ℝ) x.1).prodMk (hasDerivAt_mul_exp_smul_zero x.2 _)
  have hγ0 : (fun t : ℝ => (x.1, x.2 * NormedSpace.exp ((t : ℂ) • genW k r w))) 0 = x := by
    simp [NormedSpace.exp_zero]
  have hd : DifferentiableAt ℝ F x := (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)
  have hcomp := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  refine hcomp.congr_of_eventuallyEq ?_
  have hc : Filter.Tendsto (fun t : ℝ => (x.1, x.2 * NormedSpace.exp ((t : ℂ) • genW k r w))) (nhds 0) (nhds x) := by
    have h := hγ.continuousAt.tendsto
    first | (rw [hγ0] at h; exact h) | exact hγ0 ▸ h | (simp only [hγ0] at h; exact h)
  filter_upwards [hc (hU.mem_nhds hx)] with t ht
  exact he _ ht (glev_mul_exp hxG w t)

/- English proof (translation)
Unfold `Hpk`. Distinguish the cases in `hip : i = p`. Substitute `hip` using the available equality. Rewrite using `[if_neg (by omega), if_neg (by omega), if_pos ⟨hp.1, hp.2, rfl⟩, if_pos rfl]`. Establish `hv : i.val ≠ p.val` using `fun h => hip (Fin.ext h)`.

Rewrite using `[if_neg (by omega), if_neg (by omega), if_neg (fun h => hip h.2.2), if_neg hip]`.
-/
theorem hpk_col (p i : Fin (2 * r + k + 1)) (hp : r ≤ p.val ∧ p.val ≤ r + k) :
    Hpk k r i p = if i = p then (if p.val = r + k then -1 else 1) else 0 := by
  unfold Hpk
  by_cases hip : i = p
  · subst hip
    rw [if_neg (by omega), if_neg (by omega), if_pos ⟨hp.1, hp.2, rfl⟩, if_pos rfl]
  · have hv : i.val ≠ p.val := fun h => hip (Fin.ext h)
    rw [if_neg (by omega), if_neg (by omega), if_neg (fun h => hip h.2.2), if_neg hip]

/- English proof (translation)
Unfold `Hpk`. Distinguish the cases in `hip : j = p`. Substitute `hip` using the available equality. Rewrite using `[if_neg (by omega), if_neg (by omega), if_pos ⟨hp.1, hp.2, rfl⟩, if_pos rfl]`. Establish `hv : j.val ≠ p.val` using `fun h => hip (Fin.ext h)`.

Rewrite using `[if_neg (by omega), if_neg (by omega), if_neg (fun h => hip h.2.2.symm), if_neg hip]`.
-/
theorem hpk_row (p j : Fin (2 * r + k + 1)) (hp : r ≤ p.val ∧ p.val ≤ r + k) :
    Hpk k r p j = if j = p then (if p.val = r + k then -1 else 1) else 0 := by
  unfold Hpk
  by_cases hip : j = p
  · subst hip
    rw [if_neg (by omega), if_neg (by omega), if_pos ⟨hp.1, hp.2, rfl⟩, if_pos rfl]
  · have hv : j.val ≠ p.val := fun h => hip (Fin.ext h)
    rw [if_neg (by omega), if_neg (by omega), if_neg (fun h => hip h.2.2.symm), if_neg hip]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single p]`. Distinguish the cases in `hm : m = p`. Substitute `hm` using the available equality. Simplify using `[Matrix.single_apply]`. Simplify using `[Matrix.single_apply, Ne.symm hm, hm]`.

Introduce `l _ hl`. Simplify using `[Matrix.single_apply, Ne.symm hl]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ p) h`.
-/
theorem hs_apply (p i m : Fin (2 * r + k + 1)) :
    (Hpk k r * Matrix.single p p (1 : ℂ)) i m = if m = p then Hpk k r i p else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single p]
  · by_cases hm : m = p
    · subst hm; simp [Matrix.single_apply]
    · simp [Matrix.single_apply, Ne.symm hm, hm]
  · intro l _ hl; simp [Matrix.single_apply, Ne.symm hl]
  · intro h; exact absurd (Finset.mem_univ p) h

/- English proof (translation)
Rewrite using `[Qx2.hpk_inv, Matrix.conjTranspose_single, star_one]`. Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single p]`. Rewrite using `[hs_apply, if_pos rfl, hpk_col p i hp, hpk_row p j hp, Matrix.single_apply]`. Apply the tactic sequence `by_cases hi : i = p <;> by_cases hj : j = p`.

Apply the tactic sequence `subst hi; subst hj; simp only [if_true, and_self]; split_ifs <;> norm_num`. Simplify using `[hi, hj, Ne.symm hj]`. Simplify using `[hi, hj, Ne.symm hi]`. Simplify using `[hi, hj, Ne.symm hi]`. Introduce `m _ hm`.

Rewrite using `[hs_apply, if_neg hm, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ p) h`.
-/
theorem hpk_single (p : Fin (2 * r + k + 1)) (hp : r ≤ p.val ∧ p.val ≤ r + k) :
    (Hpk k r)⁻¹ * (Matrix.single p p (1 : ℂ)).conjTranspose * Hpk k r = Matrix.single p p 1 := by
  rw [Qx2.hpk_inv, Matrix.conjTranspose_single, star_one]
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single p]
  · rw [hs_apply, if_pos rfl, hpk_col p i hp, hpk_row p j hp, Matrix.single_apply]
    by_cases hi : i = p <;> by_cases hj : j = p
    · subst hi; subst hj; simp only [if_true, and_self]; split_ifs <;> norm_num
    · simp [hi, hj, Ne.symm hj]
    · simp [hi, hj, Ne.symm hi]
    · simp [hi, hj, Ne.symm hi]
  · intro m _ hm
    rw [hs_apply, if_neg hm, zero_mul]
  · intro h; exact absurd (Finset.mem_univ p) h

/- English proof (translation)
Unfold `hpart1`. Rewrite using `[hpk_single p hp, sub_self, smul_zero]`.
-/
theorem hpart1_single (p : Fin (2 * r + k + 1)) (hp : r ≤ p.val ∧ p.val ≤ r + k) :
    hpart1 (Hpk k r) (Matrix.single p p (1 : ℂ)) = 0 := by
  unfold hpart1
  rw [hpk_single p hp, sub_self, smul_zero]

/- English proof (translation)
Establish `hp : r ≤ p.val ∧ p.val ≤ r + k` using `⟨by omega, by omega⟩`. Unfold `hpart2`. Rewrite using `[hpk_single p hp]`. Use extensionality with `i l`. Unfold `genW`.

Rewrite using `[Matrix.smul_apply, Matrix.add_apply, Matrix.single_apply, smul_eq_mul, Matrix.diagonal_apply]`. Establish `hI : Complex.I ≠ 0` using `Complex.I_ne_zero`. Distinguish the cases in `hil : i = l`. Substitute `hil` using the available equality. Rewrite using `[if_pos rfl]`.

Distinguish the cases in `hi : i = p`. Substitute `hi` using the available equality. Rewrite using `[if_pos ⟨rfl, rfl⟩, dif_pos hp]`. Simplify using `only`. Rewrite using `[if_pos (by omega)]`.

Clear the denominators using the available nonvanishing facts. Use `push_cast`. Put the polynomial expressions in normal form. Rewrite using `[Complex.I_sq]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[if_neg (fun h => hi h.1.symm)] dsimp only split_ifs with h1 h2`. It suffices to derive a contradiction. Apply `hi` to reduce the goal to its premises. Apply `Fin.ext` to reduce the goal to its premises. Use linear arithmetic over natural numbers and integers.

Apply the tactic sequence `all_goals simp`. Rewrite using `[if_neg (fun h => hil (h.1.symm.trans h.2)), if_neg hil]`. Simplify using the standard rewrite rules.
-/
theorem hpart2_single (n : ℕ) (p : Fin (2 * r + k + 1)) (hpn : p.val = r + n) (hn : n ≤ k) :
    hpart2 (Hpk k r) (Matrix.single p p (1 : ℂ)) = genW k r (fun j' => if j'.val = n then -1 else 0) := by
  have hp : r ≤ p.val ∧ p.val ≤ r + k := ⟨by omega, by omega⟩
  unfold hpart2
  rw [hpk_single p hp]
  ext i l
  unfold genW
  rw [Matrix.smul_apply, Matrix.add_apply, Matrix.single_apply, smul_eq_mul, Matrix.diagonal_apply]
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  by_cases hil : i = l
  · subst hil
    rw [if_pos rfl]
    by_cases hi : i = p
    · subst hi
      rw [if_pos ⟨rfl, rfl⟩, dif_pos hp]
      dsimp only
      rw [if_pos (by omega)]
      field_simp
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    · rw [if_neg (fun h => hi h.1.symm)]
      dsimp only
      split_ifs with h1 h2
      · exfalso; apply hi; apply Fin.ext; omega
      all_goals simp
  · rw [if_neg (fun h => hil (h.1.symm.trans h.2)), if_neg hil]
    simp

/- English proof (translation)
Unfold `RdV`. Simplify using `[NormedSpace.exp_zero]`.
-/
theorem rdV_zero' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : Q.Mx k r → E) (g : Q.Mx k r) :
    RdV (0 : Q.Mx k r) f g = 0 := by
  unfold RdV
  simp [NormedSpace.exp_zero]

/- English proof (translation)
Use extensionality with `i l`. Rewrite using `[Matrix.sum_apply, Matrix.neg_apply]`. Unfold `genW`. Simplify using `only [Matrix.diagonal_apply]`. Distinguish the cases in `hil : i = l`.

Substitute `hil` using the available equality. Simplify using `only [if_true]`. Distinguish the cases in `h : r ≤ i.val ∧ i.val ≤ r + k`. Simplify using `only [dif_pos h]`. Establish `hm : i.val - r < Q.mdim k r (Fin.last r)` using `by unfold Q.mdim; simp; omega`.

Rewrite using `[Finset.sum_eq_single ⟨i.val - r, hm⟩]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Rewrite using `[if_neg]`. Simplify using the standard rewrite rules.

Introduce `hh`. Apply `hb` to reduce the goal to its premises. Use `ext`. Simplify using `only at hh ⊢`. Use linear arithmetic over natural numbers and integers.

Introduce `hh`. Conclude with `absurd (Finset.mem_univ _) hh`. Simplify using `[dif_neg h]`. Simplify using `[hil]`.
-/
theorem genW_sum : ∑ a : Fin (Q.mdim k r (Fin.last r)),
    genW k r (fun j' : Fin (k + 1) => if j'.val = a.val then (-1 : ℝ) else 0) = -genW k r (fun _ => 1) := by
  ext i l
  rw [Matrix.sum_apply, Matrix.neg_apply]
  unfold genW
  simp only [Matrix.diagonal_apply]
  by_cases hil : i = l
  · subst hil
    simp only [if_true]
    by_cases h : r ≤ i.val ∧ i.val ≤ r + k
    · simp only [dif_pos h]
      have hm : i.val - r < Q.mdim k r (Fin.last r) := by unfold Q.mdim; simp; omega
      rw [Finset.sum_eq_single ⟨i.val - r, hm⟩]
      · simp
      · intro b _ hb
        rw [if_neg]
        · simp
        · intro hh; apply hb; ext; simp only at hh ⊢; omega
      · intro hh; exact absurd (Finset.mem_univ _) hh
    · simp [dif_neg h]
  · simp [hil]

/- English proof (translation)
Rewrite using `[exp_genW]`. Unfold `zc dW`. Use `congr 1`. Use extensionality with `i j`. Rewrite using `[Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply]`.

Distinguish the cases in `h : i = j`. Simplify using `[h, mul_comm]`. Simplify using `[h]`.
-/
theorem zc_eq (φ : ℝ) : zc k r φ = NormedSpace.exp ((φ : ℂ) • genW k r (fun _ => 1)) := by
  rw [exp_genW]
  unfold zc dW
  congr 1
  ext i j
  rw [Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · simp [h, mul_comm]
  · simp [h]

/- English proof (translation)
Establish `ha : a.val ≤ k` using `by have := a.isLt; unfold Q.mdim at this; simp at this; omega`. Establish `hpn : (Q.posL k r (Fin.last r) a).val = r + a.val` using `by simp [Q.posL]; omega`. Establish `hp : r ≤ (Q.posL k r (Fin.last r) a).val ∧ (Q.posL k r (Fin.last r) a).val ≤ r + k` using `⟨by omega, by omega⟩`. Use `show RdV _ _ _ + Complex.I • RdV _ _ _ = _`. Rewrite using `[hpart1_single _ hp, hpart2_single a.val _ hpn ha, rdV_zero', zero_add]`.

Use `congr 1`. Conclude with `(hasDerivAt_genW hU hF he hx hxG _).deriv`.
-/
theorem eh_pp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {Φ : (Fin r → ℂ) → Q.Mx k r → E} {U : Set ((Fin r → ℂ) × Q.Mx k r)} {F : (Fin r → ℂ) × Q.Mx k r → E}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (he : ∀ y ∈ U, y.2 ∈ Q.Glev k r (Fin.last r) → Φ y.1 y.2 = F y)
    {x : (Fin r → ℂ) × Q.Mx k r} (hx : x ∈ U) (hxG : x.2 ∈ Q.Glev k r (Fin.last r))
    (a : Fin (Q.mdim k r (Fin.last r))) :
    Q.EH k r (Q.posL k r (Fin.last r) a) (Q.posL k r (Fin.last r) a) (Φ x.1) x.2 =
      Complex.I • fderiv ℝ F x ((0 : Fin r → ℂ),
        x.2 * genW k r (fun j' : Fin (k + 1) => if j'.val = a.val then (-1 : ℝ) else 0)) := by
  have ha : a.val ≤ k := by have := a.isLt; unfold Q.mdim at this; simp at this; omega
  have hpn : (Q.posL k r (Fin.last r) a).val = r + a.val := by simp [Q.posL]; omega
  have hp : r ≤ (Q.posL k r (Fin.last r) a).val ∧ (Q.posL k r (Fin.last r) a).val ≤ r + k :=
    ⟨by omega, by omega⟩
  show RdV _ _ _ + Complex.I • RdV _ _ _ = _
  rw [hpart1_single _ hp, hpart2_single a.val _ hpn ha, rdV_zero', zero_add]
  congr 1
  exact (hasDerivAt_genW hU hF he hx hxG _).deriv

end

end RRCentre

open RRCentre in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
/- English proof (translation)
Introduce `k r z z' Wp Wq _ _ _ _ π π' Φ x hx`. Take `⟨U, F, hU, hxU, hF, he⟩` from `Φ.2.2.1 x hx`. Establish `hxG : x.2 ∈ Q.Glev k r (Fin.last r)` using `hx.2.1`. Establish `hfun : (fun φ : ℝ => (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 (x.2 * zc k r φ)) = fun φ : ℝ => (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 (x.2 * NormedSpace.exp ((φ : ℂ) • genW k r (fun _ => 1)))`. Use function extensionality and compare the values at `φ`.

Rewrite using `[zc_eq]`. Rewrite using `[hfun]`. Establish `hd` using `hasDerivAt_genW hU hF he hxU hxG (fun _ => 1)`. Use `hd.congr_deriv ?_` and prove the remaining obligations. Use `symm`.

Rewrite using `[Finset.sum_congr rfl (fun a _ => eh_pp hU hF he hxU hxG a), ← Finset.smul_sum, ← map_sum]`. Establish `hs : ∑ a : Fin (Q.mdim k r (Fin.last r)), ((0 : Fin r → ℂ), x.2 * genW k r (fun j' : Fin (k + 1) => if j'.val = a.val then (-1 : ℝ) else 0)) = -((0 : Fin r → ℂ), x.2 * genW k r (fun _ => 1))` using `by ext1`. Rewrite using `[Prod.fst_sum]`. Simplify using the standard rewrite rules. Rewrite using `[Prod.snd_sum, ← Finset.mul_sum, genW_sum]`.

Simplify using the standard rewrite rules. Rewrite using `[hs, map_neg, smul_smul, Complex.I_mul_I, neg_one_smul, neg_neg]`.
-/
theorem rotation_centre_condition : GTRRCentre := by
  intro k r z z' Wp Wq _ _ _ _ π π' Φ x hx
  obtain ⟨U, F, hU, hxU, hF, he⟩ := Φ.2.2.1 x hx
  have hxG : x.2 ∈ Q.Glev k r (Fin.last r) := hx.2.1
  have hfun : (fun φ : ℝ => (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 (x.2 * zc k r φ)) =
      fun φ : ℝ => (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1
        (x.2 * NormedSpace.exp ((φ : ℂ) • genW k r (fun _ => 1))) := by
    funext φ; rw [zc_eq]
  rw [hfun]
  have hd := hasDerivAt_genW hU hF he hxU hxG (fun _ => 1)
  refine hd.congr_deriv ?_
  symm
  rw [Finset.sum_congr rfl (fun a _ => eh_pp hU hF he hxU hxG a), ← Finset.smul_sum, ← map_sum]
  have hs : ∑ a : Fin (Q.mdim k r (Fin.last r)), ((0 : Fin r → ℂ),
      x.2 * genW k r (fun j' : Fin (k + 1) => if j'.val = a.val then (-1 : ℝ) else 0)) =
      -((0 : Fin r → ℂ), x.2 * genW k r (fun _ => 1)) := by
    ext1
    · rw [Prod.fst_sum]; simp
    · rw [Prod.snd_sum, ← Finset.mul_sum, genW_sum]
      simp
  rw [hs, map_neg, smul_smul, Complex.I_mul_I, neg_one_smul, neg_neg]

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
