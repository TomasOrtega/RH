import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutTypeNormMeas
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsCompactZetaLe
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock

namespace Formalism.FourierDecayAlt.P.CutBP.TNM.HM

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants MeasureTheory Matrix
open Formalism.FourierDecayAlt.P5.HerB

noncomputable section

variable {k r : ℕ}

/- English proof (translation)
The claim follows from `hb_self_real _ (hpk_herm k r) x`.
-/
theorem herm_real (x : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) x x = ((herm (Hpk k r) x x).re : ℂ) :=
  hb_self_real _ (hpk_herm k r) x

/- English proof (translation)
Establish `hzz : herm (Hpk k r) z z ≠ 0` using `fun h => by rw [h, Complex.zero_re] at hzn; exact lt_irrefl _ hzn`. Establish `hW : ∀ x, inWb k r x → herm (Hpk k r) x z = 0 → herm (Hpk k r) v x = 0`. Introduce `x hx hxz`. Establish `key : ∀ s : ℝ, 0 < s → ‖herm (Hpk k r) v x‖ * s ≤ (herm (Hpk k r) x x).re`. Introduce `s hs`.

Use `set t : ℝ := Real.sqrt s with htdef`. Establish `ht : 0 < t` using `Real.sqrt_pos.2 hs`. Establish `htt : t * t = s` using `Real.mul_self_sqrt hs.le`. Establish `h` using `norm_perp_le hz hzn (u := (t : ℂ) • v) (v := ((t⁻¹ : ℝ) : ℂ) • x) (inWb_smul _ hv) (inWb_smul _ hx) (by rw [hb_smul_left, hvz, mul_zero]) (by rw [hb_smul_left, hxz, mul_zero])`. Rewrite `h` using `[hb_smul_left, hb_smul_right, hb_smul_left, hb_smul_right, hb_smul_left, hb_smul_right]`.

Establish `e1 : (t : ℂ) * (star (((t⁻¹ : ℝ)) : ℂ) * herm (Hpk k r) v x) = herm (Hpk k r) v x`. Rewrite using `[Complex.star_def, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ ht.ne', Complex.ofReal_one, one_mul]`. Rewrite `h` using `[e1]`. Simplify using `only [Complex.star_def, Complex.conj_ofReal] at h`. Rewrite `h` using `[Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.re_ofReal_mul, h0]`.

Establish `hti : t⁻¹ * (t⁻¹ * (herm (Hpk k r) x x).re) = (herm (Hpk k r) x x).re / s`. Rewrite using `[← htt]`. Clear the denominators using the available nonvanishing facts. Rewrite `h` using `[hti]`. Establish `h' : ‖herm (Hpk k r) v x‖ ≤ (herm (Hpk k r) x x).re / s` using `by linarith`.

Rewrite `h'` using `[le_div_iff₀ hs]`. Then use the resulting hypothesis. Assume the negation of the conclusion as `hne`. Establish `hn : 0 < ‖herm (Hpk k r) v x‖` using `norm_pos_iff.2 hne`. Establish `hxx : 0 ≤ (herm (Hpk k r) x x).re` using `perp_nonneg hz hzn hx hxz`. Use `key (((herm (Hpk k r) x x).re + 1) / ‖herm (Hpk k r) v x‖) (by positivity)` as an intermediate fact.

Rewrite `this` using `[mul_div_cancel₀ _ hn.ne']`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hall : ∀ y, herm (Hpk k r) v y = 0`. Introduce `y`. Establish `hd` using `Formalism.FourierDecayAlt.P.Dx2.DF.decomp (k := k) (r := r) y`.

Use `set α : ℂ := herm (Hpk k r) (Formalism.FourierDecayAlt.P.Dx2.DF.Wb y) z / herm (Hpk k r) z z with hα`. Establish `hWb : inWb k r (Formalism.FourierDecayAlt.P.Dx2.DF.Wb y)`. Introduce `i hi; simp only [Formalism.FourierDecayAlt.P.Dx2.DF.Wb]; rw [if_neg (by omega)]`. Establish `hx : inWb k r (Formalism.FourierDecayAlt.P.Dx2.DF.Wb y - α • z)` using `inWb_sub hWb (inWb_smul _ hz)`. Establish `hxz : herm (Hpk k r) (Formalism.FourierDecayAlt.P.Dx2.DF.Wb y - α • z) z = 0`.

Rewrite using `[hb_sub_left, hb_smul_left, hα, div_mul_cancel₀ _ hzz, sub_self]`. Establish `h1 : herm (Hpk k r) v (Formalism.FourierDecayAlt.P.Dx2.DF.Wb y) = 0`. Establish `e : Formalism.FourierDecayAlt.P.Dx2.DF.Wb y = (Formalism.FourierDecayAlt.P.Dx2.DF.Wb y - α • z) + α • z` using `by abel`. Rewrite using `[e, hb_add_right, hb_smul_right, hW _ hx hxz, hvz, mul_zero, add_zero]`. Rewrite using `[hd, hb_add_right, hb_add_right, h1, Formalism.FourierDecayAlt.P.Dx2.DF.herm_sum_right, Formalism.FourierDecayAlt.P.Dx2.DF.herm_sum_right]`.

Simplify using `only [hb_smul_right, Formalism.FourierDecayAlt.P.Dx2.DF.h_w_ee hv, Formalism.FourierDecayAlt.P.Dx2.DF.h_w_es hv, mul_zero, Finset.sum_const_zero, add_zero]`. Establish `hHv : Hpk k r *ᵥ v = 0`. Use function extensionality and compare the values at `p`. Use `hall (bvec p)` as an intermediate fact. Rewrite `this` using `[Formalism.FourierDecayAlt.P.Dx2.DF.herm_bvec_right]`.

Simplify `this` using `[mulVec, dotProduct]`. Establish `hHH : Hpk k r * Hpk k r = 1` using `(Formalism.QuantumDeterminants.hpkFacts k r).2.1`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem perp_eq_zero {z v : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hzn : (herm (Hpk k r) z z).re < 0)
    (hv : inWb k r v) (hvz : herm (Hpk k r) v z = 0) (h0 : (herm (Hpk k r) v v).re = 0) : v = 0 := by
  have hzz : herm (Hpk k r) z z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hzn; exact lt_irrefl _ hzn
  have hW : ∀ x, inWb k r x → herm (Hpk k r) x z = 0 → herm (Hpk k r) v x = 0 := by
    intro x hx hxz
    have key : ∀ s : ℝ, 0 < s → ‖herm (Hpk k r) v x‖ * s ≤ (herm (Hpk k r) x x).re := by
      intro s hs
      set t : ℝ := Real.sqrt s with htdef
      have ht : 0 < t := Real.sqrt_pos.2 hs
      have htt : t * t = s := Real.mul_self_sqrt hs.le
      have h := norm_perp_le hz hzn (u := (t : ℂ) • v) (v := ((t⁻¹ : ℝ) : ℂ) • x) (inWb_smul _ hv)
        (inWb_smul _ hx) (by rw [hb_smul_left, hvz, mul_zero]) (by rw [hb_smul_left, hxz, mul_zero])
      rw [hb_smul_left, hb_smul_right, hb_smul_left, hb_smul_right, hb_smul_left, hb_smul_right] at h
      have e1 : (t : ℂ) * (star (((t⁻¹ : ℝ)) : ℂ) * herm (Hpk k r) v x) = herm (Hpk k r) v x := by
        rw [Complex.star_def, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ ht.ne',
          Complex.ofReal_one, one_mul]
      rw [e1] at h
      simp only [Complex.star_def, Complex.conj_ofReal] at h
      rw [Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.re_ofReal_mul, h0] at h
      have hti : t⁻¹ * (t⁻¹ * (herm (Hpk k r) x x).re) = (herm (Hpk k r) x x).re / s := by
        rw [← htt]; field_simp
      rw [hti] at h
      have h' : ‖herm (Hpk k r) v x‖ ≤ (herm (Hpk k r) x x).re / s := by linarith
      rwa [le_div_iff₀ hs] at h'
    by_contra hne
    have hn : 0 < ‖herm (Hpk k r) v x‖ := norm_pos_iff.2 hne
    have hxx : 0 ≤ (herm (Hpk k r) x x).re := perp_nonneg hz hzn hx hxz
    have := key (((herm (Hpk k r) x x).re + 1) / ‖herm (Hpk k r) v x‖) (by positivity)
    rw [mul_div_cancel₀ _ hn.ne'] at this
    linarith
  have hall : ∀ y, herm (Hpk k r) v y = 0 := by
    intro y
    have hd := Formalism.FourierDecayAlt.P.Dx2.DF.decomp (k := k) (r := r) y
    set α : ℂ := herm (Hpk k r) (Formalism.FourierDecayAlt.P.Dx2.DF.Wb y) z / herm (Hpk k r) z z with hα
    have hWb : inWb k r (Formalism.FourierDecayAlt.P.Dx2.DF.Wb y) := by
      intro i hi; simp only [Formalism.FourierDecayAlt.P.Dx2.DF.Wb]; rw [if_neg (by omega)]
    have hx : inWb k r (Formalism.FourierDecayAlt.P.Dx2.DF.Wb y - α • z) := inWb_sub hWb (inWb_smul _ hz)
    have hxz : herm (Hpk k r) (Formalism.FourierDecayAlt.P.Dx2.DF.Wb y - α • z) z = 0 := by
      rw [hb_sub_left, hb_smul_left, hα, div_mul_cancel₀ _ hzz, sub_self]
    have h1 : herm (Hpk k r) v (Formalism.FourierDecayAlt.P.Dx2.DF.Wb y) = 0 := by
      have e : Formalism.FourierDecayAlt.P.Dx2.DF.Wb y = (Formalism.FourierDecayAlt.P.Dx2.DF.Wb y - α • z) + α • z := by abel
      rw [e, hb_add_right, hb_smul_right, hW _ hx hxz, hvz, mul_zero, add_zero]
    rw [hd, hb_add_right, hb_add_right, h1, Formalism.FourierDecayAlt.P.Dx2.DF.herm_sum_right, Formalism.FourierDecayAlt.P.Dx2.DF.herm_sum_right]
    simp only [hb_smul_right, Formalism.FourierDecayAlt.P.Dx2.DF.h_w_ee hv, Formalism.FourierDecayAlt.P.Dx2.DF.h_w_es hv, mul_zero,
      Finset.sum_const_zero, add_zero]
  have hHv : Hpk k r *ᵥ v = 0 := by
    funext p
    have := hall (bvec p)
    rw [Formalism.FourierDecayAlt.P.Dx2.DF.herm_bvec_right] at this
    simpa [mulVec, dotProduct] using this
  have hHH : Hpk k r * Hpk k r = 1 := (Formalism.QuantumDeterminants.hpkFacts k r).2.1
  calc v = (Hpk k r * Hpk k r) *ᵥ v := by rw [hHH, one_mulVec]
    _ = 0 := by rw [← mulVec_mulVec, hHv, mulVec_zero]

section house

def pW (k r : ℕ) (z u : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ := D.prW k r z u

def aC (k r : ℕ) (z e u : Fin (2 * r + k + 1) → ℂ) : ℂ := herm (Hpk k r) (pW k r z u) e

def nR (k r : ℕ) (z u : Fin (2 * r + k + 1) → ℂ) : ℝ := Real.sqrt (herm (Hpk k r) (pW k r z u) (pW k r z u)).re

def sC (k r : ℕ) (z e u : Fin (2 * r + k + 1) → ℂ) : ℂ :=
  if aC k r z e u = 0 then (nR k r z u : ℂ) else (nR k r z u : ℂ) * (aC k r z e u / (‖aC k r z e u‖ : ℂ))

def vH (k r : ℕ) (z e u : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ := pW k r z u - sC k r z e u • e

def hh (k r : ℕ) (z e u : Fin (2 * r + k + 1) → ℂ) : B.Mat k r :=
  if (herm (Hpk k r) (vH k r z e u) (vH k r z e u)).re = 0 then 1
  else Formalism.FourierDecayAlt.P.TwoByOneBlock.qrefl (Hpk k r) (vH k r z e u)
    ((-2 / (herm (Hpk k r) (vH k r z e u) (vH k r z e u)).re : ℝ) : ℂ)

variable {k r : ℕ} {z e : Fin (2 * r + k + 1) → ℂ}

/- English proof (translation)
Unfold `pW`. Rewrite using `[Formalism.FourierDecayAlt.P.Dx2.DF.prW_eq]`. Use `inWb_sub ?_ (inWb_smul _ hz)` and prove the remaining obligations. Introduce `i hi; simp only [Formalism.FourierDecayAlt.P.Dx2.DF.Wb]; rw [if_neg (by omega)]`.
-/
theorem pW_inWb (hz : inWb k r z) (u : Fin (2 * r + k + 1) → ℂ) : inWb k r (pW k r z u) := by
  unfold pW
  rw [Formalism.FourierDecayAlt.P.Dx2.DF.prW_eq]
  refine inWb_sub ?_ (inWb_smul _ hz)
  intro i hi; simp only [Formalism.FourierDecayAlt.P.Dx2.DF.Wb]; rw [if_neg (by omega)]

/- English proof (translation)
Unfold `pW`. Rewrite using `[Formalism.FourierDecayAlt.P.Dx2.DF.prW_eq, hb_sub_left, hb_smul_left, div_mul_cancel₀ _ hzz, sub_self]`.
-/
theorem pW_perp (hzz : herm (Hpk k r) z z ≠ 0) (u : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (pW k r z u) z = 0 := by
  unfold pW
  rw [Formalism.FourierDecayAlt.P.Dx2.DF.prW_eq, hb_sub_left, hb_smul_left, div_mul_cancel₀ _ hzz, sub_self]

/- English proof (translation)
The claim follows from `inWb_sub (pW_inWb hz u) (inWb_smul _ he)`.
-/
theorem vH_inWb (hz : inWb k r z) (he : inWb k r e) (u : Fin (2 * r + k + 1) → ℂ) : inWb k r (vH k r z e u) :=
  inWb_sub (pW_inWb hz u) (inWb_smul _ he)

/- English proof (translation)
Unfold `vH`. Rewrite using `[hb_sub_left, hb_smul_left, pW_perp hzz, hez, mul_zero, sub_zero]`.
-/
theorem vH_perp (hzz : herm (Hpk k r) z z ≠ 0) (hez : herm (Hpk k r) e z = 0) (u : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (vH k r z e u) z = 0 := by
  unfold vH
  rw [hb_sub_left, hb_smul_left, pW_perp hzz, hez, mul_zero, sub_zero]

/- English proof (translation)
Unfold `hh`. Use `split_ifs with h0`. Conclude with `⟨by simp [UH], fun a => by simp, by simp⟩`. Use `set v := vH k r z e u with hv set R := (herm (Hpk k r) v v).re with hR`. Establish `hvv : herm (Hpk k r) v v = (R : ℂ)` using `herm_real v`.

Establish `hvW` using `vH_inWb hz he u`. Establish `hvz` using `vH_perp hzz hez u`. Establish `hzv : herm (Hpk k r) z v = 0` using `by rw [hb_symm _ (hpk_herm k r) v z, hvz, star_zero]`. Use `⟨?_, fun a => ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Apply `Formalism.FourierDecayAlt.P.TwoByOneBlock.qrefl_mem (Hpk k r) (hpk_herm k r)` to reduce the goal to its premises.

Rewrite using `[hvv, Complex.star_def, Complex.conj_ofReal]`. Establish `hR0 : (R : ℂ) ≠ 0` using `by exact_mod_cast h0`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[Formalism.FourierDecayAlt.P.TwoByOneBlock.qrefl_mulVec, Formalism.FourierDecayAlt.P.Dx2.DF.h_ee_w hvW a, mul_zero, zero_smul, add_zero]`. Rewrite using `[Formalism.FourierDecayAlt.P.TwoByOneBlock.qrefl_mulVec, Formalism.FourierDecayAlt.P.Dx2.DF.h_es_w hvW a, mul_zero, zero_smul, add_zero]`. Rewrite using `[Formalism.FourierDecayAlt.P.TwoByOneBlock.qrefl_mulVec, hzv, mul_zero, zero_smul, add_zero]`.
-/
theorem hh_mem (hz : inWb k r z) (hzz : herm (Hpk k r) z z ≠ 0) (he : inWb k r e) (hez : herm (Hpk k r) e z = 0)
    (u : Fin (2 * r + k + 1) → ℂ) : hh k r z e u ∈ UWset k r z := by
  unfold hh
  split_ifs with h0
  · exact ⟨by simp [UH], fun a => by simp, by simp⟩
  · set v := vH k r z e u with hv
    set R := (herm (Hpk k r) v v).re with hR
    have hvv : herm (Hpk k r) v v = (R : ℂ) := herm_real v
    have hvW := vH_inWb hz he u
    have hvz := vH_perp hzz hez u
    have hzv : herm (Hpk k r) z v = 0 := by rw [hb_symm _ (hpk_herm k r) v z, hvz, star_zero]
    refine ⟨?_, fun a => ⟨?_, ?_⟩, ?_⟩
    · apply Formalism.FourierDecayAlt.P.TwoByOneBlock.qrefl_mem (Hpk k r) (hpk_herm k r)
      rw [hvv, Complex.star_def, Complex.conj_ofReal]
      have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast h0
      push_cast
      field_simp
      ring
    · rw [Formalism.FourierDecayAlt.P.TwoByOneBlock.qrefl_mulVec, Formalism.FourierDecayAlt.P.Dx2.DF.h_ee_w hvW a, mul_zero, zero_smul, add_zero]
    · rw [Formalism.FourierDecayAlt.P.TwoByOneBlock.qrefl_mulVec, Formalism.FourierDecayAlt.P.Dx2.DF.h_es_w hvW a, mul_zero, zero_smul, add_zero]
    · rw [Formalism.FourierDecayAlt.P.TwoByOneBlock.qrefl_mulVec, hzv, mul_zero, zero_smul, add_zero]

end house

section apply

variable {k r : ℕ} {z e : Fin (2 * r + k + 1) → ℂ}

/- English proof (translation)
Establish `hzz : herm (Hpk k r) z z ≠ 0` using `fun h => by rw [h, Complex.zero_re] at hzn; exact lt_irrefl _ hzn`. Establish `hp : pW k r z u = u` using `Formalism.FourierDecayAlt.P.Dx2.DF.prW_perp hu huz`. Use `set a := aC k r z e u with ha`. Use `set N := nR k r z u with hN`. Use `set s := sC k r z e u with hs`.

Establish `ha' : herm (Hpk k r) u e = a` using `by rw [ha, aC, hp]`. Establish `hNn : 0 ≤ N` using `Real.sqrt_nonneg _`. Establish `hre : 0 ≤ (herm (Hpk k r) u u).re` using `perp_nonneg hz hzn hu huz`. Establish `hN2 : N ^ 2 = (herm (Hpk k r) u u).re` using `by rw [hN, nR, hp, Real.sq_sqrt hre]`. Establish `huu : herm (Hpk k r) u u = ((N ^ 2 : ℝ) : ℂ)` using `by rw [hN2]; exact herm_real u`.

Establish `hsa : star s * a = ((N * ‖a‖ : ℝ) : ℂ)`. Rewrite using `[hs, sC, ← ha]`. Use `split_ifs with h0`. Rewrite using `[h0]`. Simplify using the standard rewrite rules.

Establish `hn : (‖a‖ : ℂ) ≠ 0` using `by simpa using h0`. Simplify using `only [star_mul', star_div₀, Complex.star_def, Complex.conj_ofReal]`. Rewrite using `[← hN, show (N : ℂ) * ((starRingEnd ℂ) a / (‖a‖ : ℂ)) * a = (N : ℂ) * ((starRingEnd ℂ) a * a) / (‖a‖ : ℂ) by ring, Complex.conj_mul']`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Establish `hss : s * star s = ((N ^ 2 : ℝ) : ℂ)`. Rewrite using `[hs, sC, ← ha]`. Use `split_ifs with h0`. Rewrite using `[Complex.star_def, Complex.conj_ofReal]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hn : (‖a‖ : ℂ) ≠ 0` using `by simpa using h0`. Simplify using `only [star_mul', star_div₀, Complex.star_def, Complex.conj_ofReal]`. Rewrite using `[← hN, show (N : ℂ) * (a / (‖a‖ : ℂ)) * ((N : ℂ) * ((starRingEnd ℂ) a / (‖a‖ : ℂ))) = (N : ℂ) ^ 2 * (a * (starRingEnd ℂ) a) / (‖a‖ : ℂ) ^ 2 by ring, Complex.mul_conj']`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Establish `hea : s * herm (Hpk k r) e u = ((N * ‖a‖ : ℝ) : ℂ)`. Rewrite using `[hb_symm _ (hpk_herm k r) u e, ha']`. Establish `: s * star a = star (star s * a)` using `by rw [star_mul', star_star, mul_comm]`. Rewrite using `[this, hsa, Complex.star_def, Complex.conj_ofReal]`.

Establish `hv : vH k r z e u = u + (-s) • e` using `by rw [vH, hp, neg_smul, ← sub_eq_add_neg]`. Establish `hvv : herm (Hpk k r) (vH k r z e u) (vH k r z e u) = ((2 * (N ^ 2 - N * ‖a‖) : ℝ) : ℂ)`. Rewrite using `[hv, hb_expand, huu, ha', hee]`. Simplify using `only [star_neg, neg_mul, mul_neg, neg_neg, mul_one]`. Rewrite using `[hsa, hea, hss]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `huv : herm (Hpk k r) u (vH k r z e u) = ((N ^ 2 - N * ‖a‖ : ℝ) : ℂ)`. Rewrite using `[hv, hb_add_right, hb_smul_right, huu, ha', star_neg, neg_mul, hsa]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Unfold `hh`. Rewrite using `[hvv, Complex.ofReal_re]`. Use `split_ifs with h0`. Establish `hv0 : vH k r z e u = 0` using `perp_eq_zero hz hzn (vH_inWb hz he u) (vH_perp hzz hez u) (by rw [hvv, Complex.ofReal_re, h0])`.

Rewrite using `[one_mulVec]`. Use `hv0` as an intermediate fact. Rewrite `this` using `[vH, hp, sub_eq_zero]`. Conclude with `this`. Rewrite using `[Formalism.FourierDecayAlt.P.TwoByOneBlock.qrefl_mulVec, huv]`.

Establish `h1 : N ^ 2 - N * ‖a‖ ≠ 0` using `fun h => h0 (by rw [h, mul_zero])`. Establish `hc : ((-2 / (2 * (N ^ 2 - N * ‖a‖)) : ℝ) : ℂ) * ((N ^ 2 - N * ‖a‖ : ℝ) : ℂ) = -1`. Rewrite using `[← Complex.ofReal_mul]`. Establish `: -2 / (2 * (N ^ 2 - N * ‖a‖)) * (N ^ 2 - N * ‖a‖) = -1`. Establish `h2 : (2 : ℝ) * (N ^ 2 - N * ‖a‖) ≠ 0` using `mul_ne_zero two_ne_zero h1`.

Rewrite using `[div_mul_eq_mul_div, div_eq_iff h2]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hc, vH, hp]`. Simplify using `only [neg_smul, one_smul]`. Rewrite using `[← hs]`. Normalize the expressions using the abelian group laws.
-/
theorem hh_apply (hz : inWb k r z) (hzn : (herm (Hpk k r) z z).re < 0) (he : inWb k r e)
    (hez : herm (Hpk k r) e z = 0) (hee : herm (Hpk k r) e e = 1) {u : Fin (2 * r + k + 1) → ℂ}
    (hu : inWb k r u) (huz : herm (Hpk k r) u z = 0) : hh k r z e u *ᵥ u = sC k r z e u • e := by
  have hzz : herm (Hpk k r) z z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hzn; exact lt_irrefl _ hzn
  have hp : pW k r z u = u := Formalism.FourierDecayAlt.P.Dx2.DF.prW_perp hu huz
  set a := aC k r z e u with ha
  set N := nR k r z u with hN
  set s := sC k r z e u with hs
  have ha' : herm (Hpk k r) u e = a := by rw [ha, aC, hp]
  have hNn : 0 ≤ N := Real.sqrt_nonneg _
  have hre : 0 ≤ (herm (Hpk k r) u u).re := perp_nonneg hz hzn hu huz
  have hN2 : N ^ 2 = (herm (Hpk k r) u u).re := by rw [hN, nR, hp, Real.sq_sqrt hre]
  have huu : herm (Hpk k r) u u = ((N ^ 2 : ℝ) : ℂ) := by rw [hN2]; exact herm_real u
  have hsa : star s * a = ((N * ‖a‖ : ℝ) : ℂ) := by
    rw [hs, sC, ← ha]
    split_ifs with h0
    · rw [h0]; simp
    · have hn : (‖a‖ : ℂ) ≠ 0 := by simpa using h0
      simp only [star_mul', star_div₀, Complex.star_def, Complex.conj_ofReal]
      rw [← hN, show (N : ℂ) * ((starRingEnd ℂ) a / (‖a‖ : ℂ)) * a = (N : ℂ) * ((starRingEnd ℂ) a * a) / (‖a‖ : ℂ) by
        ring, Complex.conj_mul']
      push_cast
      field_simp
  have hss : s * star s = ((N ^ 2 : ℝ) : ℂ) := by
    rw [hs, sC, ← ha]
    split_ifs with h0
    · rw [Complex.star_def, Complex.conj_ofReal]; push_cast; ring
    · have hn : (‖a‖ : ℂ) ≠ 0 := by simpa using h0
      simp only [star_mul', star_div₀, Complex.star_def, Complex.conj_ofReal]
      rw [← hN, show (N : ℂ) * (a / (‖a‖ : ℂ)) * ((N : ℂ) * ((starRingEnd ℂ) a / (‖a‖ : ℂ))) =
        (N : ℂ) ^ 2 * (a * (starRingEnd ℂ) a) / (‖a‖ : ℂ) ^ 2 by ring, Complex.mul_conj']
      push_cast
      field_simp
  have hea : s * herm (Hpk k r) e u = ((N * ‖a‖ : ℝ) : ℂ) := by
    rw [hb_symm _ (hpk_herm k r) u e, ha']
    have : s * star a = star (star s * a) := by rw [star_mul', star_star, mul_comm]
    rw [this, hsa, Complex.star_def, Complex.conj_ofReal]
  have hv : vH k r z e u = u + (-s) • e := by rw [vH, hp, neg_smul, ← sub_eq_add_neg]
  have hvv : herm (Hpk k r) (vH k r z e u) (vH k r z e u) = ((2 * (N ^ 2 - N * ‖a‖) : ℝ) : ℂ) := by
    rw [hv, hb_expand, huu, ha', hee]
    simp only [star_neg, neg_mul, mul_neg, neg_neg, mul_one]
    rw [hsa, hea, hss]
    push_cast; ring
  have huv : herm (Hpk k r) u (vH k r z e u) = ((N ^ 2 - N * ‖a‖ : ℝ) : ℂ) := by
    rw [hv, hb_add_right, hb_smul_right, huu, ha', star_neg, neg_mul, hsa]
    push_cast; ring
  unfold hh
  rw [hvv, Complex.ofReal_re]
  split_ifs with h0
  · have hv0 : vH k r z e u = 0 := perp_eq_zero hz hzn (vH_inWb hz he u) (vH_perp hzz hez u)
      (by rw [hvv, Complex.ofReal_re, h0])
    rw [one_mulVec]
    have := hv0
    rw [vH, hp, sub_eq_zero] at this
    exact this
  · rw [Formalism.FourierDecayAlt.P.TwoByOneBlock.qrefl_mulVec, huv]
    have h1 : N ^ 2 - N * ‖a‖ ≠ 0 := fun h => h0 (by rw [h, mul_zero])
    have hc : ((-2 / (2 * (N ^ 2 - N * ‖a‖)) : ℝ) : ℂ) * ((N ^ 2 - N * ‖a‖ : ℝ) : ℂ) = -1 := by
      rw [← Complex.ofReal_mul]
      have : -2 / (2 * (N ^ 2 - N * ‖a‖)) * (N ^ 2 - N * ‖a‖) = -1 := by
        have h2 : (2 : ℝ) * (N ^ 2 - N * ‖a‖) ≠ 0 := mul_ne_zero two_ne_zero h1
        rw [div_mul_eq_mul_div, div_eq_iff h2]; ring
      rw [this]; push_cast; ring
    rw [hc, vH, hp]
    simp only [neg_smul, one_smul]
    rw [← hs]; abel

end apply

section meas

variable {k r : ℕ}

/- English proof (translation)
Unfold `herm`. Use `fun_prop`.
-/
theorem herm_cont : Continuous (fun q : (Fin (2 * r + k + 1) → ℂ) × (Fin (2 * r + k + 1) → ℂ) =>
    herm (Hpk k r) q.1 q.2) := by
  unfold herm; fun_prop

/- English proof (translation)
Set `L : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] (Fin (2 * r + k + 1) → ℂ)` to `{ toFun := pW k r z map_add' := fun v w => Formalism.FourierDecayAlt.P.Dx2.DF.prW_add z v w map_smul' := fun c v => Formalism.FourierDecayAlt.P.Dx2.DF.prW_smul z v c }`. Conclude with `L.continuous_of_finiteDimensional`.
-/
theorem pW_cont (z : Fin (2 * r + k + 1) → ℂ) : Continuous (pW k r z) := by
  let L : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] (Fin (2 * r + k + 1) → ℂ) :=
    { toFun := pW k r z
      map_add' := fun v w => Formalism.FourierDecayAlt.P.Dx2.DF.prW_add z v w
      map_smul' := fun c v => Formalism.FourierDecayAlt.P.Dx2.DF.prW_smul z v c }
  exact L.continuous_of_finiteDimensional

/- English proof (translation)
Establish `hp` using `pW_cont (k := k) (r := r) z`. Unfold `aC`. Conclude with `(herm_cont (k := k) (r := r)).comp (hp.prodMk continuous_const)`.
-/
theorem aC_cont (z e : Fin (2 * r + k + 1) → ℂ) : Continuous (aC k r z e) := by
  have hp := pW_cont (k := k) (r := r) z
  unfold aC
  exact (herm_cont (k := k) (r := r)).comp (hp.prodMk continuous_const)

/- English proof (translation)
Establish `hp` using `pW_cont (k := k) (r := r) z`. Unfold `nR`. Conclude with `Real.continuous_sqrt.comp (Complex.continuous_re.comp ((herm_cont (k := k) (r := r)).comp (hp.prodMk hp)))`.
-/
theorem nR_cont (z : Fin (2 * r + k + 1) → ℂ) : Continuous (nR k r z) := by
  have hp := pW_cont (k := k) (r := r) z
  unfold nR
  exact Real.continuous_sqrt.comp (Complex.continuous_re.comp ((herm_cont (k := k) (r := r)).comp (hp.prodMk hp)))

/- English proof (translation)
Establish `ha` using `aC_cont (k := k) (r := r) z e`. Establish `hn` using `nR_cont (k := k) (r := r) z`. Unfold `sC`. Conclude with `Measurable.ite (measurableSet_eq_fun ha.measurable measurable_const) (Complex.measurable_ofReal.comp hn.measurable) ((Complex.measurable_ofReal.comp hn.measurable).mul (ha.measurable.div (Complex.measurable_ofReal.comp ha.measurable.norm)))`.
-/
theorem sC_meas (z e : Fin (2 * r + k + 1) → ℂ) : Measurable (sC k r z e) := by
  have ha := aC_cont (k := k) (r := r) z e
  have hn := nR_cont (k := k) (r := r) z
  unfold sC
  exact Measurable.ite (measurableSet_eq_fun ha.measurable measurable_const)
    (Complex.measurable_ofReal.comp hn.measurable)
    ((Complex.measurable_ofReal.comp hn.measurable).mul
      (ha.measurable.div (Complex.measurable_ofReal.comp ha.measurable.norm)))

/- English proof (translation)
Establish `hp` using `pW_cont (k := k) (r := r) z`. Unfold `vH`. Conclude with `hp.measurable.sub ((sC_meas (k := k) (r := r) z e).smul_const e)`.
-/
theorem vH_meas (z e : Fin (2 * r + k + 1) → ℂ) : Measurable (vH k r z e) := by
  have hp := pW_cont (k := k) (r := r) z
  unfold vH
  exact hp.measurable.sub ((sC_meas (k := k) (r := r) z e).smul_const e)

/- English proof (translation)
Unfold `herm`. Use `fun_prop`.
-/
theorem hermSelf_cont : Continuous (fun x : Fin (2 * r + k + 1) → ℂ => herm (Hpk k r) x x) := by
  unfold herm; fun_prop

/- English proof (translation)
Use `fun_prop`.
-/
theorem vecH_cont (j : Fin (2 * r + k + 1)) :
    Continuous (fun x : Fin (2 * r + k + 1) → ℂ => (star x ᵥ* Hpk k r) j) := by
  fun_prop

/- English proof (translation)
The claim follows from `(Complex.continuous_re.comp (hermSelf_cont (k := k) (r := r))).measurable.comp (vH_meas (k := k) (r := r) z e)`.
-/
theorem R_meas (z e : Fin (2 * r + k + 1) → ℂ) :
    Measurable (fun u => (herm (Hpk k r) (vH k r z e u) (vH k r z e u)).re) :=
  (Complex.continuous_re.comp (hermSelf_cont (k := k) (r := r))).measurable.comp (vH_meas (k := k) (r := r) z e)

/- English proof (translation)
Establish `hv` using `vH_meas (k := k) (r := r) z e`. Establish `hR` using `R_meas (k := k) (r := r) z e`. Use `measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_` and prove the remaining obligations. Establish `e1 : (fun u => hh k r z e u i j) = fun u => if (herm (Hpk k r) (vH k r z e u) (vH k r z e u)).re = 0 then (1 : B.Mat k r) i j else (1 : B.Mat k r) i j + ((-2 / (herm (Hpk k r) (vH k r z e u) (vH k r z e u)).re : ℝ) : ℂ) * (vH k r z e u i * (star (vH k r z e u) ᵥ* Hpk k r) j)`. Use function extensionality and compare the values at `u`.

Unfold `hh`. Use `split_ifs`. Both sides reduce to the same expression. Simplify using `[Formalism.FourierDecayAlt.P.TwoByOneBlock.qrefl, Matrix.vecMulVec_apply]`. Rewrite using `[e1]`.

Conclude with `Measurable.ite (measurableSet_eq_fun hR measurable_const) measurable_const (measurable_const.add ((Complex.measurable_ofReal.comp (measurable_const.div hR)).mul (((measurable_pi_apply i).comp hv).mul ((vecH_cont (k := k) (r := r) j).measurable.comp hv))))`.
-/
theorem hh_meas (z e : Fin (2 * r + k + 1) → ℂ) : Measurable (hh k r z e) := by
  have hv := vH_meas (k := k) (r := r) z e
  have hR := R_meas (k := k) (r := r) z e
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  have e1 : (fun u => hh k r z e u i j) = fun u =>
      if (herm (Hpk k r) (vH k r z e u) (vH k r z e u)).re = 0 then (1 : B.Mat k r) i j
      else (1 : B.Mat k r) i j + ((-2 / (herm (Hpk k r) (vH k r z e u) (vH k r z e u)).re : ℝ) : ℂ) *
        (vH k r z e u i * (star (vH k r z e u) ᵥ* Hpk k r) j) := by
    funext u; unfold hh; split_ifs
    · rfl
    · simp [Formalism.FourierDecayAlt.P.TwoByOneBlock.qrefl, Matrix.vecMulVec_apply]
  rw [e1]
  exact Measurable.ite (measurableSet_eq_fun hR measurable_const) measurable_const
    (measurable_const.add ((Complex.measurable_ofReal.comp (measurable_const.div hR)).mul
      (((measurable_pi_apply i).comp hv).mul ((vecH_cont (k := k) (r := r) j).measurable.comp hv))))

end meas

/- English proof (translation)
Introduce `k r z e hz hzn he hez hee`. Establish `hzz : herm (Hpk k r) z z ≠ 0` using `fun h => by rw [h, Complex.zero_re] at hzn; exact lt_irrefl _ hzn`. Conclude with `⟨hh k r z e, hh_meas z e, hh_mem hz hzz he hez, fun u hu huz _ => ⟨sC k r z e u, hh_apply hz hzn he hez hee hu huz⟩⟩`.
-/
theorem householder_measurability_holds : HouseMeas := by
  intro k r z e hz hzn he hez hee
  have hzz : herm (Hpk k r) z z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hzn; exact lt_irrefl _ hzn
  exact ⟨hh k r z e, hh_meas z e, hh_mem hz hzz he hez, fun u hu huz _ =>
    ⟨sC k r z e u, hh_apply hz hzn he hez hee hu huz⟩⟩

end

end Formalism.FourierDecayAlt.P.CutBP.TNM.HM
