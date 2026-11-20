import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SquareSplitPairs.HomLMulPres

noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.PairingIndexBounds.Eq.SquareSplitPairs

open Formalism.MainNotions Formalism.L2.PairingIndexBounds.Eq Formalism.L2.Th1.H

variable {D : D7}

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem sum_three_comm {a b c : ℕ} (F : Fin a → Fin b → Fin c → ℂ) :
    ∑ i, ∑ j, ∑ k, F i j k = ∑ k, ∑ j, ∑ i, F i j k := by
  calc ∑ i, ∑ j, ∑ k, F i j k = ∑ i, ∑ k, ∑ j, F i j k := Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, F i j k := Finset.sum_comm
    _ = ∑ k, ∑ j, ∑ i, F i j k := Finset.sum_congr rfl fun k _ => Finset.sum_comm

/- English proof (translation)
Set `_` to `D.host.cmStar`. Simplify using `only [Ker.formV, LinearMap.mk₂'ₛₗ_apply, phi_apply]`. Use `congr 1`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Simplify using `only [Finset.sum_mul, map_sum, map_mul, Finset.mul_sum, conjTranspose_apply, embT_star']`.

Rewrite using `[sum_three_comm]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [starRingEnd_apply, star_star]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem formV_phi {N N' : ℕ} (A : ℝ) (M : Matrix (Fin N') (Fin N') D.host.E) (x y : TaylorLogMetric.VC D N N') :
    Ker.formV A D.what₂.Tau N N' (phi M x) y =
      Ker.formV A D.what₂.Tau N N' x (phi (letI := D.host.cmStar; Mᴴ) y) := by
  let _ := D.host.cmStar
  simp only [Ker.formV, LinearMap.mk₂'ₛₗ_apply, phi_apply]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [Finset.sum_mul, map_sum, map_mul, Finset.mul_sum, conjTranspose_apply, embT_star']
  rw [sum_three_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [starRingEnd_apply, star_star]
  ring

variable (D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ)

def HH : Sesq (TaylorLogMetric.VC D N N') := Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N'

def qq (x : TaylorLogMetric.VC D N N') : ℝ := Real.sqrt D.host.d / 2 * (HH D cc δ N N' x x).re

def cp (x y : TaylorLogMetric.VC D N N') : ℝ :=
  Real.sqrt D.host.d / 2 * ((HH D cc δ N N' x y).re + (HH D cc δ N N' y x).re)

def bet (x y : TaylorLogMetric.VC D N N') : ℝ := cp D cc δ N N' x y - (HH D cc δ N N' x y).im

def Good (x y : TaylorLogMetric.VC D N N') : Prop := ∃ k : ℤ, bet D cc δ N N' x y = 2 * k

variable {D cc δ N N'}

/- English proof (translation)
Simplify using `only [qq, cp, map_add, LinearMap.add_apply, Complex.add_re]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem qq_add (x y : TaylorLogMetric.VC D N N') :
    qq D cc δ N N' (x + y) = qq D cc δ N N' x + qq D cc δ N N' y + cp D cc δ N N' x y := by
  simp only [qq, cp, map_add, LinearMap.add_apply, Complex.add_re]
  ring

/- English proof (translation)
Simplify using `only [bet, cp, map_add, LinearMap.add_apply, Complex.add_re, Complex.add_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem bet_add_left (x x' y : TaylorLogMetric.VC D N N') :
    bet D cc δ N N' (x + x') y = bet D cc δ N N' x y + bet D cc δ N N' x' y := by
  simp only [bet, cp, map_add, LinearMap.add_apply, Complex.add_re, Complex.add_im]
  ring

/- English proof (translation)
Simplify using `only [bet, cp, map_add, LinearMap.add_apply, Complex.add_re, Complex.add_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem bet_add_right (x y y' : TaylorLogMetric.VC D N N') :
    bet D cc δ N N' x (y + y') = bet D cc δ N N' x y + bet D cc δ N N' x y' := by
  simp only [bet, cp, map_add, LinearMap.add_apply, Complex.add_re, Complex.add_im]
  ring

/- English proof (translation)
Take `⟨m, hm⟩` from `ha`. Take `⟨m', hm'⟩` from `hb`. Use `⟨m + m', ?_⟩` and prove the remaining obligations. Rewrite using `[hm, hm']`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem good_add {a b : ℝ} (ha : ∃ k : ℤ, a = 2 * k) (hb : ∃ k : ℤ, b = 2 * k) : ∃ k : ℤ, a + b = 2 * k := by
  obtain ⟨m, hm⟩ := ha
  obtain ⟨m', hm'⟩ := hb
  refine ⟨m + m', ?_⟩
  rw [hm, hm']
  push_cast
  ring

/- English proof (translation)
Use `letI := D.host.cmStar`. Establish `h1 : HH D cc δ N N' (phi e x) (phi e y) = HH D cc δ N N' x (phi (eᴴ * e) y)`. Unfold `HH`. Rewrite using `[formV_phi, phi_mul]`. Establish `h2 : HH D cc δ N N' (phi e y) (phi e x) = HH D cc δ N N' (phi (eᴴ * e) y) x`.

Unfold `HH`. Rewrite using `[formV_phi, formV_phi, ← phi_mul, conjTranspose_mul, conjTranspose_conjTranspose]`. Unfold `bet cp`. Rewrite using `[h1, h2]`.
-/
theorem bet_phi (e : Matrix (Fin N') (Fin N') D.host.E) (x y : TaylorLogMetric.VC D N N') :
    bet D cc δ N N' (phi e x) (phi e y) = bet D cc δ N N' x (phi (letI := D.host.cmStar; eᴴ * e) y) := by
  letI := D.host.cmStar
  have h1 : HH D cc δ N N' (phi e x) (phi e y) = HH D cc δ N N' x (phi (eᴴ * e) y) := by
    unfold HH
    rw [formV_phi, phi_mul]
  have h2 : HH D cc δ N N' (phi e y) (phi e x) = HH D cc δ N N' (phi (eᴴ * e) y) x := by
    unfold HH
    rw [formV_phi, formV_phi, ← phi_mul, conjTranspose_mul, conjTranspose_conjTranspose]
  unfold bet cp
  rw [h1, h2]

/- English proof (translation)
Rewrite using `[show (Real.pi : ℂ) * Complex.I * (b : ℂ) = (b : ℂ) * ((Real.pi : ℂ) * Complex.I) by ring, Complex.exp_int_mul, Complex.exp_pi_mul_I]`.
-/
theorem negpow (b : ℤ) : ((-1 : ℂ) ^ b) = Complex.exp ((Real.pi : ℂ) * Complex.I * (b : ℂ)) := by
  rw [show (Real.pi : ℂ) * Complex.I * (b : ℂ) = (b : ℂ) * ((Real.pi : ℂ) * Complex.I) by ring,
    Complex.exp_int_mul, Complex.exp_pi_mul_I]

/- English proof (translation)
Use `show (-1 : ℂ) ^ (round (qq D cc δ N N' z)) = _`. Rewrite using `[h, round_intCast]`.
-/
theorem al_of_q {z : TaylorLogMetric.VC D N N'} {m : ℤ} (h : qq D cc δ N N' z = m) : TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) z = (-1 : ℂ) ^ m := by
  show (-1 : ℂ) ^ (round (qq D cc δ N N' z)) = _
  rw [h, round_intCast]

/- English proof (translation)
Rewrite `hlaw` using `[al_of_q hxy, al_of_q hx, al_of_q hy, negpow, negpow, negpow, ← Complex.exp_add, ← Complex.exp_add]`. Take `⟨n, hn⟩` from `Complex.exp_eq_exp_iff_exists_int.mp hlaw`. Establish `hq` using `qq_add (D := D) (cc := cc) (δ := δ) x y`. Rewrite `hq` using `[hx, hy, hxy]`. Use `⟨n, ?_⟩` and prove the remaining obligations.

Establish `hpi : (Real.pi : ℂ) * Complex.I ≠ 0` using `mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) Complex.I_ne_zero`. Establish `h2 : (mxy : ℂ) = mx + my + (altE (HH D cc δ N N') x y : ℂ) + 2 * n`. Apply `mul_left_cancel₀ hpi` to reduce the goal to its premises. Take the linear combination `hn`. Establish `h3 : (mxy : ℝ) = mx + my + altE (HH D cc δ N N') x y + 2 * n`.

Conclude with `h2` after adjusting the coercions. Simplify using `only [bet, altE] at h3 ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem good_of_law {x y : TaylorLogMetric.VC D N N'} {mx my mxy : ℤ} (hx : qq D cc δ N N' x = mx) (hy : qq D cc δ N N' y = my)
    (hxy : qq D cc δ N N' (x + y) = mxy)
    (hlaw : TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) (x + y) = TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) x * TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) y *
      Complex.exp ((Real.pi : ℂ) * Complex.I * (altE (HH D cc δ N N') x y : ℂ))) :
    Good D cc δ N N' x y := by
  rw [al_of_q hxy, al_of_q hx, al_of_q hy, negpow, negpow, negpow, ← Complex.exp_add,
    ← Complex.exp_add] at hlaw
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hlaw
  have hq := qq_add (D := D) (cc := cc) (δ := δ) x y
  rw [hx, hy, hxy] at hq
  refine ⟨n, ?_⟩
  have hpi : (Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) Complex.I_ne_zero
  have h2 : (mxy : ℂ) = mx + my + (altE (HH D cc δ N N') x y : ℂ) + 2 * n := by
    apply mul_left_cancel₀ hpi
    linear_combination hn
  have h3 : (mxy : ℝ) = mx + my + altE (HH D cc δ N N') x y + 2 * n := by
    exact_mod_cast h2
  simp only [bet, altE] at h3 ⊢
  linarith

/- English proof (translation)
Take `⟨k, hk⟩` from `hg`. Rewrite using `[al_of_q hxy, al_of_q hx, al_of_q hy, negpow, negpow, negpow, ← Complex.exp_add, ← Complex.exp_add]`. Apply `Complex.exp_eq_exp_iff_exists_int.mpr` to reduce the goal to its premises. Use `⟨k, ?_⟩` and prove the remaining obligations. Establish `hq` using `qq_add (D := D) (cc := cc) (δ := δ) x y`.

Rewrite `hq` using `[hx, hy, hxy]`. Simplify using `only [bet] at hk`. Establish `h4 : (mxy : ℝ) = mx + my + altE (HH D cc δ N N') x y + 2 * k`. Simplify using `only [altE]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h5 : (mxy : ℂ) = mx + my + (altE (HH D cc δ N N') x y : ℂ) + 2 * k`. Conclude with `h4` after adjusting the coercions. Rewrite using `[h5]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem law_of_good {x y : TaylorLogMetric.VC D N N'} {mx my mxy : ℤ} (hx : qq D cc δ N N' x = mx) (hy : qq D cc δ N N' y = my)
    (hxy : qq D cc δ N N' (x + y) = mxy) (hg : Good D cc δ N N' x y) :
    TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) (x + y) = TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) x * TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) y *
      Complex.exp ((Real.pi : ℂ) * Complex.I * (altE (HH D cc δ N N') x y : ℂ)) := by
  obtain ⟨k, hk⟩ := hg
  rw [al_of_q hxy, al_of_q hx, al_of_q hy, negpow, negpow, negpow, ← Complex.exp_add,
    ← Complex.exp_add]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨k, ?_⟩
  have hq := qq_add (D := D) (cc := cc) (δ := δ) x y
  rw [hx, hy, hxy] at hq
  simp only [bet] at hk
  have h4 : (mxy : ℝ) = mx + my + altE (HH D cc δ N N') x y + 2 * k := by
    simp only [altE]
    linarith
  have h5 : (mxy : ℂ) = mx + my + (altE (HH D cc δ N N') x y : ℂ) + 2 * k := by
    exact_mod_cast h4
  rw [h5]
  ring

/- English proof (translation)
Take `⟨mx, hmx⟩` from `hq x hx`. Take `⟨my, hmy⟩` from `hq y hy`. Take `⟨mxy, hmxy⟩` from `hq (x + y) (Y.add_mem hx hy)`. Conclude with `good_of_law hmx hmy hmxy (hsc.2 x hx y hy)`.
-/
theorem good_of_lat {Y : AddSubgroup (TaylorLogMetric.VC D N N')} (hsc : IsSemiChar (HH D cc δ N N') Y (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ)))
    (hq : ∀ z ∈ Y, ∃ m : ℤ, qq D cc δ N N' z = m) {x y : TaylorLogMetric.VC D N N'} (hx : x ∈ Y) (hy : y ∈ Y) :
    Good D cc δ N N' x y := by
  obtain ⟨mx, hmx⟩ := hq x hx
  obtain ⟨my, hmy⟩ := hq y hy
  obtain ⟨mxy, hmxy⟩ := hq (x + y) (Y.add_mem hx hy)
  exact good_of_law hmx hmy hmxy (hsc.2 x hx y hy)

end Formalism.L2.PairingIndexBounds.Eq.SquareSplitPairs
