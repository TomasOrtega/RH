import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqLMat

noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.SquareSplitPairs

open Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Ker.Cd.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq Formalism.L2.Th1.H

variable {D : Car}

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem sum_three_comm {a b c : ℕ} (F : Fin a → Fin b → Fin c → ℂ) :
    ∑ i, ∑ j, ∑ k, F i j k = ∑ k, ∑ j, ∑ i, F i j k := by
  calc ∑ i, ∑ j, ∑ k, F i j k = ∑ i, ∑ k, ∑ j, F i j k :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, F i j k := Finset.sum_comm
    _ = ∑ k, ∑ j, ∑ i, F i j k := Finset.sum_congr rfl fun k _ => Finset.sum_comm

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem formV_apply' (A : ℝ) {N N' : ℕ} (z w : TaylorLogMetric.VC D N N') :
    Ker.formV A D.what₂.Tau N N' z w = (∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j)) / (A : ℂ) := rfl

/- English proof (translation)
Rewrite using `[formV_apply', formV_apply']`. Use `congr 1`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Simplify using `only [phi_apply, Matrix.conjTranspose_apply, Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.embT_star', Complex.star_def, map_sum, map_mul, Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]`. Use `(sum_three_comm _).trans ?_` and prove the remaining obligations.

Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem formV_phi {N N' : ℕ} (A : ℝ) (M : Matrix (Fin N') (Fin N') D.host.E) (x y : TaylorLogMetric.VC D N N') :
    Ker.formV A D.what₂.Tau N N' (phi M x) y =
      Ker.formV A D.what₂.Tau N N' x (phi (letI := D.host.cmStar; Mᴴ) y) := by
  rw [formV_apply', formV_apply']
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [phi_apply, Matrix.conjTranspose_apply, Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.embT_star', Complex.star_def, map_sum,
    map_mul, Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
  refine (sum_three_comm _).trans ?_
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
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
Use `letI := D.host.cmStar`. Establish `h1 : ∀ a b : TaylorLogMetric.VC D N N', HH D cc δ N N' (phi e a) (phi e b) = HH D cc δ N N' a (phi (eᴴ * e) b)`. Introduce `a b`. Simplify using `only [HH]`. Rewrite using `[formV_phi, ← phi_mul]`.

Establish `h2 : ∀ a b : TaylorLogMetric.VC D N N', HH D cc δ N N' (phi (eᴴ * e) a) b = HH D cc δ N N' a (phi (eᴴ * e) b)`. Introduce `a b`. Simplify using `only [HH]`. Rewrite using `[formV_phi, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]`. Use `show cp D cc δ N N' (phi e x) (phi e y) - (HH D cc δ N N' (phi e x) (phi e y)).im = cp D cc δ N N' x (phi (eᴴ * e) y) - (HH D cc δ N N' x (phi (eᴴ * e) y)).im`.

Simplify using `only [cp, h1, h2]`.
-/
theorem bet_phi (e : Matrix (Fin N') (Fin N') D.host.E) (x y : TaylorLogMetric.VC D N N') :
    bet D cc δ N N' (phi e x) (phi e y) = bet D cc δ N N' x (phi (letI := D.host.cmStar; eᴴ * e) y) := by
  letI := D.host.cmStar
  have h1 : ∀ a b : TaylorLogMetric.VC D N N', HH D cc δ N N' (phi e a) (phi e b) = HH D cc δ N N' a (phi (eᴴ * e) b) := by
    intro a b
    simp only [HH]
    rw [formV_phi, ← phi_mul]
  have h2 : ∀ a b : TaylorLogMetric.VC D N N', HH D cc δ N N' (phi (eᴴ * e) a) b = HH D cc δ N N' a (phi (eᴴ * e) b) := by
    intro a b
    simp only [HH]
    rw [formV_phi, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  show cp D cc δ N N' (phi e x) (phi e y) - (HH D cc δ N N' (phi e x) (phi e y)).im =
    cp D cc δ N N' x (phi (eᴴ * e) y) - (HH D cc δ N N' x (phi (eᴴ * e) y)).im
  simp only [cp, h1, h2]

/- English proof (translation)
Rewrite using `[← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem negpow (b : ℤ) : ((-1 : ℂ) ^ b) = Complex.exp ((Real.pi : ℂ) * Complex.I * (b : ℂ)) := by
  rw [← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
  congr 1
  ring

/- English proof (translation)
Establish `h' : Real.sqrt D.host.d / 2 * (TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) z z).re = m` using `h`. Unfold `TaylorLogMetric.al`. Rewrite using `[h', round_intCast]`.
-/
theorem al_of_q {z : TaylorLogMetric.VC D N N'} {m : ℤ} (h : qq D cc δ N N' z = m) : TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) z = (-1 : ℂ) ^ m := by
  have h' : Real.sqrt D.host.d / 2 * (TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) z z).re = m := h
  unfold TaylorLogMetric.al
  rw [h', round_intCast]

/- English proof (translation)
Take `⟨n, hn⟩` from `Complex.exp_eq_exp_iff_exists_int.mp h`. Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `h2 : ((a : ℂ) - b - 2 * n) * ((Real.pi : ℂ) * Complex.I) = 0`. Take the linear combination `hn`. Establish `hpi : (Real.pi : ℂ) * Complex.I ≠ 0` using `mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) Complex.I_ne_zero`.

Establish `h3` using `(mul_eq_zero.mp h2).resolve_right hpi`. Establish `h4 : ((a - b - 2 * n : ℝ) : ℂ) = 0` using `by push_cast; exact h3`. Establish `h5` using `Complex.ofReal_eq_zero.mp h4`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem exists_int_eq_add_two_mul_of_exp_eq {a b : ℝ}
    (h : Complex.exp ((Real.pi : ℂ) * Complex.I * (a : ℂ)) = Complex.exp ((Real.pi : ℂ) * Complex.I * (b : ℂ))) :
    ∃ n : ℤ, a = b + 2 * n := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  refine ⟨n, ?_⟩
  have h2 : ((a : ℂ) - b - 2 * n) * ((Real.pi : ℂ) * Complex.I) = 0 := by
    linear_combination hn
  have hpi : (Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) Complex.I_ne_zero
  have h3 := (mul_eq_zero.mp h2).resolve_right hpi
  have h4 : ((a - b - 2 * n : ℝ) : ℂ) = 0 := by push_cast; exact h3
  have h5 := Complex.ofReal_eq_zero.mp h4
  linarith

/- English proof (translation)
Establish `h` using `qq_add (cc := cc) (δ := δ) x y`. Rewrite `h` using `[hxy, hx, hy]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem cp_eq_qq_add_sub {x y : TaylorLogMetric.VC D N N'} {mx my mxy : ℤ} (hx : qq D cc δ N N' x = mx)
    (hy : qq D cc δ N N' y = my) (hxy : qq D cc δ N N' (x + y) = mxy) :
    cp D cc δ N N' x y = (mxy : ℝ) - mx - my := by
  have h := qq_add (cc := cc) (δ := δ) x y
  rw [hxy, hx, hy] at h
  linarith

/- English proof (translation)
Establish `hc` using `cp_eq_qq_add_sub hx hy hxy`. Rewrite `hlaw` using `[al_of_q hxy, al_of_q hx, al_of_q hy]`. Establish `hpow : ((-1 : ℂ) ^ mxy) = (-1 : ℂ) ^ mx * (-1 : ℂ) ^ my * (-1 : ℂ) ^ (mxy - mx - my)`. Rewrite using `[mul_assoc, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `hlaw` using `[hpow]`. Establish `hne : ((-1 : ℂ) ^ mx * (-1 : ℂ) ^ my) ≠ 0`. Apply the tactic sequence `apply mul_ne_zero <;> exact zpow_ne_zero _ (by norm_num)`. Establish `he` using `mul_left_cancel₀ hne hlaw`.

Rewrite `he` using `[negpow]`. Take `⟨n, hn⟩` from `exists_int_eq_add_two_mul_of_exp_eq (a := altE (HH D cc δ N N') x y) (b := (mxy : ℝ) - mx - my) (by`. Rewrite using `[← he]`. Use `push_cast`. Use the proof step `ring_nf)`.

Use `⟨-n, ?_⟩` and prove the remaining obligations. Use `show cp D cc δ N N' x y - (HH D cc δ N N' x y).im = 2 * ((-n : ℤ) : ℝ)`. Simplify using `only [altE] at hn`. Rewrite using `[hc]`. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem good_of_law {x y : TaylorLogMetric.VC D N N'} {mx my mxy : ℤ} (hx : qq D cc δ N N' x = mx) (hy : qq D cc δ N N' y = my)
    (hxy : qq D cc δ N N' (x + y) = mxy)
    (hlaw : TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) (x + y) = TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) x * TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) y *
      Complex.exp ((Real.pi : ℂ) * Complex.I * (altE (HH D cc δ N N') x y : ℂ))) :
    Good D cc δ N N' x y := by
  have hc := cp_eq_qq_add_sub hx hy hxy
  rw [al_of_q hxy, al_of_q hx, al_of_q hy] at hlaw
  have hpow : ((-1 : ℂ) ^ mxy) = (-1 : ℂ) ^ mx * (-1 : ℂ) ^ my * (-1 : ℂ) ^ (mxy - mx - my) := by
    rw [mul_assoc, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    congr 1
    ring
  rw [hpow] at hlaw
  have hne : ((-1 : ℂ) ^ mx * (-1 : ℂ) ^ my) ≠ 0 := by
    apply mul_ne_zero <;> exact zpow_ne_zero _ (by norm_num)
  have he := mul_left_cancel₀ hne hlaw
  rw [negpow] at he
  obtain ⟨n, hn⟩ := exists_int_eq_add_two_mul_of_exp_eq (a := altE (HH D cc δ N N') x y) (b := (mxy : ℝ) - mx - my) (by
    rw [← he]
    push_cast
    ring_nf)
  refine ⟨-n, ?_⟩
  show cp D cc δ N N' x y - (HH D cc δ N N' x y).im = 2 * ((-n : ℤ) : ℝ)
  simp only [altE] at hn
  rw [hc]
  push_cast
  linarith

/- English proof (translation)
Establish `hc` using `cp_eq_qq_add_sub hx hy hxy`. Take `⟨k, hk⟩` from `hg`. Establish `hA0 : altE (HH D cc δ N N') x y = (mxy : ℝ) - mx - my - 2 * k`. Simplify using `only [bet] at hk`. Simplify using `only [altE]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hA : ((altE (HH D cc δ N N') x y : ℝ) : ℂ) = ((mxy - mx - my - 2 * k : ℤ) : ℂ)`. Rewrite using `[hA0]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[al_of_q hxy, al_of_q hx, al_of_q hy, hA, ← negpow, mul_assoc, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]`. Establish `he : mx + (my + (mxy - mx - my - 2 * k)) = mxy + 2 * (-k)` using `by ring`. Rewrite using `[he, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), _root_.zpow_mul]`. Evaluate the numerical expressions.
-/
theorem law_of_good {x y : TaylorLogMetric.VC D N N'} {mx my mxy : ℤ} (hx : qq D cc δ N N' x = mx) (hy : qq D cc δ N N' y = my)
    (hxy : qq D cc δ N N' (x + y) = mxy) (hg : Good D cc δ N N' x y) :
    TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) (x + y) = TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) x * TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) y *
      Complex.exp ((Real.pi : ℂ) * Complex.I * (altE (HH D cc δ N N') x y : ℂ)) := by
  have hc := cp_eq_qq_add_sub hx hy hxy
  obtain ⟨k, hk⟩ := hg
  have hA0 : altE (HH D cc δ N N') x y = (mxy : ℝ) - mx - my - 2 * k := by
    simp only [bet] at hk
    simp only [altE]
    linarith
  have hA : ((altE (HH D cc δ N N') x y : ℝ) : ℂ) = ((mxy - mx - my - 2 * k : ℤ) : ℂ) := by
    rw [hA0]
    push_cast
    ring
  rw [al_of_q hxy, al_of_q hx, al_of_q hy, hA, ← negpow, mul_assoc,
    ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  have he : mx + (my + (mxy - mx - my - 2 * k)) = mxy + 2 * (-k) := by ring
  rw [he, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), _root_.zpow_mul]
  norm_num

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

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.SquareSplitPairs
