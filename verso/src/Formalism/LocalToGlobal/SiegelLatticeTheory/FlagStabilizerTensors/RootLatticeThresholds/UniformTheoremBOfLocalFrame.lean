import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BesselExpansion
import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceExpansion

noncomputable section

namespace Formalism.L2.SG.Pf.BesselExpansion

open MeasureTheory Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.BesselShellMomentBounds Formalism.MainNotions.RotatedPoints Formalism.MainNotions.S.Pv.Frames

section Fr

variable (D : D7)

def PlaceOK1 (Ch Cg b dist dinf : ℝ) (v : D.what₂.Tau) (L : LocBessel D.R.k D.R.rS)
    (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) : Prop :=
  LocOk D Ch Cg L (lamSH D.R (D.hc v)) (kaRe D) b 1 ∧ l1 L.lam (lamSH D.R (D.hc v)) ≤ dist ∧
    (∀ s, |L.lam s - lamSH D.R (D.hc v) s| ≤ dinf) ∧ IsKFinCoefH L.σ f ∧ IsSection D.R.k D.R.rS L.z L.z' μsec

def BpLoc1 (Ch Cg dist dinf : ℝ) (A : ℕ) (C : ℝ) (e : ℕ) : Prop :=
  ∀ (b : ℝ) (v : D.what₂.Tau) (L : LocBessel D.R.k D.R.rS) (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ), PlaceOK1 D Ch Cg b dist dinf v L f μsec →
    ∀ p : Point ℂ (D.R.rS + 1), Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') p ≠ 0 →
      ENNReal.ofReal (ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') p) * orbSq L f p ≤
        ENNReal.ofReal (b ^ (C * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ e) *
          max 1 (1 / Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') p) ^ A) * jNorm2 L f μsec

variable {D}

/- English proof (translation)
Introduce `a b hab`. Establish `h1` using `hg a b hab`. Establish `e1 : |lam a - lam' a| ≤ d` using `by rw [abs_sub_comm]; exact hd a`. Establish `e2` using `hd b`. Establish `key : |lam a - lam b| ≤ |lam a - lam' a| + |lam' a - lam' b| + |lam' b - lam b|`.

Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gap_transfer {n : ℕ} {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {h d : ℝ} (hg : GapAtLeast ε lam h)
    (hd : ∀ s, |lam' s - lam s| ≤ d) : GapAtLeast ε lam' (h - 2 * d) := by
  intro a b hab
  have h1 := hg a b hab
  have e1 : |lam a - lam' a| ≤ d := by rw [abs_sub_comm]; exact hd a
  have e2 := hd b
  have key : |lam a - lam b| ≤ |lam a - lam' a| + |lam' a - lam' b| + |lam' b - lam b| := by
    calc |lam a - lam b| = |(lam a - lam' a) + (lam' a - lam' b) + (lam' b - lam b)| := by ring_nf
      _ ≤ |lam a - lam' a| + |lam' a - lam' b| + |lam' b - lam b| := abs_add_three _ _ _
  linarith

/- English proof (translation)
Introduce `a b hab` and use `hh.trans (hg a b hab)`.
-/
theorem gap_mono {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {h h' : ℝ} (hg : GapAtLeast ε lam h) (hh : h' ≤ h) :
    GapAtLeast ε lam h' := fun a b hab => hh.trans (hg a b hab)

/- English proof (translation)
Use `set M : ℝ := ((2 * r + 2 : ℕ) : ℝ) with hM`. Establish `hM1 : 1 ≤ M` using `by rw [hM]; norm_cast; omega`. Establish `hCA0 : 0 ≤ CA`. Assume the negation of the conclusion as `hneg`. Use `push_neg at hneg`.

Establish `: CA * M ^ 2 < 0` using `mul_neg_of_neg_of_pos hneg (by positivity)`. Establish `h0 : (0 : ℝ) ≤ A` using `Nat.cast_nonneg A`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[← Real.rpow_natCast (b ^ (x * M ^ 2)) A, ← Real.rpow_mul (by linarith)]`. Apply `Real.rpow_le_rpow_of_exponent_le hb` to reduce the goal to its premises.

Establish `h4 : M ^ 4 ≤ M ^ e` using `pow_le_pow_right₀ hM1 he`. Establish `hxM : 0 ≤ x * M ^ 2` using `mul_nonneg hx (by positivity)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem pow_cost {b x CA : ℝ} {A e r : ℕ} (hb : 1 ≤ b) (hx : 0 ≤ x) (he : 4 ≤ e)
    (hA : (A : ℝ) ≤ CA * ((2 * r + 2 : ℕ) : ℝ) ^ 2) :
    (b ^ (x * ((2 * r + 2 : ℕ) : ℝ) ^ 2)) ^ A ≤ b ^ (x * CA * ((2 * r + 2 : ℕ) : ℝ) ^ e) := by
  set M : ℝ := ((2 * r + 2 : ℕ) : ℝ) with hM
  have hM1 : 1 ≤ M := by rw [hM]; norm_cast; omega
  have hCA0 : 0 ≤ CA := by
    by_contra hneg
    push_neg at hneg
    have : CA * M ^ 2 < 0 := mul_neg_of_neg_of_pos hneg (by positivity)
    have h0 : (0 : ℝ) ≤ A := Nat.cast_nonneg A
    linarith
  rw [← Real.rpow_natCast (b ^ (x * M ^ 2)) A, ← Real.rpow_mul (by linarith)]
  apply Real.rpow_le_rpow_of_exponent_le hb
  have h4 : M ^ 4 ≤ M ^ e := pow_le_pow_right₀ hM1 he
  have hxM : 0 ≤ x * M ^ 2 := mul_nonneg hx (by positivity)
  calc x * M ^ 2 * (A : ℝ) ≤ x * M ^ 2 * (CA * M ^ 2) := mul_le_mul_of_nonneg_left hA hxM
    _ = x * CA * M ^ 4 := by ring
    _ ≤ x * CA * M ^ e := mul_le_mul_of_nonneg_left h4 (mul_nonneg hx hCA0)

/- English proof (translation)
Use `set M : ℝ := ((2 * r + 2 : ℕ) : ℝ) with hM`. Establish `hM1 : 1 ≤ M` using `by rw [hM]; norm_cast; omega`. Establish `hrM : (r : ℝ) ≤ M` using `by rw [hM]; norm_cast; omega`. Establish `hb0 : 0 < b` using `by linarith`. Establish `hX : max ka⁻¹ ka⁻¹⁻¹ ≤ b ^ Ch`.

Rewrite using `[inv_inv]`. Conclude with `max_le hk2 hk1`. Establish `hX0 : 0 ≤ max ka⁻¹ ka⁻¹⁻¹` using `le_max_of_le_left (inv_nonneg.2 hka.le)`. Establish `hY : max (ka ^ r) (ka ^ r)⁻¹ ≤ b ^ (Ch * r)`. Rewrite using `[Real.rpow_mul hb0.le, Real.rpow_natCast]`.

Use `max_le (pow_le_pow_left₀ hka.le hk1 r) ?_` and prove the remaining obligations. Rewrite using `[← inv_pow]`. Conclude with `pow_le_pow_left₀ (inv_nonneg.2 hka.le) hk2 r`. Establish `hY0 : 0 ≤ max (ka ^ r) (ka ^ r)⁻¹` using `le_max_of_le_left (pow_nonneg hka.le r)`. Establish `e1 : max ka⁻¹ ka⁻¹⁻¹ ^ (Cf * M ^ 2) ≤ b ^ (Ch * (Cf * M ^ 2))`.

Rewrite using `[Real.rpow_mul hb0.le]`. Conclude with `Real.rpow_le_rpow hX0 hX (mul_nonneg hCf (by positivity))`. Establish `e2 : max (ka ^ r) (ka ^ r)⁻¹ ^ (Cf * M) ≤ b ^ (Ch * r * (Cf * M))`. Rewrite using `[Real.rpow_mul hb0.le]`. Conclude with `Real.rpow_le_rpow hY0 hY (mul_nonneg hCf (by linarith))`.

Combine the equalities or inequalities in the displayed calculation. Apply `Real.rpow_le_rpow_of_exponent_le hb` to reduce the goal to its premises. Establish `h2 : M ^ 2 ≤ M ^ e` using `pow_le_pow_right₀ hM1 he`. Establish `h3 : (r : ℝ) * M ≤ M ^ 2` using `by nlinarith`. Establish `hCC : 0 ≤ Ch * Cf` using `mul_nonneg hCh hCf`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h2 hCC, mul_le_mul_of_nonneg_left h3 hCC]`.
-/
theorem frames_factor_le {b ka Ch Cf : ℝ} {e r : ℕ} (hb : 1 ≤ b) (hka : 0 < ka) (hk1 : ka ≤ b ^ Ch)
    (hk2 : ka⁻¹ ≤ b ^ Ch) (hCh : 0 ≤ Ch) (hCf : 0 ≤ Cf) (he : 2 ≤ e) :
    max ka⁻¹ ka⁻¹⁻¹ ^ (Cf * ((2 * r + 2 : ℕ) : ℝ) ^ 2) * max (ka ^ r) (ka ^ r)⁻¹ ^ (Cf * ((2 * r + 2 : ℕ) : ℝ)) ≤
      b ^ (2 * Ch * Cf * ((2 * r + 2 : ℕ) : ℝ) ^ e) := by
  set M : ℝ := ((2 * r + 2 : ℕ) : ℝ) with hM
  have hM1 : 1 ≤ M := by rw [hM]; norm_cast; omega
  have hrM : (r : ℝ) ≤ M := by rw [hM]; norm_cast; omega
  have hb0 : 0 < b := by linarith
  have hX : max ka⁻¹ ka⁻¹⁻¹ ≤ b ^ Ch := by
    rw [inv_inv]
    exact max_le hk2 hk1
  have hX0 : 0 ≤ max ka⁻¹ ka⁻¹⁻¹ := le_max_of_le_left (inv_nonneg.2 hka.le)
  have hY : max (ka ^ r) (ka ^ r)⁻¹ ≤ b ^ (Ch * r) := by
    rw [Real.rpow_mul hb0.le, Real.rpow_natCast]
    refine max_le (pow_le_pow_left₀ hka.le hk1 r) ?_
    rw [← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.2 hka.le) hk2 r
  have hY0 : 0 ≤ max (ka ^ r) (ka ^ r)⁻¹ := le_max_of_le_left (pow_nonneg hka.le r)
  have e1 : max ka⁻¹ ka⁻¹⁻¹ ^ (Cf * M ^ 2) ≤ b ^ (Ch * (Cf * M ^ 2)) := by
    rw [Real.rpow_mul hb0.le]
    exact Real.rpow_le_rpow hX0 hX (mul_nonneg hCf (by positivity))
  have e2 : max (ka ^ r) (ka ^ r)⁻¹ ^ (Cf * M) ≤ b ^ (Ch * r * (Cf * M)) := by
    rw [Real.rpow_mul hb0.le]
    exact Real.rpow_le_rpow hY0 hY (mul_nonneg hCf (by linarith))
  calc _ ≤ b ^ (Ch * (Cf * M ^ 2)) * b ^ (Ch * r * (Cf * M)) :=
        mul_le_mul e1 e2 (Real.rpow_nonneg hY0 _) (Real.rpow_nonneg hb0.le _)
    _ = b ^ (Ch * (Cf * M ^ 2) + Ch * r * (Cf * M)) := (Real.rpow_add hb0 _ _).symm
    _ ≤ b ^ (2 * Ch * Cf * M ^ e) := by
        apply Real.rpow_le_rpow_of_exponent_le hb
        have h2 : M ^ 2 ≤ M ^ e := pow_le_pow_right₀ hM1 he
        have h3 : (r : ℝ) * M ≤ M ^ 2 := by nlinarith
        have hCC : 0 ≤ Ch * Cf := mul_nonneg hCh hCf
        nlinarith [mul_le_mul_of_nonneg_left h2 hCC, mul_le_mul_of_nonneg_left h3 hCC]

/- English proof (translation)
Introduce `T T' b v L f μsec hP p hp`. Take `⟨⟨hLoc, hdist, hKF, hSec, hT, hT'⟩, hdinf⟩` from `hP`. Take `⟨hk1, hε, hc, hκN, hκN', hStd, hTz, hTz'⟩` from `hLoc`. Take `⟨-, -, -, hka0, hkaU, hkaL, -, -, -, -, hlamb, -, -, hAll, hGap, -, -⟩` from `id hStd`. Use `set M : ℝ := ((2 * D.R.rS + 2 : ℕ) : ℝ) with hM`.

Establish `hkne : kaRe D ≠ 0` using `hka0.ne'`. Establish `hb8 : 8 ≤ b`. Establish `hne : (⟨0, by omega⟩ : Fin (2 * D.R.rS + D.R.k + 1)) ≠ ⟨1, by omega⟩`. Simplify using `[Fin.ext_iff]`. Establish `g` using `hAll _ _ hne`.

Establish `a0` using `hlamb ⟨0, by omega⟩`. Establish `a1` using `hlamb ⟨1, by omega⟩`. Establish `hM2 : (2 : ℝ) ≤ M` using `by rw [hM]; norm_cast; omega`. Establish `hM8 : (8 : ℝ) ≤ M ^ 3` using `by nlinarith`. Establish `hs` using `(abs_sub _ _).trans (add_le_add a0 a1)`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hb1 : 1 ≤ b` using `by linarith`. Establish `hb0 : 0 < b` using `by linarith`. Establish `hCh : 0 ≤ Ch`. Assume the negation of the conclusion as `hneg`.

Use `push_neg at hneg`. Establish `hlt : b ^ Ch < 1` using `Real.rpow_lt_one_of_one_lt_of_neg (by linarith) hneg`. Establish `h1 : kaRe D < 1` using `lt_of_le_of_lt hkaU hlt`. Establish `h2 : (kaRe D)⁻¹ < 1` using `lt_of_le_of_lt hkaL hlt`. Establish `h3 : kaRe D * (kaRe D)⁻¹ < 1 * 1` using `mul_lt_mul'' h1 h2 hka0.le (inv_nonneg.2 hka0.le)`.

Rewrite `h3` using `[mul_inv_cancel₀ hkne, one_mul]`. Conclude with `lt_irrefl _ h3`. Establish `hgapL` using `gap_mono (gap_transfer hGap hdinf) hgap`. Take `⟨L₁, f₁, hε1, hlam1, hu1, hu1', hc1, hκ1, hκ1', hz1, hz1', hKF1, hrest⟩` from `hFr L f (kaRe D) (kaRe D)⁻¹ (kaRe D ^ D.R.rS) hka0 (inv_pos.2 hka0) (pow_pos hka0 _) hc hκN hκN' hε hgapL hKF`. Take `⟨μsec₁, hSec1, K₁, hK1, hJ1, hpts⟩` from `hrest μsec hSec`.

Rewrite `hp`, the goal using `[← hT, ← hT']`. Take `⟨γ₁, -, hG1, -, hW2⟩` from `hpts p hp`. Establish `hkq : (kaRe D ^ D.R.rS) ^ 2 * (1 / kaRe D) ^ (2 * D.R.rS) = 1`. Rewrite using `[one_div, inv_pow, ← pow_mul, mul_comm D.R.rS 2, mul_inv_cancel₀ (pow_ne_zero _ hkne)]`. Establish `e1 : Tz D.R.k D.R.rS L₁.z * (1 / kaRe D) ^ (2 * D.R.rS) = Tz D.R.k D.R.rS L.z * (kaRe D / kaRe D) ^ (2 * D.R.rS)`.

Rewrite using `[hz1, div_self hkne, one_pow, mul_one]`. Take the linear combination `(Tz D.R.k D.R.rS L.z) * hkq`. Establish `e1' : Tz D.R.k D.R.rS L₁.z' * (1 / kaRe D) ^ (2 * D.R.rS) = Tz D.R.k D.R.rS L.z' * (kaRe D / kaRe D) ^ (2 * D.R.rS)`. Rewrite using `[hz1', div_self hkne, one_pow, mul_one]`. Take the linear combination `(Tz D.R.k D.R.rS L.z') * hkq`.

Establish `hPl1 : PlaceOK1 D Ch Cg b dist dinf v L₁ f₁ μsec₁`. Use `⟨⟨hk1, hε1.trans hε, ?_, hκ1, hκ1', ?_, ?_, ?_⟩, by rw [hlam1]; exact hdist, by rw [hlam1]; exact hdinf, hKF1, hSec1⟩` and prove the remaining obligations. Rewrite using `[hc1, inv_mul_cancel₀ hkne]`. Rewrite using `[hε1, hu1, hu1', e1, e1']`. Conclude with `hStd`.

Rewrite using `[one_pow, mul_one, hz1]`. Establish `: (kaRe D ^ D.R.rS) ^ 2 * Tz D.R.k D.R.rS L.z = Tz D.R.k D.R.rS L.z * kaRe D ^ (2 * D.R.rS)` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[one_pow, mul_one, hz1']`. Establish `: (kaRe D ^ D.R.rS) ^ 2 * Tz D.R.k D.R.rS L.z' = Tz D.R.k D.R.rS L.z' * kaRe D ^ (2 * D.R.rS)` using `by ring`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hc0 : 0 < (kaRe D)⁻¹ ^ (2 * D.R.rS * (D.R.rS + 1)) * (kaRe D ^ D.R.rS) ^ (4 * (D.R.rS + 1))` using `by positivity`. Establish `hG1ne : Gpt (Tz D.R.k D.R.rS L₁.z) (Tz D.R.k D.R.rS L₁.z') γ₁ ≠ 0`. Rewrite using `[hG1]`. Conclude with `mul_ne_zero hc0.ne' hp`.

Establish `hB1` using `hB b v L₁ f₁ μsec₁ hPl1 γ₁ hG1ne`. Use `set G := Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') p with hGdef`. Use `set c := (kaRe D)⁻¹ ^ (2 * D.R.rS * (D.R.rS + 1)) * (kaRe D ^ D.R.rS) ^ (4 * (D.R.rS + 1)) with hcdef`. Use `set Fr := max (kaRe D)⁻¹ (kaRe D)⁻¹⁻¹ ^ (Cf * M ^ 2) * max (kaRe D ^ D.R.rS) (kaRe D ^ D.R.rS)⁻¹ ^ (Cf * M) with hFrdef`. Establish `hFr0 : 0 ≤ Fr` using `by positivity`.

Establish `hFrle : Fr ≤ b ^ (2 * Ch * Cf * M ^ e)` using `frames_factor_le hb1 hka0 hkaU hkaL hCh hCf (by omega)`. Establish `hcinv : c⁻¹ = (kaRe D)⁻¹ ^ (2 * D.R.rS * (D.R.rS + 1))`. Establish `hpow : (kaRe D ^ D.R.rS) ^ (4 * (D.R.rS + 1)) = kaRe D ^ (2 * D.R.rS * (D.R.rS + 1)) * kaRe D ^ (2 * D.R.rS * (D.R.rS + 1))`. Rewrite using `[← pow_mul, ← pow_add]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `hc' : c = kaRe D ^ (2 * D.R.rS * (D.R.rS + 1))`. Rewrite using `[hcdef, hpow, inv_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hkne), one_mul]`. Rewrite using `[hc', inv_pow]`. Establish `hN : ((2 * D.R.rS * (D.R.rS + 1) : ℕ) : ℝ) ≤ M ^ 2`.

Rewrite using `[hM]`. Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities. Establish `hcb : max 1 c⁻¹ ≤ b ^ (Ch * M ^ 2)`. Use `max_le (Real.one_le_rpow hb1 (mul_nonneg hCh (by positivity))) ?_` and prove the remaining obligations.

Rewrite using `[hcinv]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.rpow_mul hb0.le, Real.rpow_natCast]`. Use `_ ≤ b ^ (Ch * M ^ 2) := Real.rpow_le_rpow_of_exponent_le hb1 (mul_le_mul_of_nonneg_left hN hCh)`. Establish `hmax : max 1 (1 / (c * G)) ≤ max 1 c⁻¹ * max 1 (1 / G)`.

Use `max_le (one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _)) ?_` and prove the remaining obligations. Establish `hc0' : 0 ≤ c⁻¹` using `inv_nonneg.2 hc0.le`. Combine the equalities or inequalities in the displayed calculation. Establish `hpowA : max 1 (1 / (c * G)) ^ A ≤ b ^ (Ch * CA * M ^ e) * max 1 (1 / G) ^ A`. Combine the equalities or inequalities in the displayed calculation.

Establish `hreal : Fr * (b ^ (C * M ^ e) * max 1 (1 / (c * G)) ^ A) ≤ b ^ ((C + 2 * Ch * Cf + Ch * CA) * M ^ e) * max 1 (1 / G) ^ A`. Establish `hsplit : b ^ ((C + 2 * Ch * Cf + Ch * CA) * M ^ e) = b ^ (2 * Ch * Cf * M ^ e) * (b ^ (C * M ^ e) * b ^ (Ch * CA * M ^ e))`. Rewrite using `[← Real.rpow_add hb0, ← Real.rpow_add hb0]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hsplit]`. Establish `hbC : 0 ≤ b ^ (C * M ^ e)` using `Real.rpow_nonneg hb0.le _`. Combine the equalities or inequalities in the displayed calculation. Establish `hK1ne : ENNReal.ofReal K₁ ≠ 0` using `(ENNReal.ofReal_pos.2 hK1).ne'`. Establish `hB1'` using `hB1`.

Rewrite `hB1'` using `[hG1, hJ1]`. Establish `key : ENNReal.ofReal K₁ * (ENNReal.ofReal (ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') p) * orbSq L f p) ≤ ENNReal.ofReal K₁ * (ENNReal.ofReal (b ^ ((C + 2 * Ch * Cf + Ch * CA) * M ^ e) * max 1 (1 / G) ^ A) * jNorm2 L f μsec)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ENNReal.ofReal_mul hFr0]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ ≤ _ := by gcongr`. Conclude with `(ENNReal.mul_le_mul_iff_right hK1ne ENNReal.ofReal_ne_top).1 key`.
-/
theorem bpLocS_of_1 {Ch Cg dist dinf C CA Cgf Cf : ℝ} {A e : ℕ} (hCg : 2 ≤ Cg) (he : 4 ≤ e)
    (hA : (A : ℝ) ≤ CA * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2) (hCf : 0 ≤ Cf)
    (hgap : Cgf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
        (((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 + ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3) ≤
      Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
        (((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 + ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3) -
        2 * dinf)
    (hFr : Formalism.MainNotions.OnePlaceEstimates.FrameBesselBound D Cgf Cf) (hB : BpLoc1 D Ch Cg dist dinf A C e) :
    BpLocS D Ch Cg dist dinf A (C + 2 * Ch * Cf + Ch * CA) e := by
  intro T T' b v L f μsec hP p hp
  obtain ⟨⟨hLoc, hdist, hKF, hSec, hT, hT'⟩, hdinf⟩ := hP
  obtain ⟨hk1, hε, hc, hκN, hκN', hStd, hTz, hTz'⟩ := hLoc
  obtain ⟨-, -, -, hka0, hkaU, hkaL, -, -, -, -, hlamb, -, -, hAll, hGap, -, -⟩ := id hStd
  set M : ℝ := ((2 * D.R.rS + 2 : ℕ) : ℝ) with hM
  have hkne : kaRe D ≠ 0 := hka0.ne'

  have hb8 : 8 ≤ b := by
    have hne : (⟨0, by omega⟩ : Fin (2 * D.R.rS + D.R.k + 1)) ≠ ⟨1, by omega⟩ := by
      simp [Fin.ext_iff]
    have g := hAll _ _ hne
    have a0 := hlamb ⟨0, by omega⟩
    have a1 := hlamb ⟨1, by omega⟩
    have hM2 : (2 : ℝ) ≤ M := by rw [hM]; norm_cast; omega
    have hM8 : (8 : ℝ) ≤ M ^ 3 := by nlinarith
    have hs := (abs_sub _ _).trans (add_le_add a0 a1)
    nlinarith
  have hb1 : 1 ≤ b := by linarith
  have hb0 : 0 < b := by linarith
  have hCh : 0 ≤ Ch := by
    by_contra hneg
    push_neg at hneg
    have hlt : b ^ Ch < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) hneg
    have h1 : kaRe D < 1 := lt_of_le_of_lt hkaU hlt
    have h2 : (kaRe D)⁻¹ < 1 := lt_of_le_of_lt hkaL hlt
    have h3 : kaRe D * (kaRe D)⁻¹ < 1 * 1 := mul_lt_mul'' h1 h2 hka0.le (inv_nonneg.2 hka0.le)
    rw [mul_inv_cancel₀ hkne, one_mul] at h3
    exact lt_irrefl _ h3
  have hgapL := gap_mono (gap_transfer hGap hdinf) hgap
  obtain ⟨L₁, f₁, hε1, hlam1, hu1, hu1', hc1, hκ1, hκ1', hz1, hz1', hKF1, hrest⟩ :=
    hFr L f (kaRe D) (kaRe D)⁻¹ (kaRe D ^ D.R.rS) hka0 (inv_pos.2 hka0) (pow_pos hka0 _) hc hκN hκN' hε
      hgapL hKF
  obtain ⟨μsec₁, hSec1, K₁, hK1, hJ1, hpts⟩ := hrest μsec hSec
  rw [← hT, ← hT'] at hp ⊢
  obtain ⟨γ₁, -, hG1, -, hW2⟩ := hpts p hp
  have hkq : (kaRe D ^ D.R.rS) ^ 2 * (1 / kaRe D) ^ (2 * D.R.rS) = 1 := by
    rw [one_div, inv_pow, ← pow_mul, mul_comm D.R.rS 2, mul_inv_cancel₀ (pow_ne_zero _ hkne)]
  have e1 : Tz D.R.k D.R.rS L₁.z * (1 / kaRe D) ^ (2 * D.R.rS) =
      Tz D.R.k D.R.rS L.z * (kaRe D / kaRe D) ^ (2 * D.R.rS) := by
    rw [hz1, div_self hkne, one_pow, mul_one]
    linear_combination (Tz D.R.k D.R.rS L.z) * hkq
  have e1' : Tz D.R.k D.R.rS L₁.z' * (1 / kaRe D) ^ (2 * D.R.rS) =
      Tz D.R.k D.R.rS L.z' * (kaRe D / kaRe D) ^ (2 * D.R.rS) := by
    rw [hz1', div_self hkne, one_pow, mul_one]
    linear_combination (Tz D.R.k D.R.rS L.z') * hkq
  have hPl1 : PlaceOK1 D Ch Cg b dist dinf v L₁ f₁ μsec₁ := by
    refine ⟨⟨hk1, hε1.trans hε, ?_, hκ1, hκ1', ?_, ?_, ?_⟩, by rw [hlam1]; exact hdist,
      by rw [hlam1]; exact hdinf, hKF1, hSec1⟩
    · rw [hc1, inv_mul_cancel₀ hkne]
    · rw [hε1, hu1, hu1', e1, e1']
      exact hStd
    · rw [one_pow, mul_one, hz1]
      have : (kaRe D ^ D.R.rS) ^ 2 * Tz D.R.k D.R.rS L.z = Tz D.R.k D.R.rS L.z * kaRe D ^ (2 * D.R.rS) := by ring
      linarith
    · rw [one_pow, mul_one, hz1']
      have : (kaRe D ^ D.R.rS) ^ 2 * Tz D.R.k D.R.rS L.z' = Tz D.R.k D.R.rS L.z' * kaRe D ^ (2 * D.R.rS) := by ring
      linarith
  have hc0 : 0 < (kaRe D)⁻¹ ^ (2 * D.R.rS * (D.R.rS + 1)) * (kaRe D ^ D.R.rS) ^ (4 * (D.R.rS + 1)) := by positivity
  have hG1ne : Gpt (Tz D.R.k D.R.rS L₁.z) (Tz D.R.k D.R.rS L₁.z') γ₁ ≠ 0 := by
    rw [hG1]
    exact mul_ne_zero hc0.ne' hp
  have hB1 := hB b v L₁ f₁ μsec₁ hPl1 γ₁ hG1ne

  set G := Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') p with hGdef
  set c := (kaRe D)⁻¹ ^ (2 * D.R.rS * (D.R.rS + 1)) * (kaRe D ^ D.R.rS) ^ (4 * (D.R.rS + 1)) with hcdef
  set Fr := max (kaRe D)⁻¹ (kaRe D)⁻¹⁻¹ ^ (Cf * M ^ 2) * max (kaRe D ^ D.R.rS) (kaRe D ^ D.R.rS)⁻¹ ^ (Cf * M)
    with hFrdef
  have hFr0 : 0 ≤ Fr := by positivity
  have hFrle : Fr ≤ b ^ (2 * Ch * Cf * M ^ e) :=
    frames_factor_le hb1 hka0 hkaU hkaL hCh hCf (by omega)
  have hcinv : c⁻¹ = (kaRe D)⁻¹ ^ (2 * D.R.rS * (D.R.rS + 1)) := by
    have hpow : (kaRe D ^ D.R.rS) ^ (4 * (D.R.rS + 1)) =
        kaRe D ^ (2 * D.R.rS * (D.R.rS + 1)) * kaRe D ^ (2 * D.R.rS * (D.R.rS + 1)) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      ring
    have hc' : c = kaRe D ^ (2 * D.R.rS * (D.R.rS + 1)) := by
      rw [hcdef, hpow, inv_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hkne), one_mul]
    rw [hc', inv_pow]
  have hN : ((2 * D.R.rS * (D.R.rS + 1) : ℕ) : ℝ) ≤ M ^ 2 := by
    rw [hM]
    push_cast
    nlinarith
  have hcb : max 1 c⁻¹ ≤ b ^ (Ch * M ^ 2) := by
    refine max_le (Real.one_le_rpow hb1 (mul_nonneg hCh (by positivity))) ?_
    rw [hcinv]
    calc (kaRe D)⁻¹ ^ (2 * D.R.rS * (D.R.rS + 1)) ≤ (b ^ Ch) ^ (2 * D.R.rS * (D.R.rS + 1)) :=
          pow_le_pow_left₀ (inv_nonneg.2 hka0.le) hkaL _
      _ = b ^ (Ch * ((2 * D.R.rS * (D.R.rS + 1) : ℕ) : ℝ)) := by
          rw [Real.rpow_mul hb0.le, Real.rpow_natCast]
      _ ≤ b ^ (Ch * M ^ 2) := Real.rpow_le_rpow_of_exponent_le hb1 (mul_le_mul_of_nonneg_left hN hCh)
  have hmax : max 1 (1 / (c * G)) ≤ max 1 c⁻¹ * max 1 (1 / G) := by
    refine max_le (one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _)) ?_
    have hc0' : 0 ≤ c⁻¹ := inv_nonneg.2 hc0.le
    calc 1 / (c * G) = c⁻¹ * (1 / G) := by rw [one_div, mul_inv, one_div]
      _ ≤ c⁻¹ * max 1 (1 / G) := mul_le_mul_of_nonneg_left (le_max_right _ _) hc0'
      _ ≤ max 1 c⁻¹ * max 1 (1 / G) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (le_trans zero_le_one (le_max_left _ _))
  have hpowA : max 1 (1 / (c * G)) ^ A ≤ b ^ (Ch * CA * M ^ e) * max 1 (1 / G) ^ A := by
    calc max 1 (1 / (c * G)) ^ A ≤ (max 1 c⁻¹ * max 1 (1 / G)) ^ A :=
          pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _)) hmax A
      _ = max 1 c⁻¹ ^ A * max 1 (1 / G) ^ A := mul_pow _ _ _
      _ ≤ (b ^ (Ch * M ^ 2)) ^ A * max 1 (1 / G) ^ A :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _)) hcb A)
            (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
      _ ≤ b ^ (Ch * CA * M ^ e) * max 1 (1 / G) ^ A :=
          mul_le_mul_of_nonneg_right (pow_cost hb1 hCh he hA)
            (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
  have hreal : Fr * (b ^ (C * M ^ e) * max 1 (1 / (c * G)) ^ A) ≤
      b ^ ((C + 2 * Ch * Cf + Ch * CA) * M ^ e) * max 1 (1 / G) ^ A := by
    have hsplit : b ^ ((C + 2 * Ch * Cf + Ch * CA) * M ^ e) =
        b ^ (2 * Ch * Cf * M ^ e) * (b ^ (C * M ^ e) * b ^ (Ch * CA * M ^ e)) := by
      rw [← Real.rpow_add hb0, ← Real.rpow_add hb0]
      congr 1
      ring
    rw [hsplit]
    have hbC : 0 ≤ b ^ (C * M ^ e) := Real.rpow_nonneg hb0.le _
    calc Fr * (b ^ (C * M ^ e) * max 1 (1 / (c * G)) ^ A)
        ≤ b ^ (2 * Ch * Cf * M ^ e) * (b ^ (C * M ^ e) * (b ^ (Ch * CA * M ^ e) * max 1 (1 / G) ^ A)) :=
          mul_le_mul hFrle (mul_le_mul_of_nonneg_left hpowA hbC)
            (mul_nonneg hbC (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)) (Real.rpow_nonneg hb0.le _)
      _ = _ := by ring
  have hK1ne : ENNReal.ofReal K₁ ≠ 0 := (ENNReal.ofReal_pos.2 hK1).ne'
  have hB1' := hB1
  rw [hG1, hJ1] at hB1'
  have key : ENNReal.ofReal K₁ * (ENNReal.ofReal (ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS L.z)
      (Tz D.R.k D.R.rS L.z') p) * orbSq L f p) ≤
      ENNReal.ofReal K₁ * (ENNReal.ofReal (b ^ ((C + 2 * Ch * Cf + Ch * CA) * M ^ e) * max 1 (1 / G) ^ A) *
        jNorm2 L f μsec) := by
    calc _ ≤ ENNReal.ofReal Fr * (ENNReal.ofReal (ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS L₁.z)
          (Tz D.R.k D.R.rS L₁.z') γ₁) * orbSq L₁ f₁ γ₁) := hW2
      _ ≤ ENNReal.ofReal Fr * (ENNReal.ofReal (b ^ (C * M ^ e) * max 1 (1 / (c * G)) ^ A) *
          (ENNReal.ofReal K₁ * jNorm2 L f μsec)) := by gcongr
      _ = ENNReal.ofReal K₁ * (ENNReal.ofReal (Fr * (b ^ (C * M ^ e) * max 1 (1 / (c * G)) ^ A)) *
          jNorm2 L f μsec) := by
          rw [ENNReal.ofReal_mul hFr0]
          ring
      _ ≤ _ := by gcongr
  exact (ENNReal.mul_le_mul_iff_right hK1ne ENNReal.ofReal_ne_top).1 key

end Fr

/- English proof (translation)
Establish `hM1 : (1 : ℝ) ≤ ((2 * r + 2 : ℕ) : ℝ)` using `by norm_cast; omega`. Establish `h1 : ((2 * r + 2 : ℕ) : ℝ) ^ 3 ≤ ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2)`. Rewrite using `[← Real.rpow_natCast]`. Conclude with `Real.rpow_le_rpow_of_exponent_le hM1 (by norm_num)`. Establish `a1 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ)` using `by norm_cast; omega`.

Establish `a2 : (0 : ℝ) ≤ ((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2` using `by positivity`. Establish `a3 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 3` using `one_le_pow₀ a1`. Establish `hN : (1 : ℝ) ≤ ((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation.
-/
theorem gapX_ge (r k : ℕ) : ((2 * r + 2 : ℕ) : ℝ) ^ 3 ≤ ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
    (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3) := by
  have hM1 : (1 : ℝ) ≤ ((2 * r + 2 : ℕ) : ℝ) := by norm_cast; omega
  have h1 : ((2 * r + 2 : ℕ) : ℝ) ^ 3 ≤ ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hM1 (by norm_num)
  have a1 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by norm_cast; omega
  have a2 : (0 : ℝ) ≤ ((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  have a3 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := one_le_pow₀ a1
  have hN : (1 : ℝ) ≤ ((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := by
    linarith
  calc ((2 * r + 2 : ℕ) : ℝ) ^ 3 ≤ ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) := h1
    _ = ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) * 1 := (mul_one _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hN (Real.rpow_nonneg (by linarith) _)

def BesselExpansionLocalFrame : Prop :=
  ∀ Aw Ch : ℝ, 0 ≤ Aw → ∃ (C1 C2 CA Cinf Cgf Cg₀ : ℝ), 2 ≤ Cg₀ ∧ (∀ D : D7, Formalism.MainNotions.FrameBoundFromBesselTorus.OneBesselTor D Cgf) ∧
    ∀ Cg : ℝ, Cg₀ ≤ Cg → ∀ D : D7,
    ∃ (dist' : ℝ) (A : ℕ), (A : ℝ) ≤ CA * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 ∧
      QExpAtS D Ch Cg 0 (fun _ _ _ X => ∀ v, AllGaps (X.L v).lam (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4)) dist'
          (Cinf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3) A C1 5 (Aw * ((D.R.rS : ℝ) + 1) ^ 2) ∧
        BpLoc1 D Ch Cg dist' (Cinf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3) A C2 5

/- English proof (translation)
Introduce `Aw Ch hAw`. Take `⟨C1, C2, CA, Cinf, Cgf, Cg₀, hCg₀, hOB, hB⟩` from `h Aw Ch hAw`. Use `⟨C1, C2 + 2 * Ch * 2 + Ch * CA, CA, Cinf, max (max Cg₀ 2) (Cgf + 2 * |Cinf|), le_trans (le_max_right _ _) (le_max_left _ _), fun Cg hCg D => ?_⟩` and prove the remaining obligations. Establish `hCg1 : Cg₀ ≤ Cg` using `le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCg`. Establish `hCg2 : 2 ≤ Cg` using `le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCg`.

Establish `hCg3 : Cgf + 2 * |Cinf| ≤ Cg` using `le_trans (le_max_right _ _) hCg`. Take `⟨dist', A, hA, hQ, hB1⟩` from `hB Cg hCg1 D`. Use `⟨dist', A, hA, hQ, ?_⟩` and prove the remaining obligations. Establish `hX` using `gapX_ge D.R.rS D.R.k`. Use `set M : ℝ := ((2 * D.R.rS + 2 : ℕ) : ℝ) with hM`.

Use `set X : ℝ := M ^ ((9 : ℝ) / 2) * (((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 + ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3) with hXdef`. Establish `hM3 : 0 ≤ M ^ 3` using `by positivity`. Establish `hX0 : 0 ≤ X` using `le_trans hM3 hX`. Establish `hgap : Cgf * M ^ ((9 : ℝ) / 2) * (((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 + ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3) ≤ Cg * M ^ ((9 : ℝ) / 2) * (((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 + ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) …`. Rewrite using `[mul_assoc Cgf, mul_assoc Cg, ← hXdef]`.

Establish `h1 : (Cgf + 2 * |Cinf|) * X ≤ Cg * X` using `mul_le_mul_of_nonneg_right hCg3 hX0`. Establish `h2 : Cinf * M ^ 3 ≤ |Cinf| * M ^ 3` using `mul_le_mul_of_nonneg_right (le_abs_self _) hM3`. Establish `h3 : |Cinf| * M ^ 3 ≤ |Cinf| * X` using `mul_le_mul_of_nonneg_left hX (abs_nonneg _)`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `bpLocS_of_1 hCg2 (by norm_num) hA (by norm_num) hgap (Formalism.MainNotions.OnePlaceExpansion.frame_bound_of_bessel_torus D Cgf 2 le_rfl (hOB D)) hB1`.
-/
theorem besselLocal_of_frame (h : BesselExpansionLocalFrame) : BesselExpansionLocal := by
  intro Aw Ch hAw
  obtain ⟨C1, C2, CA, Cinf, Cgf, Cg₀, hCg₀, hOB, hB⟩ := h Aw Ch hAw
  refine ⟨C1, C2 + 2 * Ch * 2 + Ch * CA, CA, Cinf, max (max Cg₀ 2) (Cgf + 2 * |Cinf|),
    le_trans (le_max_right _ _) (le_max_left _ _), fun Cg hCg D => ?_⟩
  have hCg1 : Cg₀ ≤ Cg := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCg
  have hCg2 : 2 ≤ Cg := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCg
  have hCg3 : Cgf + 2 * |Cinf| ≤ Cg := le_trans (le_max_right _ _) hCg
  obtain ⟨dist', A, hA, hQ, hB1⟩ := hB Cg hCg1 D
  refine ⟨dist', A, hA, hQ, ?_⟩
  have hX := gapX_ge D.R.rS D.R.k
  set M : ℝ := ((2 * D.R.rS + 2 : ℕ) : ℝ) with hM
  set X : ℝ := M ^ ((9 : ℝ) / 2) *
    (((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 + ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3)
    with hXdef
  have hM3 : 0 ≤ M ^ 3 := by positivity
  have hX0 : 0 ≤ X := le_trans hM3 hX
  have hgap : Cgf * M ^ ((9 : ℝ) / 2) *
        (((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 + ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3) ≤
      Cg * M ^ ((9 : ℝ) / 2) *
        (((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 + ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3) -
        2 * (Cinf * M ^ 3) := by
    rw [mul_assoc Cgf, mul_assoc Cg, ← hXdef]
    have h1 : (Cgf + 2 * |Cinf|) * X ≤ Cg * X := mul_le_mul_of_nonneg_right hCg3 hX0
    have h2 : Cinf * M ^ 3 ≤ |Cinf| * M ^ 3 := mul_le_mul_of_nonneg_right (le_abs_self _) hM3
    have h3 : |Cinf| * M ^ 3 ≤ |Cinf| * X := mul_le_mul_of_nonneg_left hX (abs_nonneg _)
    nlinarith
  exact bpLocS_of_1 hCg2 (by norm_num) hA (by norm_num) hgap
    (Formalism.MainNotions.OnePlaceExpansion.frame_bound_of_bessel_torus D Cgf 2 le_rfl (hOB D)) hB1

/- English proof (translation)
The claim follows from `uniformTheoremB_of_local (besselLocal_of_frame h)`.
-/
theorem uniformTheoremB_of_local_frame (h : BesselExpansionLocalFrame) : WeightedBoundRotatedUniform := uniformTheoremB_of_local (besselLocal_of_frame h)

end Formalism.L2.SG.Pf.BesselExpansion
