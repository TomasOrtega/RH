import Mathlib
import Formalism.PeriodIntegrals.RhsWLim
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.HaarUniq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.MBaseMem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsHaar
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInvR
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInvO

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix Set
open scoped ENNReal

namespace PI.RhsWLim.W.RI

open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.ZetaZeros

variable {k r : ℕ}

section Form

variable {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)

/- English proof (translation)
Unfold `herm`. Rewrite using `[Matrix.mulVec_add, dotProduct_add]`.
-/
theorem herm_add_left (x y w : Fin n → ℂ) : herm H (x + y) w = herm H x w + herm H y w := by
  unfold herm
  rw [Matrix.mulVec_add, dotProduct_add]

/- English proof (translation)
Unfold `herm`. Rewrite using `[Matrix.mulVec_sub, dotProduct_sub]`.
-/
theorem herm_sub_left (x y w : Fin n → ℂ) : herm H (x - y) w = herm H x w - herm H y w := by
  unfold herm
  rw [Matrix.mulVec_sub, dotProduct_sub]

/- English proof (translation)
Unfold `herm`. Rewrite using `[Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]`.
-/
theorem herm_smul_left (c : ℂ) (x w : Fin n → ℂ) : herm H (c • x) w = c * herm H x w := by
  unfold herm
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

/- English proof (translation)
Unfold `herm`. Rewrite using `[star_add, add_dotProduct]`.
-/
theorem herm_add_right (x w y : Fin n → ℂ) : herm H x (w + y) = herm H x w + herm H x y := by
  unfold herm
  rw [star_add, add_dotProduct]

/- English proof (translation)
Unfold `herm`. Rewrite using `[star_sub, sub_dotProduct]`.
-/
theorem herm_sub_right (x w y : Fin n → ℂ) : herm H x (w - y) = herm H x w - herm H x y := by
  unfold herm
  rw [star_sub, sub_dotProduct]

/- English proof (translation)
Unfold `herm`. Rewrite using `[star_smul, smul_dotProduct, smul_eq_mul]`.
-/
theorem herm_smul_right (c : ℂ) (x w : Fin n → ℂ) : herm H x (c • w) = star c * herm H x w := by
  unfold herm
  rw [star_smul, smul_dotProduct, smul_eq_mul]

/- English proof (translation)
Unfold `herm`. Use `conv_lhs => rw [Matrix.star_dotProduct]`. Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hH]`.
-/
theorem herm_symm (hH : Hᴴ = H) (x w : Fin n → ℂ) : herm H w x = star (herm H x w) := by
  unfold herm
  conv_lhs => rw [Matrix.star_dotProduct]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hH]

/- English proof (translation)
Unfold `herm`. Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`.
-/
theorem herm_conj (g : Matrix (Fin n) (Fin n) ℂ) (x w : Fin n → ℂ) :
    herm H (g *ᵥ x) (g *ᵥ w) = herm (gᴴ * H * g) x w := by
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

/- English proof (translation)
Unfold `herm`. Rewrite using `[Matrix.mulVec_single_one]`. Simplify using `[dotProduct, Pi.single_apply]`.
-/
theorem herm_single (i j : Fin n) : herm H (Pi.single j 1) (Pi.single i 1) = H i j := by
  unfold herm
  rw [Matrix.mulVec_single_one]
  simp [dotProduct, Pi.single_apply]

/- English proof (translation)
Use extensionality with `i j`. Establish `e` using `h (Pi.single j 1) (Pi.single i 1)`. Rewrite `e` using `[herm_conj, herm_single, herm_single]`. Conclude with `e`.
-/
theorem unit_of_form (g : Matrix (Fin n) (Fin n) ℂ) (h : ∀ x w, herm H (g *ᵥ x) (g *ᵥ w) = herm H x w) :
    gᴴ * H * g = H := by
  ext i j
  have e := h (Pi.single j 1) (Pi.single i 1)
  rw [herm_conj, herm_single, herm_single] at e
  exact e

def tmat (κ : ℂ) (d : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  1 + Matrix.of fun i j => κ * d i * (star d ᵥ* H) j

/- English proof (translation)
Use extensionality with `i`. Simplify using `only [tmat, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Use `congr 1`. Unfold `herm`. Rewrite using `[Matrix.dotProduct_mulVec]`.

Simplify using `only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem tmat_mulVec (κ : ℂ) (d x : Fin n → ℂ) : tmat H κ d *ᵥ x = x + (κ * herm H x d) • d := by
  ext i
  simp only [tmat, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  unfold herm
  rw [Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

end Form

/- English proof (translation)
Use `conv_lhs => rw [← inWb_eq hx, ← inWb_eq hw]`. Unfold `herm`. Rewrite using `[Matrix.mulVec_mulVec, MB.Hpk_Em, ← Matrix.mulVec_mulVec, em_dot]`.
-/
theorem herm_wb {x w : Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x) (hw : inWb k r w) :
    herm (Hpk k r) x w = herm (Hb k) (wbPart k r x) (wbPart k r w) := by
  conv_lhs => rw [← inWb_eq hx, ← inWb_eq hw]
  unfold herm
  rw [Matrix.mulVec_mulVec, MB.Hpk_Em, ← Matrix.mulVec_mulVec, em_dot]

/- English proof (translation)
Unfold `herm Hb`. Simplify using `only [dotProduct, Matrix.mulVec_diagonal, Fin.sum_univ_castSucc, Pi.star_apply]`. Simplify using `only [Fin.castSucc_ne_last, if_false, one_mul, if_true, neg_one_mul, mul_neg]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_hb (x w : Fin (k + 1) → ℂ) :
    herm (Hb k) x w = (∑ j : Fin k, star (w (Fin.castSucc j)) * x (Fin.castSucc j)) - star (w (Fin.last k)) * x (Fin.last k) := by
  unfold herm Hb
  simp only [dotProduct, Matrix.mulVec_diagonal, Fin.sum_univ_castSucc, Pi.star_apply]
  simp only [Fin.castSucc_ne_last, if_false, one_mul, if_true, neg_one_mul, mul_neg]
  ring

/- English proof (translation)
Rewrite using `[herm_hb]`. Use `push_cast`. Simplify using `only [Complex.normSq_eq_conj_mul_self]`. Both sides reduce to the same expression.
-/
theorem herm_self_hb (x : Fin (k + 1) → ℂ) :
    herm (Hb k) x x = ((∑ j : Fin k, Complex.normSq (x (Fin.castSucc j)) - Complex.normSq (x (Fin.last k)) : ℝ) : ℂ) := by
  rw [herm_hb]
  push_cast
  simp only [Complex.normSq_eq_conj_mul_self]
  rfl

/- English proof (translation)
Rewrite `hdz` using `[herm_wb hd hz, herm_hb]`. Rewrite `hdd` using `[herm_wb hd hd, herm_self_hb]`. Establish `hT' : 0 < Complex.normSq (wbPart k r z (Fin.last k)) - ∑ j : Fin k, Complex.normSq (wbPart k r z (Fin.castSucc j))`. Unfold `Tz at hT`. Rewrite `hT` using `[herm_wb hz hz, herm_self_hb, Complex.ofReal_re]`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `set X : Fin k → ℂ := fun j => wbPart k r d (Fin.castSucc j)`. Use `set Z : Fin k → ℂ := fun j => wbPart k r z (Fin.castSucc j)`. Use `set xk := wbPart k r d (Fin.last k)`. Use `set zk := wbPart k r z (Fin.last k)`.

Establish `hX : ∑ j, Complex.normSq (X j) = Complex.normSq xk`. Use `Complex.ofReal_injective (hdd.trans Complex.ofReal_zero.symm)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hdz' : star zk * xk = ∑ j, star (Z j) * X j`. Rewrite `hdz` using `[sub_eq_zero]`.

Conclude with `hdz.symm`. Establish `hxk : xk = 0`. Assume the negation of the conclusion as `hne`. Establish `h1 : ‖zk‖ * ‖xk‖ ≤ ∑ j, ‖Z j‖ * ‖X j‖`. Combine the equalities or inequalities in the displayed calculation.

Establish `h2` using `Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖Z j‖) (fun j => ‖X j‖)`. Establish `h3 : (‖zk‖ * ‖xk‖) ^ 2 ≤ (∑ j, ‖Z j‖ ^ 2) * (∑ j, ‖X j‖ ^ 2)` using `(pow_le_pow_left₀ (by positivity) h1 2).trans h2`. Simplify using `only [← Complex.normSq_eq_norm_sq] at h3`. Rewrite `h3` using `[hX, mul_pow, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]`. Establish `hpos : 0 < Complex.normSq xk` using `Complex.normSq_pos.2 hne`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hX0 : ∀ j, X j = 0`. Introduce `j`. Rewrite `hX` using `[hxk, map_zero]`. Use `(Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (X j))).1 hX j (Finset.mem_univ _)` as an intermediate fact.

Conclude with `Complex.normSq_eq_zero.1 this`. Establish `hb : wbPart k r d = 0`. Use extensionality with `m`. Proceed by induction on `m using Fin.lastCases with`. Consider the case `last => exact hxk`.

Consider the case `cast j => exact hX0 j`. Rewrite using `[← inWb_eq hd, hb, Matrix.mulVec_zero]`.
-/
theorem wb_posdef {z d : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) (hd : inWb k r d)
    (hdz : herm (Hpk k r) d z = 0) (hdd : herm (Hpk k r) d d = 0) : d = 0 := by
  rw [herm_wb hd hz, herm_hb] at hdz
  rw [herm_wb hd hd, herm_self_hb] at hdd
  have hT' : 0 < Complex.normSq (wbPart k r z (Fin.last k)) -
      ∑ j : Fin k, Complex.normSq (wbPart k r z (Fin.castSucc j)) := by
    unfold Tz at hT
    rw [herm_wb hz hz, herm_self_hb, Complex.ofReal_re] at hT
    linarith
  set X : Fin k → ℂ := fun j => wbPart k r d (Fin.castSucc j)
  set Z : Fin k → ℂ := fun j => wbPart k r z (Fin.castSucc j)
  set xk := wbPart k r d (Fin.last k)
  set zk := wbPart k r z (Fin.last k)
  have hX : ∑ j, Complex.normSq (X j) = Complex.normSq xk := by
    have := Complex.ofReal_injective (hdd.trans Complex.ofReal_zero.symm)
    linarith
  have hdz' : star zk * xk = ∑ j, star (Z j) * X j := by
    rw [sub_eq_zero] at hdz
    exact hdz.symm
  have hxk : xk = 0 := by
    by_contra hne
    have h1 : ‖zk‖ * ‖xk‖ ≤ ∑ j, ‖Z j‖ * ‖X j‖ := by
      calc ‖zk‖ * ‖xk‖ = ‖star zk * xk‖ := by rw [norm_mul, norm_star]
        _ = ‖∑ j, star (Z j) * X j‖ := by rw [hdz']
        _ ≤ ∑ j, ‖star (Z j) * X j‖ := norm_sum_le _ _
        _ = ∑ j, ‖Z j‖ * ‖X j‖ := by simp only [norm_mul, norm_star]
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖Z j‖) (fun j => ‖X j‖)
    have h3 : (‖zk‖ * ‖xk‖) ^ 2 ≤ (∑ j, ‖Z j‖ ^ 2) * (∑ j, ‖X j‖ ^ 2) :=
      (pow_le_pow_left₀ (by positivity) h1 2).trans h2
    simp only [← Complex.normSq_eq_norm_sq] at h3
    rw [hX, mul_pow, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq] at h3
    have hpos : 0 < Complex.normSq xk := Complex.normSq_pos.2 hne
    nlinarith
  have hX0 : ∀ j, X j = 0 := by
    intro j
    rw [hxk, map_zero] at hX
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (X j))).1 hX j (Finset.mem_univ _)
    exact Complex.normSq_eq_zero.1 this
  have hb : wbPart k r d = 0 := by
    ext m
    induction m using Fin.lastCases with
    | last => exact hxk
    | cast j => exact hX0 j
  rw [← inWb_eq hd, hb, Matrix.mulVec_zero]

/- English proof (translation)
Unfold `herm bvec`. Rewrite using `[Matrix.mulVec_single_one]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Use `show star (d i) * Hpk k r i j = 0`. Rewrite using `[HU.hpk_row]`.

Use `split_ifs with h`. Distinguish the cases in `hi : i.val < r ∨ r + k < i.val`. Rewrite using `[hd i hi, star_zero, zero_mul]`. It suffices to derive a contradiction. Rewrite `h` using `[Fin.ext_iff]`.

Unfold `HU.tau at h`. Simplify using `only [hi, if_false] at h`. Use linear arithmetic over natural numbers and integers. Conclude with `mul_zero _`.
-/
theorem herm_e_wb {d : Fin (2 * r + k + 1) → ℂ} (hd : inWb k r d) {j : Fin (2 * r + k + 1)}
    (hj : j.val < r ∨ r + k < j.val) : herm (Hpk k r) (bvec j) d = 0 := by
  unfold herm bvec
  rw [Matrix.mulVec_single_one]
  refine Finset.sum_eq_zero fun i _ => ?_
  show star (d i) * Hpk k r i j = 0
  rw [HU.hpk_row]
  split_ifs with h
  · by_cases hi : i.val < r ∨ r + k < i.val
    · rw [hd i hi, star_zero, zero_mul]
    · exfalso
      rw [Fin.ext_iff] at h
      unfold HU.tau at h
      simp only [hi, if_false] at h
      omega
  · exact mul_zero _

/- English proof (translation)
Assemble the required witnesses or components as `⟨HU.uh_one, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩`.
-/
theorem uwset_one (z : Fin (2 * r + k + 1) → ℂ) : (1 : Mat k r) ∈ UWset k r z :=
  ⟨HU.uh_one, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩

/- English proof (translation)
Introduce `k r z v v' hz hv hv' hT h1 h2`. Distinguish the cases in `hvv : v = v'`. Conclude with `⟨1, uwset_one z, by rw [hvv, Matrix.one_mulVec]⟩`. Establish `hsym` using `herm_symm (Hpk k r) MB.hpk_herm`. Use `set d := v - v' with hddef`.

Establish `hd : inWb k r d` using `fun i hi => by simp only [hddef, Pi.sub_apply, hv i hi, hv' i hi, sub_zero]`. Establish `hdz : herm (Hpk k r) d z = 0` using `by rw [herm_sub_left, h2, sub_self]`. Establish `hN : herm (Hpk k r) d d = herm (Hpk k r) v d + star (herm (Hpk k r) v d)`. Simplify using `only [hddef, herm_sub_left, herm_sub_right, star_sub]`. Rewrite using `[← hsym v v, ← hsym v v', ← h1]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hne : herm (Hpk k r) v d ≠ 0`. Introduce `h0`. Establish `: herm (Hpk k r) d d = 0` using `by rw [hN, h0, star_zero, add_zero]`. Conclude with `hvv (sub_eq_zero.1 (wb_posdef hz hT hd hdz this))`.

Establish `hne' : star (herm (Hpk k r) v d) ≠ 0` using `star_ne_zero.2 hne`. Use `set κ : ℂ := -(herm (Hpk k r) v d)⁻¹ with hκ`. Establish `hTx` using `tmat_mulVec (Hpk k r) κ d`. Establish `hfix : ∀ x, herm (Hpk k r) x d = 0 → tmat (Hpk k r) κ d *ᵥ x = x`. Introduce `x hx`.

Rewrite using `[hTx, hx, mul_zero, zero_smul, add_zero]`. Establish `hbr : κ + star κ + κ * star κ * herm (Hpk k r) d d = 0`. Rewrite using `[hN, hκ, star_neg, star_inv₀]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Establish `hunit : ∀ x w, herm (Hpk k r) (tmat (Hpk k r) κ d *ᵥ x) (tmat (Hpk k r) κ d *ᵥ w) = herm (Hpk k r) x w`. Introduce `x w`. Rewrite using `[hTx, hTx, herm_add_left, herm_add_right, herm_add_right, herm_smul_left, herm_smul_left, herm_smul_right, herm_smul_right, hsym w d, star_mul']`. Take the linear combination `(herm (Hpk k r) x d * star (herm (Hpk k r) w d)) * hbr`. Establish `hzd : herm (Hpk k r) z d = 0` using `by rw [hsym d z, hdz, star_zero]`.

Use `⟨tmat (Hpk k r) κ d, ⟨unit_of_form _ _ hunit, fun a => ⟨hfix _ (herm_e_wb hd ?_), hfix _ (herm_e_wb hd ?_)⟩, hfix z hzd⟩, ?_⟩` and prove the remaining obligations. Use `left`. Conclude with `a.isLt`. Use `right show r + k < 2 * r + k - a.val`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hTx, hκ, neg_mul, inv_mul_cancel₀ hne, neg_one_smul, hddef]`. Normalize the expressions using the abelian group laws.
-/
theorem fibTrans : FibTrans := by
  intro k r z v v' hz hv hv' hT h1 h2
  by_cases hvv : v = v'
  · exact ⟨1, uwset_one z, by rw [hvv, Matrix.one_mulVec]⟩
  have hsym := herm_symm (Hpk k r) MB.hpk_herm
  set d := v - v' with hddef
  have hd : inWb k r d := fun i hi => by simp only [hddef, Pi.sub_apply, hv i hi, hv' i hi, sub_zero]
  have hdz : herm (Hpk k r) d z = 0 := by rw [herm_sub_left, h2, sub_self]
  have hN : herm (Hpk k r) d d = herm (Hpk k r) v d + star (herm (Hpk k r) v d) := by
    simp only [hddef, herm_sub_left, herm_sub_right, star_sub]
    rw [← hsym v v, ← hsym v v', ← h1]
    ring
  have hne : herm (Hpk k r) v d ≠ 0 := by
    intro h0
    have : herm (Hpk k r) d d = 0 := by rw [hN, h0, star_zero, add_zero]
    exact hvv (sub_eq_zero.1 (wb_posdef hz hT hd hdz this))
  have hne' : star (herm (Hpk k r) v d) ≠ 0 := star_ne_zero.2 hne
  set κ : ℂ := -(herm (Hpk k r) v d)⁻¹ with hκ
  have hTx := tmat_mulVec (Hpk k r) κ d
  have hfix : ∀ x, herm (Hpk k r) x d = 0 → tmat (Hpk k r) κ d *ᵥ x = x := by
    intro x hx
    rw [hTx, hx, mul_zero, zero_smul, add_zero]
  have hbr : κ + star κ + κ * star κ * herm (Hpk k r) d d = 0 := by
    rw [hN, hκ, star_neg, star_inv₀]
    field_simp
    ring
  have hunit : ∀ x w, herm (Hpk k r) (tmat (Hpk k r) κ d *ᵥ x) (tmat (Hpk k r) κ d *ᵥ w) = herm (Hpk k r) x w := by
    intro x w
    rw [hTx, hTx, herm_add_left, herm_add_right, herm_add_right, herm_smul_left, herm_smul_left,
      herm_smul_right, herm_smul_right, hsym w d, star_mul']
    linear_combination (herm (Hpk k r) x d * star (herm (Hpk k r) w d)) * hbr
  have hzd : herm (Hpk k r) z d = 0 := by rw [hsym d z, hdz, star_zero]
  refine ⟨tmat (Hpk k r) κ d, ⟨unit_of_form _ _ hunit, fun a => ⟨hfix _ (herm_e_wb hd ?_), hfix _ (herm_e_wb hd ?_)⟩,
    hfix z hzd⟩, ?_⟩
  · left
    exact a.isLt
  · right
    show r + k < 2 * r + k - a.val
    omega
  · rw [hTx, hκ, neg_mul, inv_mul_cancel₀ hne, neg_one_smul, hddef]
    abel

end PI.RhsWLim.W.RI
