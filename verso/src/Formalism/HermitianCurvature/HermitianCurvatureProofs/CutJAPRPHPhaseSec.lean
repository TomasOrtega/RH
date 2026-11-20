import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRPhaseCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRDatumConst

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.PH

noncomputable section

namespace PS

open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TwoByOneBlock Formalism.FourierDecayAlt.P.TheSec Formalism.FourierDecayAlt.P.TheSecStab

def eM (θ : ℝ) : ℂ := Complex.exp (-((θ : ℂ) * Complex.I))

def eP (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

/- English proof (translation)
Unfold `eP eM`. Rewrite using `[← Complex.exp_add, add_neg_cancel, Complex.exp_zero]`.
-/
theorem expPlus_mul_expMinus (θ : ℝ) : eP θ * eM θ = 1 := by
  unfold eP eM
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

/- English proof (translation)
Unfold `eP eM`. Rewrite using `[Complex.star_def, ← Complex.exp_conj]`. Simplify using the standard rewrite rules.
-/
theorem star_eP (θ : ℝ) : star (eP θ) = eM θ := by
  unfold eP eM
  rw [Complex.star_def, ← Complex.exp_conj]
  simp

/- English proof (translation)
Rewrite using `[← star_eP, star_star]`.
-/
theorem star_eM (θ : ℝ) : star (eM θ) = eP θ := by
  rw [← star_eP, star_star]

section block

variable {k : ℕ}

def D1 (k : ℕ) (θ : ℝ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := Matrix.diagonal fun j => if j = 0 then eM θ else 1

def D2 (k : ℕ) (θ : ℝ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  Matrix.diagonal fun j => if j = Fin.last k then 1 else eM θ

/- English proof (translation)
Use `show (Matrix.diagonal d)ᴴ * Hb k * Matrix.diagonal d = Hb k`. Unfold `Hb`. Rewrite using `[Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `j`.

Simplify using `only [Pi.star_apply]`. Take the linear combination `(if j = Fin.last k then (-1 : ℂ) else 1) * h j`.
-/
theorem diag_mem (d : Fin (k + 1) → ℂ) (h : ∀ j, star (d j) * d j = 1) : Matrix.diagonal d ∈ UH (Hb k) := by
  show (Matrix.diagonal d)ᴴ * Hb k * Matrix.diagonal d = Hb k
  unfold Hb
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext j
  simp only [Pi.star_apply]
  linear_combination (if j = Fin.last k then (-1 : ℂ) else 1) * h j

/- English proof (translation)
Use `diag_mem _ fun j => ?_` and prove the remaining obligations. Establish `hc` using `expPlus_mul_expMinus θ`. Distinguish the cases in `hj : j = 0`. Simplify using `only [hj, if_true, star_eM]`. Conclude with `hc`.

Simplify using `only [hj, if_false, star_one, mul_one]`.
-/
theorem first_diagonal_phase_mem_unitary (θ : ℝ) : D1 k θ ∈ UH (Hb k) := by
  refine diag_mem _ fun j => ?_
  have hc := expPlus_mul_expMinus θ
  by_cases hj : j = 0
  · simp only [hj, if_true, star_eM]; exact hc
  · simp only [hj, if_false, star_one, mul_one]

/- English proof (translation)
Use `diag_mem _ fun j => ?_` and prove the remaining obligations. Establish `hc` using `expPlus_mul_expMinus θ`. Distinguish the cases in `hj : j = Fin.last k`. Simplify using `only [hj, if_true, star_one, mul_one]`. Simplify using `only [hj, if_false, star_eM]`.

Conclude with `hc`.
-/
theorem diagonal_phase_mem_unitary (θ : ℝ) : D2 k θ ∈ UH (Hb k) := by
  refine diag_mem _ fun j => ?_
  have hc := expPlus_mul_expMinus θ
  by_cases hj : j = Fin.last k
  · simp only [hj, if_true, star_one, mul_one]
  · simp only [hj, if_false, star_eM]; exact hc

/- English proof (translation)
Use function extensionality and compare the values at `i`. Rewrite using `[D1, Matrix.mulVec_diagonal]`. Distinguish the cases in `hi : i = 0`. Substitute `hi` using the available equality. Rewrite using `[hx, mul_zero]`.

Rewrite using `[if_neg hi, one_mul]`.
-/
theorem first_diagonal_phase_fixes_tail (θ : ℝ) {x : Fin (k + 1) → ℂ} (hx : x 0 = 0) : D1 k θ *ᵥ x = x := by
  funext i
  rw [D1, Matrix.mulVec_diagonal]
  by_cases hi : i = 0
  · subst hi; rw [hx, mul_zero]
  · rw [if_neg hi, one_mul]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Rewrite using `[D1, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]`. Distinguish the cases in `hi : i = 0`. Substitute `hi` using the available equality. Rewrite using `[if_pos rfl]`.

Rewrite using `[if_neg hi, Pi.single_apply, if_neg hi, mul_zero, mul_zero]`.
-/
theorem diagonal_phase_first_vector (θ : ℝ) : D1 k θ *ᵥ Pi.single 0 1 = eM θ • (Pi.single 0 1 : Fin (k + 1) → ℂ) := by
  funext i
  rw [D1, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  by_cases hi : i = 0
  · subst hi; rw [if_pos rfl]
  · rw [if_neg hi, Pi.single_apply, if_neg hi, mul_zero, mul_zero]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Rewrite using `[D2, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]`. Distinguish the cases in `hi : i = Fin.last k`. Substitute `hi` using the available equality. Rewrite using `[hx, mul_zero, mul_zero]`.

Rewrite using `[if_neg hi]`.
-/
theorem diagonal_phase_scalar_action (θ : ℝ) {x : Fin (k + 1) → ℂ} (hx : x (Fin.last k) = 0) : D2 k θ *ᵥ x = eM θ • x := by
  funext i
  rw [D2, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  by_cases hi : i = Fin.last k
  · subst hi; rw [hx, mul_zero, mul_zero]
  · rw [if_neg hi]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Rewrite using `[D2, Matrix.mulVec_diagonal]`. Distinguish the cases in `hi : i = Fin.last k`. Substitute `hi` using the available equality. Rewrite using `[if_pos rfl, one_mul]`.

Rewrite using `[if_neg hi, Pi.single_apply, if_neg hi, mul_zero]`.
-/
theorem second_diagonal_phase_last_vector (θ : ℝ) : D2 k θ *ᵥ Pi.single (Fin.last k) 1 = (Pi.single (Fin.last k) 1 : Fin (k + 1) → ℂ) := by
  funext i
  rw [D2, Matrix.mulVec_diagonal]
  by_cases hi : i = Fin.last k
  · subst hi; rw [if_pos rfl, one_mul]
  · rw [if_neg hi, Pi.single_apply, if_neg hi, mul_zero]

/- English proof (translation)
Establish `h0` using `zero_ne_last hk`. Establish `hc` using `expPlus_mul_expMinus θ`. Use extensionality with `i j`. Rewrite using `[D1, D2, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, nu_apply, nu_apply, star_mul', star_eP, smul_eq_mul]`. Simplify using `only [Matrix.one_apply, Pi.single_apply]`.

Distinguish the cases in `hi0 : i = 0`. Substitute `hi0` using the available equality. Distinguish the cases in `hj0 : j = 0`. Substitute `hj0` using the available equality. Simplify using `only [h0, if_true, if_false]`.

Take the linear combination `(eM θ * star w) * hc`. Distinguish the cases in `hjl : j = Fin.last k`. Substitute `hjl` using the available equality. Simplify using `only [h0, h0.symm, if_true, if_false]`. Take the linear combination `s * hc`.

Simplify using `only [h0, hj0, hjl, Ne.symm hj0, if_true, if_false]`. Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `hil : i = Fin.last k`. Substitute `hil` using the available equality. Distinguish the cases in `hj0 : j = 0`.

Substitute `hj0` using the available equality. Simplify using `only [h0, h0.symm, if_true, if_false]`. Take the linear combination `s * hc`. Distinguish the cases in `hjl : j = Fin.last k`. Substitute `hjl` using the available equality.

Simplify using `only [h0.symm, if_true, if_false]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [h0.symm, hj0, hjl, Ne.symm hjl, if_true, if_false]`. Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `hj0 : j = 0`.

Substitute `hj0` using the available equality. Simplify using `only [h0, hi0, hil, if_true, if_false]`. Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `hjl : j = Fin.last k`. Substitute `hjl` using the available equality.

Simplify using `only [h0.symm, hi0, hil, if_true, if_false]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hi0, hil, hj0, hjl, if_false]`. Take the linear combination `(if i = j then (1 : ℂ) else 0) * hc`.
-/
theorem nu_rot (hk : 1 ≤ k) (θ : ℝ) (w s : ℂ) : D1 k θ * (eP θ • nu k w s) * D2 k θ = nu k (eP θ * w) s := by
  have h0 := zero_ne_last hk
  have hc := expPlus_mul_expMinus θ
  ext i j
  rw [D1, D2, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, nu_apply, nu_apply, star_mul', star_eP,
    smul_eq_mul]
  simp only [Matrix.one_apply, Pi.single_apply]
  by_cases hi0 : i = 0
  · subst hi0
    by_cases hj0 : j = 0
    · subst hj0
      simp only [h0, if_true, if_false]
      linear_combination (eM θ * star w) * hc
    · by_cases hjl : j = Fin.last k
      · subst hjl
        simp only [h0, h0.symm, if_true, if_false]
        linear_combination s * hc
      · simp only [h0, hj0, hjl, Ne.symm hj0, if_true, if_false]
        ring
  · by_cases hil : i = Fin.last k
    · subst hil
      by_cases hj0 : j = 0
      · subst hj0
        simp only [h0, h0.symm, if_true, if_false]
        linear_combination s * hc
      · by_cases hjl : j = Fin.last k
        · subst hjl
          simp only [h0.symm, if_true, if_false]
          ring
        · simp only [h0.symm, hj0, hjl, Ne.symm hjl, if_true, if_false]
          ring
    · by_cases hj0 : j = 0
      · subst hj0
        simp only [h0, hi0, hil, if_true, if_false]
        ring
      · by_cases hjl : j = Fin.last k
        · subst hjl
          simp only [h0.symm, hi0, hil, if_true, if_false]
          ring
        · simp only [hi0, hil, hj0, hjl, if_false]
          linear_combination (if i = j then (1 : ℂ) else 0) * hc

/- English proof (translation)
Unfold `wZ rot eP`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wZ_rot (T T' : ℝ) (θ : ℝ) (ζ : ℂ) : wZ T T' (rot θ ζ) = eP θ * wZ T T' ζ := by
  unfold wZ rot eP
  ring

/- English proof (translation)
Unfold `rot`. Rewrite using `[Complex.normSq_mul, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]`. Evaluate the numerical expressions.
-/
theorem normSq_rot (θ : ℝ) (ζ : ℂ) : Complex.normSq (rot θ ζ) = Complex.normSq ζ := by
  unfold rot
  rw [Complex.normSq_mul, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
  norm_num

/- English proof (translation)
Unfold `sZ`. Rewrite using `[normSq_rot]`.
-/
theorem sZ_rot (T T' : ℝ) (θ : ℝ) (ζ : ℂ) : sZ T T' (rot θ ζ) = sZ T T' ζ := by
  unfold sZ
  rw [normSq_rot]

def hA (k : ℕ) (a : Fin (k + 1) → ℂ) (T : ℝ) (θ : ℝ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  gA k a T * D1 k θ * (gA k a T)⁻¹

def hB (k : ℕ) (b : Fin (k + 1) → ℂ) (T' : ℝ) (θ : ℝ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  (gB k b T')⁻¹ * D2 k θ * gB k b T'

/- English proof (translation)
The claim follows from `(UHb_inv (show gA k a T ∈ UH (Hb k) from (gA_spec k hT ha).1)).1`.
-/
theorem gA_unit {a : Fin (k + 1) → ℂ} {T : ℝ} (hT : 0 < T) (ha : herm (Hb k) a a = -(T : ℂ)) :
    IsUnit (gA k a T).det := (UHb_inv (show gA k a T ∈ UH (Hb k) from (gA_spec k hT ha).1)).1

/- English proof (translation)
Establish `hg : gA k a T ∈ UH (Hb k)` using `(gA_spec k hT ha).1`. Conclude with `UHb_mul (UHb_mul hg (first_diagonal_phase_mem_unitary θ)) (UHb_inv hg).2`.
-/
theorem hA_mem {a : Fin (k + 1) → ℂ} {T : ℝ} (hT : 0 < T) (ha : herm (Hb k) a a = -(T : ℂ)) (θ : ℝ) :
    hA k a T θ ∈ UH (Hb k) := by
  have hg : gA k a T ∈ UH (Hb k) := (gA_spec k hT ha).1
  exact UHb_mul (UHb_mul hg (first_diagonal_phase_mem_unitary θ)) (UHb_inv hg).2

/- English proof (translation)
Establish `hg : gB k b T' ∈ UH (Hb k)` using `(gB_spec k hT' hb).1`. Conclude with `UHb_mul (UHb_mul (UHb_inv hg).2 (diagonal_phase_mem_unitary θ)) hg`.
-/
theorem hB_mem {b : Fin (k + 1) → ℂ} {T' : ℝ} (hT' : 0 < T') (hb : herm (Hb k) b b = -(T' : ℂ)) (θ : ℝ) :
    hB k b T' θ ∈ UH (Hb k) := by
  have hg : gB k b T' ∈ UH (Hb k) := (gB_spec k hT' hb).1
  exact UHb_mul (UHb_mul (UHb_inv hg).2 (diagonal_phase_mem_unitary θ)) hg

/- English proof (translation)
Establish `uA` using `gA_unit hT ha`. Establish `uB` using `DC.gB_unit hT' hb`. Unfold `theSecB hA hB`. Rewrite using `[wZ_rot, sZ_rot, ← nu_rot hk]`. Simplify using `only [Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.nonsing_inv_mul_cancel_left _ _ uA, Matrix.mul_nonsing_inv_cancel_left _ _ uB]`.
-/
theorem secB_rot (hk : 1 ≤ k) {a b : Fin (k + 1) → ℂ} {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T')
    (ha : herm (Hb k) a a = -(T : ℂ)) (hb : herm (Hb k) b b = -(T' : ℂ)) (θ : ℝ) (ζ : ℂ) :
    theSecB k a b T T' (rot θ ζ) =
      hA k a T θ * (eP θ • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)) * theSecB k a b T T' ζ * hB k b T' θ := by
  have uA := gA_unit hT ha
  have uB := DC.gB_unit hT' hb
  unfold theSecB hA hB
  rw [wZ_rot, sZ_rot, ← nu_rot hk]
  simp only [Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.nonsing_inv_mul_cancel_left _ _ uA,
    Matrix.mul_nonsing_inv_cancel_left _ _ uB]

/- English proof (translation)
Establish `uA` using `gA_unit hT ha`. Unfold `hA`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ uA, Matrix.mul_one, ← Matrix.mulVec_mulVec, diagonal_phase_first_vector, Matrix.mulVec_smul]`.
-/
theorem hA_zero {a : Fin (k + 1) → ℂ} {T : ℝ} (hT : 0 < T) (ha : herm (Hb k) a a = -(T : ℂ)) (θ : ℝ) :
    hA k a T θ *ᵥ (gA k a T *ᵥ Pi.single 0 1) = eM θ • (gA k a T *ᵥ Pi.single 0 1) := by
  have uA := gA_unit hT ha
  unfold hA
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ uA, Matrix.mul_one, ← Matrix.mulVec_mulVec, diagonal_phase_first_vector,
    Matrix.mulVec_smul]

/- English proof (translation)
Establish `uA` using `gA_unit hT ha`. Establish `h0` using `zero_ne_last hk`. Establish `hy : ((gA k a T)⁻¹ *ᵥ x) 0 = 0`. Establish `h` using `form_of_unitary (Hb k) (gA_spec k hT ha).1 ((gA k a T)⁻¹ *ᵥ x) (Pi.single 0 1)`. Rewrite `h` using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ uA, Matrix.one_mulVec, hx, herm_Hb_right, if_neg h0, one_mul]`.

Conclude with `h.symm`. Unfold `hA`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, first_diagonal_phase_fixes_tail θ hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ uA, Matrix.one_mulVec]`.
-/
theorem hA_perp (hk : 1 ≤ k) {a : Fin (k + 1) → ℂ} {T : ℝ} (hT : 0 < T) (ha : herm (Hb k) a a = -(T : ℂ)) (θ : ℝ)
    {x : Fin (k + 1) → ℂ} (hx : herm (Hb k) x (gA k a T *ᵥ Pi.single 0 1) = 0) : hA k a T θ *ᵥ x = x := by
  have uA := gA_unit hT ha
  have h0 := zero_ne_last hk
  have hy : ((gA k a T)⁻¹ *ᵥ x) 0 = 0 := by
    have h := form_of_unitary (Hb k) (gA_spec k hT ha).1 ((gA k a T)⁻¹ *ᵥ x) (Pi.single 0 1)
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ uA, Matrix.one_mulVec, hx, herm_Hb_right, if_neg h0, one_mul] at h
    exact h.symm
  unfold hA
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, first_diagonal_phase_fixes_tail θ hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ uA,
    Matrix.one_mulVec]

/- English proof (translation)
Use `hA_perp hk hT ha θ ?_` and prove the remaining obligations. Rewrite using `[← SettingConstruction.herm_symm (Hb k) (SettingConstruction.Hb_herm k), DC.boost_first_orthogonal hk hT ha, star_zero]`.
-/
theorem hA_fix (hk : 1 ≤ k) {a : Fin (k + 1) → ℂ} {T : ℝ} (hT : 0 < T) (ha : herm (Hb k) a a = -(T : ℂ)) (θ : ℝ) :
    hA k a T θ *ᵥ a = a := by
  refine hA_perp hk hT ha θ ?_
  rw [← SettingConstruction.herm_symm (Hb k) (SettingConstruction.Hb_herm k), DC.boost_first_orthogonal hk hT ha, star_zero]

/- English proof (translation)
Establish `uB` using `DC.gB_unit hT' hb`. Establish `hne : ((Real.sqrt T' : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast (Real.sqrt_pos.2 hT').ne'`. Establish `cl : (gB k b T' *ᵥ x) (Fin.last k) = 0`. Rewrite `hxb` using `[← form_of_unitary (Hb k) (gB_spec k hT' hb).1, (gB_spec k hT' hb).2, herm_smul_right, herm_Hb_right, if_pos rfl]`. Establish `h1 : star ((Real.sqrt T' : ℝ) : ℂ) ≠ 0`.

Rewrite using `[show star ((Real.sqrt T' : ℝ) : ℂ) = _ from Complex.conj_ofReal _]`. Conclude with `hne`. Establish `h2` using `(mul_eq_zero.1 hxb).resolve_left h1`. Conclude with `(mul_eq_zero.1 h2).resolve_left (by norm_num)`. Unfold `hB`.

Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, diagonal_phase_scalar_action θ cl, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ uB, Matrix.one_mulVec]`.
-/
theorem hB_perp {b : Fin (k + 1) → ℂ} {T' : ℝ} (hT' : 0 < T') (hb : herm (Hb k) b b = -(T' : ℂ)) (θ : ℝ)
    {x : Fin (k + 1) → ℂ} (hxb : herm (Hb k) x b = 0) : hB k b T' θ *ᵥ x = eM θ • x := by
  have uB := DC.gB_unit hT' hb
  have hne : ((Real.sqrt T' : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hT').ne'
  have cl : (gB k b T' *ᵥ x) (Fin.last k) = 0 := by
    rw [← form_of_unitary (Hb k) (gB_spec k hT' hb).1, (gB_spec k hT' hb).2, herm_smul_right, herm_Hb_right, if_pos rfl] at hxb
    have h1 : star ((Real.sqrt T' : ℝ) : ℂ) ≠ 0 := by
      rw [show star ((Real.sqrt T' : ℝ) : ℂ) = _ from Complex.conj_ofReal _]; exact hne
    have h2 := (mul_eq_zero.1 hxb).resolve_left h1
    exact (mul_eq_zero.1 h2).resolve_left (by norm_num)
  unfold hB
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, diagonal_phase_scalar_action θ cl, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ uB, Matrix.one_mulVec]

/- English proof (translation)
Establish `uB` using `DC.gB_unit hT' hb`. Establish `h2` using `(gB_spec k hT' hb).2`. Establish `h3 : (gB k b T')⁻¹ *ᵥ (((Real.sqrt T' : ℝ) : ℂ) • Pi.single (Fin.last k) 1) = b`. Rewrite using `[← h2, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ uB, Matrix.one_mulVec]`. Unfold `hB`.

Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_smul, second_diagonal_phase_last_vector, h3]`.
-/
theorem hB_fix {b : Fin (k + 1) → ℂ} {T' : ℝ} (hT' : 0 < T') (hb : herm (Hb k) b b = -(T' : ℂ)) (θ : ℝ) :
    hB k b T' θ *ᵥ b = b := by
  have uB := DC.gB_unit hT' hb
  have h2 := (gB_spec k hT' hb).2
  have h3 : (gB k b T')⁻¹ *ᵥ (((Real.sqrt T' : ℝ) : ℂ) • Pi.single (Fin.last k) 1) = b := by
    rw [← h2, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ uB, Matrix.one_mulVec]
  unfold hB
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_smul, second_diagonal_phase_last_vector, h3]

end block

end PS

open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.TwoByOneBlock Formalism.FourierDecayAlt.P.TheSec in
/- English proof (translation)
Introduce `k r z z' hk hz hz' hT hT' θ`. Establish `ha` using `SettingConstruction.herm_self k r z hz`. Establish `hb` using `SettingConstruction.herm_self k r z' hz'`. Use `⟨embWb k r (PS.hA k (wbPart k r z) (Tz k r z) θ), embWb k r (PS.hB k (wbPart k r z') (Tz k r z') θ), (UWset_iff hz _).2 ⟨_, PS.hA_mem hT ha θ, PS.hA_fix hk hT ha θ, rfl⟩, (UWset_iff hz' _).2 ⟨_, PS.hB_mem hT' hb θ, PS.hB_fix hT' hb θ, rfl⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `ζ hζ`.

Rewrite using `[DC.section_first_vector_eq hk hz hz' hT hT' hζ]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Unfold `DC.EE`. Rewrite using `[emb_mulVec_jV, PS.hA_zero hT ha, DC.jV_smul]`. Both sides reduce to the same expression.

Introduce `v hv _ hvE`. Rewrite `hvE` using `[DC.EE, DC.herm_of hv (inWb_jV _), wbPart_jV]`. Rewrite using `[DC.emb_mulVec_of _ hv, PS.hA_perp hk hT ha θ hvE, jV_wbPart hv]`. Use `show embWb k r (theSecB k (wbPart k r z) (wbPart k r z') (Tz k r z) (Tz k r z') (rot θ ζ)) = embWb k r (PS.hA k (wbPart k r z) (Tz k r z) θ) * embWb k r (PS.eP θ • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)) * embWb k r (theSecB k (wbPart k r z) (wbPart k r z') (Tz k r z) (Tz k r …`. Rewrite using `[← emb_mul, ← emb_mul, ← emb_mul, ← PS.secB_rot hk hT hT' ha hb]`.

Introduce `v hv hvz`. Rewrite `hvz` using `[DC.herm_of hv hz']`. Rewrite using `[DC.emb_mulVec_of _ hv, PS.hB_perp hT' hb θ hvz, DC.jV_smul, jV_wbPart hv]`. Both sides reduce to the same expression.
-/
theorem phase_section_holds : PhaseSec := by
  intro k r z z' hk hz hz' hT hT' θ
  have ha := SettingConstruction.herm_self k r z hz
  have hb := SettingConstruction.herm_self k r z' hz'
  refine ⟨embWb k r (PS.hA k (wbPart k r z) (Tz k r z) θ), embWb k r (PS.hB k (wbPart k r z') (Tz k r z') θ),
    (UWset_iff hz _).2 ⟨_, PS.hA_mem hT ha θ, PS.hA_fix hk hT ha θ, rfl⟩,
    (UWset_iff hz' _).2 ⟨_, PS.hB_mem hT' hb θ, PS.hB_fix hT' hb θ, rfl⟩, ?_, ?_⟩
  · intro ζ hζ
    rw [DC.section_first_vector_eq hk hz hz' hT hT' hζ]
    refine ⟨?_, ?_, ?_⟩
    · unfold DC.EE
      rw [emb_mulVec_jV, PS.hA_zero hT ha, DC.jV_smul]
      rfl
    · intro v hv _ hvE
      rw [DC.EE, DC.herm_of hv (inWb_jV _), wbPart_jV] at hvE
      rw [DC.emb_mulVec_of _ hv, PS.hA_perp hk hT ha θ hvE, jV_wbPart hv]
    · show embWb k r (theSecB k (wbPart k r z) (wbPart k r z') (Tz k r z) (Tz k r z') (rot θ ζ)) =
        embWb k r (PS.hA k (wbPart k r z) (Tz k r z) θ) * embWb k r (PS.eP θ • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)) *
          embWb k r (theSecB k (wbPart k r z) (wbPart k r z') (Tz k r z) (Tz k r z') ζ) *
          embWb k r (PS.hB k (wbPart k r z') (Tz k r z') θ)
      rw [← emb_mul, ← emb_mul, ← emb_mul, ← PS.secB_rot hk hT hT' ha hb]
  · intro v hv hvz
    rw [DC.herm_of hv hz'] at hvz
    rw [DC.emb_mulVec_of _ hv, PS.hB_perp hT' hb θ hvz, DC.jV_smul, jV_wbPart hv]
    rfl

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.PH
