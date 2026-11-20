import Formalism.HermitianCurvature.HermitianCurvatureProofs.RuleOfEq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaFiniteOfHaar

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.HeadLetterLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBG

variable {k r : ℕ}

open Formalism.FourierDecayAlt.Q.QRR in

/- English proof (translation)
Unfold `RdV`. Establish `hfun : (fun t : ℝ => Φ (g * NormedSpace.exp ((t : ℂ) • X))) = fun t : ℝ => psi k r z' cStd (NormedSpace.exp ((t : ℂ) • X)) • Φ g`. Use function extensionality and compare the values at `t`. Apply `hΦ` to reduce the goal to its premises. Apply `(exp_mem_nlev (pat_smul _ hX) _).1` to reduce the goal to its premises.

Rewrite using `[dag_smul, hS, Complex.star_def, Complex.conj_ofReal, smul_neg]`. Rewrite using `[hfun]`. Conclude with `((hasDerivAt_psi z' hz X).smul_const (Φ g)).deriv`.
-/
theorem rdV_of_eq {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (z' : Fin (2 * r + k + 1) → ℂ)
    (hz : inWb k r z') (Φ : Q.Mx k r → E) (g : Q.Mx k r)
    (hΦ : ∀ n ∈ QuantumDeterminants.Nset k r, Φ (g * n) = psi k r z' cStd n • Φ g)
    (l : Fin r) (X : Q.Mx k r) (hX : Pat k r l X) (hS : dag k r X = -X) :
    RdV X Φ g = (ell k r z' X - star (ell k r z' X)) • Φ g := by
  unfold RdV
  have hfun : (fun t : ℝ => Φ (g * NormedSpace.exp ((t : ℂ) • X))) =
      fun t : ℝ => psi k r z' cStd (NormedSpace.exp ((t : ℂ) • X)) • Φ g := by
    funext t
    apply hΦ
    apply (exp_mem_nlev (pat_smul _ hX) _).1
    rw [dag_smul, hS, Complex.star_def, Complex.conj_ofReal, smul_neg]
  rw [hfun]
  exact ((hasDerivAt_psi z' hz X).smul_const (Φ g)).deriv

/- English proof (translation)
Introduce `E _ _ k r z' Φ g hz hΦ p q hpq`. Take `⟨l, hl⟩` from `exists_pat p q hpq`. Establish `hr : 1 ≤ r` using `by have := l.isLt; omega`. Use `set Z : B.Mat k r := Matrix.single p q (1 : ℂ) with hZ`. Establish `h1` using `rdV_of_eq z' hz Φ g hΦ l _ (Formalism.FourierDecayAlt.Q.QRR.pat_hpart1 hl) (Formalism.FourierDecayAlt.Q.QRR.skew_hpart1 Z)`.

Establish `h2` using `rdV_of_eq z' hz Φ g hΦ l _ (Formalism.FourierDecayAlt.Q.QRR.pat_hpart2 hl) (Formalism.FourierDecayAlt.Q.QRR.skew_hpart2 Z)`. Use `set Λ : B.Mat k r → ℂ := fun X => ∑ a, ∑ b, X a b * C3.dpsiP k r z' a b with hΛ`. Establish `hΛ1 : ell k r z' (hpart1 (Hpk k r) Z) - star (ell k r z' (hpart1 (Hpk k r) Z)) = Λ (hpart1 (Hpk k r) Z)`. Rewrite using `[← dEll_eq_ell _ _ hr]`. Conclude with `(Formalism.FourierDecayAlt.P.dpsi_is_derivation k r z' _ hr hz (Formalism.FourierDecayAlt.P.PBG.hermitian_part_one_mem_lie Z) (pat_inNp (Formalism.FourierDecayAlt.Q.QRR.pat_hpart1 hl))).symm`.

Establish `hΛ2 : ell k r z' (hpart2 (Hpk k r) Z) - star (ell k r z' (hpart2 (Hpk k r) Z)) = Λ (hpart2 (Hpk k r) Z)`. Rewrite using `[← dEll_eq_ell _ _ hr]`. Conclude with `(Formalism.FourierDecayAlt.P.dpsi_is_derivation k r z' _ hr hz (Formalism.FourierDecayAlt.P.PBG.hermitian_part_two_mem_lie Z) (pat_inNp (Formalism.FourierDecayAlt.Q.QRR.pat_hpart2 hl))).symm`. Establish `hsum : hpart1 (Hpk k r) Z + Complex.I • hpart2 (Hpk k r) Z = Z`. Unfold `hpart1 hpart2`.

Rewrite using `[smul_smul]`. Establish `hI : Complex.I ≠ 0` using `Complex.I_ne_zero`. Establish `: Complex.I * (1 / (2 * Complex.I)) = 1 / 2` using `by field_simp`. Rewrite using `[this, ← smul_add]`. Rewrite using `[show Z - (Hpk k r)⁻¹ * Zᴴ * Hpk k r + (Z + (Hpk k r)⁻¹ * Zᴴ * Hpk k r) = (2 : ℂ) • Z by`.

Rewrite using `[two_smul]`. Use the proof step `abel]`. Rewrite using `[smul_smul]`. Evaluate the numerical expressions. Establish `hΛZ : Λ (hpart1 (Hpk k r) Z) + Complex.I * Λ (hpart2 (Hpk k r) Z) = C3.dpsiP k r z' p q`.

Establish `hlin : Λ (hpart1 (Hpk k r) Z) + Complex.I * Λ (hpart2 (Hpk k r) Z) = Λ (hpart1 (Hpk k r) Z + Complex.I • hpart2 (Hpk k r) Z)`. Simplify using `only [hΛ, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]`. Rewrite using `[hlin, hsum]`. Simplify using `only [hΛ, hZ, Matrix.single_apply]`. Rewrite using `[Finset.sum_eq_single p, Finset.sum_eq_single q]`.

Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Ne.symm hb]`. Simplify using the standard rewrite rules. Introduce `a _ ha`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `b _`. Simplify using `[Ne.symm ha]`. Simplify using the standard rewrite rules. Use `show EabH (Hpk k r) p q Φ g = _`.

Unfold `EabH`. Rewrite using `[h1, h2, hΛ1, hΛ2, smul_smul, ← add_smul, hΛZ]`.
-/
theorem _root_.Formalism.FourierDecayAlt.P.rule_of_eq : LevelPointCoordinates.RuleOfEq := by
  intro E _ _ k r z' Φ g hz hΦ p q hpq
  obtain ⟨l, hl⟩ := exists_pat p q hpq
  have hr : 1 ≤ r := by have := l.isLt; omega
  set Z : B.Mat k r := Matrix.single p q (1 : ℂ) with hZ
  have h1 := rdV_of_eq z' hz Φ g hΦ l _ (Formalism.FourierDecayAlt.Q.QRR.pat_hpart1 hl) (Formalism.FourierDecayAlt.Q.QRR.skew_hpart1 Z)
  have h2 := rdV_of_eq z' hz Φ g hΦ l _ (Formalism.FourierDecayAlt.Q.QRR.pat_hpart2 hl) (Formalism.FourierDecayAlt.Q.QRR.skew_hpart2 Z)
  set Λ : B.Mat k r → ℂ := fun X => ∑ a, ∑ b, X a b * C3.dpsiP k r z' a b with hΛ
  have hΛ1 : ell k r z' (hpart1 (Hpk k r) Z) - star (ell k r z' (hpart1 (Hpk k r) Z)) = Λ (hpart1 (Hpk k r) Z) := by
    rw [← dEll_eq_ell _ _ hr]
    exact (Formalism.FourierDecayAlt.P.dpsi_is_derivation k r z' _ hr hz (Formalism.FourierDecayAlt.P.PBG.hermitian_part_one_mem_lie Z)
      (pat_inNp (Formalism.FourierDecayAlt.Q.QRR.pat_hpart1 hl))).symm
  have hΛ2 : ell k r z' (hpart2 (Hpk k r) Z) - star (ell k r z' (hpart2 (Hpk k r) Z)) = Λ (hpart2 (Hpk k r) Z) := by
    rw [← dEll_eq_ell _ _ hr]
    exact (Formalism.FourierDecayAlt.P.dpsi_is_derivation k r z' _ hr hz (Formalism.FourierDecayAlt.P.PBG.hermitian_part_two_mem_lie Z)
      (pat_inNp (Formalism.FourierDecayAlt.Q.QRR.pat_hpart2 hl))).symm
  have hsum : hpart1 (Hpk k r) Z + Complex.I • hpart2 (Hpk k r) Z = Z := by
    unfold hpart1 hpart2
    rw [smul_smul]
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    have : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by field_simp
    rw [this, ← smul_add]
    rw [show Z - (Hpk k r)⁻¹ * Zᴴ * Hpk k r + (Z + (Hpk k r)⁻¹ * Zᴴ * Hpk k r) = (2 : ℂ) • Z by
      rw [two_smul]; abel]
    rw [smul_smul]; norm_num
  have hΛZ : Λ (hpart1 (Hpk k r) Z) + Complex.I * Λ (hpart2 (Hpk k r) Z) = C3.dpsiP k r z' p q := by
    have hlin : Λ (hpart1 (Hpk k r) Z) + Complex.I * Λ (hpart2 (Hpk k r) Z) =
        Λ (hpart1 (Hpk k r) Z + Complex.I • hpart2 (Hpk k r) Z) := by
      simp only [hΛ, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
        Finset.mul_sum, mul_assoc]
    rw [hlin, hsum]
    simp only [hΛ, hZ, Matrix.single_apply]
    rw [Finset.sum_eq_single p, Finset.sum_eq_single q]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
    · intro a _ ha; apply Finset.sum_eq_zero; intro b _; simp [Ne.symm ha]
    · simp
  show EabH (Hpk k r) p q Φ g = _
  unfold EabH
  rw [h1, h2, hΛ1, hΛ2, smul_smul, ← add_smul, hΛZ]

end Formalism.FourierDecayAlt.P.HeadLetterLemmas
