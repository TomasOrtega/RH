import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFrameTranslatedPerpOfIsFrame
open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

noncomputable section

namespace UpperTheory.Lit.Bur.BlockEmb

open PI.UpqRep PI.HwUniqW

/- English proof (translation)
Use extensionality with `i a`. Establish `h1 : (PI.UpqRep.blockW m r s * colW m r) i a = PI.UpqRep.blockW m r s i (bl m r a)`. Simplify using `[Matrix.mul_apply, colW]`. Rewrite using `[h1]`. Distinguish the cases in `hi : InB m r i`.

Establish `hp : i.val - r < m` using `by unfold InB at hi; omega`. Establish `hb` using `block_mk hi hp`. Rewrite using `[← hb, blockW_bl, Matrix.mul_apply]`. Simplify using `[colW, blockIndex_injective.eq_iff]`. Rewrite using `[blockW_out s hi, if_neg (ne_of_inB (inB_bl a) hi).symm, Matrix.mul_apply]`.

Use `(Finset.sum_eq_zero fun b _ => ?_).symm` and prove the remaining obligations. Simplify using `[colW, (ne_of_inB (inB_bl b) hi).symm]`.
-/
theorem blockW_mul_colW {m r : ℕ} (s : Matrix (Fin m) (Fin m) ℂ) :
    PI.UpqRep.blockW m r s * colW m r = colW m r * s := by
  ext i a
  have h1 : (PI.UpqRep.blockW m r s * colW m r) i a = PI.UpqRep.blockW m r s i (bl m r a) := by
    simp [Matrix.mul_apply, colW]
  rw [h1]
  by_cases hi : InB m r i
  · have hp : i.val - r < m := by unfold InB at hi; omega
    have hb := block_mk hi hp
    rw [← hb, blockW_bl, Matrix.mul_apply]
    simp [colW, blockIndex_injective.eq_iff]
  · rw [blockW_out s hi, if_neg (ne_of_inB (inB_bl a) hi).symm, Matrix.mul_apply]
    refine (Finset.sum_eq_zero fun b _ => ?_).symm
    simp [colW, (ne_of_inB (inB_bl b) hi).symm]

/- English proof (translation)
Establish `hz : ∀ j, InB m r j → y j = 0` using `fun j hj => by`. Establish `hp : j.val - r < m` using `by unfold InB at hj; omega`. Rewrite using `[← block_mk hj hp]`. Conclude with `hy _`. Use function extensionality and compare the values at `i`.

Rewrite using `[Matrix.mulVec, dotProduct]`. Distinguish the cases in `hi : InB m r i`. Rewrite using `[hz i hi]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `hj : InB m r j`.

Rewrite using `[hz j hj, mul_zero]`. Rewrite using `[blockW_in_out s hi hj, zero_mul]`. Simplify using `[blockW_out s hi]`.
-/
theorem blockW_mulVec_of_vanish {m r : ℕ} (s : Matrix (Fin m) (Fin m) ℂ) {y : Fin (2 * r + m + 1) → ℂ}
    (hy : ∀ a, y (bl m r a) = 0) : PI.UpqRep.blockW m r s *ᵥ y = y := by
  have hz : ∀ j, InB m r j → y j = 0 := fun j hj => by
    have hp : j.val - r < m := by unfold InB at hj; omega
    rw [← block_mk hj hp]; exact hy _
  funext i
  rw [Matrix.mulVec, dotProduct]
  by_cases hi : InB m r i
  · rw [hz i hi]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : InB m r j
    · rw [hz j hj, mul_zero]
    · rw [blockW_in_out s hi hj, zero_mul]
  · simp [blockW_out s hi]

/- English proof (translation)
Establish `hFe : F = Q * colW m r * Ai` using `by rw [hF, Matrix.mul_assoc, hA, Matrix.mul_one]`. Use `⟨?_, fun x hx => ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hFe]`. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = Q * (PI.UpqRep.blockW m r s * colW m r) * Ai := by`. Rewrite using `[h2]`. Simplify using `only [Matrix.mul_one, Matrix.mul_assoc]`. Use `_ = (Q * colW m r) * s * Ai := by`. Rewrite using `[blockW_mul_colW]`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = F * (A * s * Ai) := by`. Rewrite using `[hF]`. Simplify using `only [Matrix.mul_assoc]`. Establish `hy : ∀ a, (Qi *ᵥ x) (bl m r a) = 0` using `fun a => by`.

Establish `e : (colW m r)ᴴ * PI.UpqRep.Hpk m r * Qi = Aᴴ * (Fᴴ * J)`. Establish `hH : PI.UpqRep.Hpk m r = Qᴴ * J * Q` using `hg.symm`. Rewrite using `[hH]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[conjTranspose_mul]`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = Aᴴ * (Fᴴ * J) := by`. Rewrite using `[h1, hF, conjTranspose_mul]`. Simplify using `only [Matrix.mul_one, Matrix.mul_assoc]`. Rewrite using `[← colW_mulVec (Qi *ᵥ x) a, mulVec_mulVec, e, ← mulVec_mulVec, hx, mulVec_zero]`.

Both sides reduce to the same expression. Rewrite using `[← mulVec_mulVec, ← mulVec_mulVec, blockW_mulVec_of_vanish s hy, mulVec_mulVec, h1, one_mulVec]`.
-/
theorem isEmb_conj_blockW {m r : ℕ} {J Q Qi : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ}
    {F : Matrix (Fin (2 * r + m + 1)) (Fin m) ℂ} {A Ai s : Matrix (Fin m) (Fin m) ℂ}
    (h1 : Q * Qi = 1) (h2 : Qi * Q = 1) (hg : Qᴴ * J * Q = Formalism.QuantumDeterminants.Hpk m r)
    (hF : Q * colW m r = F * A) (hA : A * Ai = 1) :
    IsEmb J F (Q * PI.UpqRep.blockW m r s * Qi) (A * s * Ai) := by
  have hFe : F = Q * colW m r * Ai := by rw [hF, Matrix.mul_assoc, hA, Matrix.mul_one]
  refine ⟨?_, fun x hx => ?_⟩
  · calc Q * PI.UpqRep.blockW m r s * Qi * F
        = Q * PI.UpqRep.blockW m r s * (Qi * Q) * colW m r * Ai := by
          rw [hFe]; simp only [Matrix.mul_assoc]
      _ = Q * (PI.UpqRep.blockW m r s * colW m r) * Ai := by
          rw [h2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = (Q * colW m r) * s * Ai := by
          rw [blockW_mul_colW]; simp only [Matrix.mul_assoc]
      _ = F * (A * s * Ai) := by
          rw [hF]; simp only [Matrix.mul_assoc]
  · have hy : ∀ a, (Qi *ᵥ x) (bl m r a) = 0 := fun a => by
      have e : (colW m r)ᴴ * PI.UpqRep.Hpk m r * Qi = Aᴴ * (Fᴴ * J) := by
        have hH : PI.UpqRep.Hpk m r = Qᴴ * J * Q := hg.symm
        rw [hH]
        calc (colW m r)ᴴ * (Qᴴ * J * Q) * Qi = (Q * colW m r)ᴴ * J * (Q * Qi) := by
              rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
          _ = Aᴴ * (Fᴴ * J) := by
              rw [h1, hF, conjTranspose_mul]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      rw [← colW_mulVec (Qi *ᵥ x) a, mulVec_mulVec, e, ← mulVec_mulVec, hx, mulVec_zero]; rfl
    rw [← mulVec_mulVec, ← mulVec_mulVec, blockW_mulVec_of_vanish s hy, mulVec_mulVec, h1, one_mulVec]

end UpperTheory.Lit.Bur.BlockEmb

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @UpperTheory.Lit.Bur.BlockEmb.isEmb_conj_blockW | exact UpperTheory.Lit.Bur.BlockEmb.isEmb_conj_blockW | (intros; apply UpperTheory.Lit.Bur.BlockEmb.isEmb_conj_blockW <;> assumption)`.
-/
theorem _root_.UpperTheory.Lit.Bur.blockEmbed_conj_isUnitaryEmbedding : ∀ {m r : ℕ} {J Q Qi : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ} {F : Matrix (Fin (2 * r + m + 1)) (Fin m) ℂ} {A Ai s : Matrix (Fin m) (Fin m) ℂ} (h1 : Q * Qi = 1) (h2 : Qi * Q = 1) (hg : Qᴴ * J * Q = Formalism.QuantumDeterminants.Hpk m r) (hF : Q * colW m r = F * A) (hA : A * Ai = 1), IsEmb J F (Q * PI.UpqRep.blockW m r s * Qi) (A * s * Ai) := by
  first | exact @UpperTheory.Lit.Bur.BlockEmb.isEmb_conj_blockW | exact UpperTheory.Lit.Bur.BlockEmb.isEmb_conj_blockW | (intros; apply UpperTheory.Lit.Bur.BlockEmb.isEmb_conj_blockW <;> assumption)
