import Mathlib
import Formalism.HermitianCurvature.StatementD
import Formalism.HermitianCurvature.StatementQ
import Formalism.HermitianCurvature.BigCellVanishingOfCommute
import Formalism.HermitianCurvature.StatementU
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeadingMinorInvariant
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.SBasic
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.NilpotentSubgroup
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CasimirSplitting

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

noncomputable section

namespace GlobalTheory.WigSh

open GlobalTheory.LeadingMinorInv

namespace OmgRight

/- English proof (translation)
Establish `hdet : U.det = 1`. Rewrite using `[det_of_isUpperTriangular]`. Simplify using `[hU.2]`. Introduce `i j hij`. Conclude with `hU.1 _ _ hij`.

Establish `hrow : ∀ b, U.adjugate (Fin.last n) b = if Fin.last n = b then 1 else 0`. Introduce `b`. Establish `h` using `congrFun (congrFun (Matrix.mul_adjugate U) (Fin.last n)) b`. Rewrite `h` using `[Matrix.mul_apply, Finset.sum_eq_single (Fin.last n), hU.2, one_mul, hdet, one_smul, Matrix.one_apply]`. Conclude with `h`.

Introduce `j _ hj`. Rewrite using `[hU.1 _ _ (lt_of_le_of_ne (Fin.le_last j) hj), zero_mul]`. Simplify using the standard rewrite rules. Rewrite using `[adjugate_mul_distrib, Matrix.mul_apply]`. Simplify using `[hrow]`.
-/
lemma adjugate_last_mul {n : ℕ} (Z U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hU : UpUni U) (a : Fin (n + 1)) :
    (Z * U).adjugate (Fin.last n) a = Z.adjugate (Fin.last n) a := by
  have hdet : U.det = 1 := by
    rw [det_of_isUpperTriangular]
    · simp [hU.2]
    · intro i j hij
      exact hU.1 _ _ hij
  have hrow : ∀ b, U.adjugate (Fin.last n) b = if Fin.last n = b then 1 else 0 := by
    intro b
    have h := congrFun (congrFun (Matrix.mul_adjugate U) (Fin.last n)) b
    rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last n), hU.2, one_mul, hdet, one_smul,
      Matrix.one_apply] at h
    · exact h
    · intro j _ hj
      rw [hU.1 _ _ (lt_of_le_of_ne (Fin.le_last j) hj), zero_mul]
    · simp
  rw [adjugate_mul_distrib, Matrix.mul_apply]
  simp [hrow]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[conjTranspose_apply]`. Unfold `Hpk`. Simplify using `only [Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | (exfalso; omega) | simp`.
-/
lemma hpk_conjTranspose (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  rw [conjTranspose_apply]
  unfold Hpk
  simp only [Fin.ext_iff]
  split_ifs <;> first | (exfalso; omega) | simp

/- English proof (translation)
Establish `ha` using `a.isLt`. Rewrite using `[mulVec, dotProduct, Finset.sum_eq_single (eI k r a)]`. Establish `: Hpk k r (esI k r a) (eI k r a) = 1`. Unfold `Hpk esI eI`. Simplify using `only [Fin.ext_iff]`.

Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`. Rewrite using `[this, one_mul]`. Introduce `j _ hj`. Establish `hj' : j.val ≠ a.val` using `fun h => hj (Fin.ext h)`. Establish `: Hpk k r (esI k r a) j = 0`.

Unfold `Hpk esI`. Simplify using `only [Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`. Rewrite using `[this, zero_mul]`. Simplify using the standard rewrite rules.
-/
lemma hpk_mulVec_esI (k r : ℕ) (w : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    (Hpk k r *ᵥ w) (esI k r a) = w (eI k r a) := by
  have ha := a.isLt
  rw [mulVec, dotProduct, Finset.sum_eq_single (eI k r a)]
  · have : Hpk k r (esI k r a) (eI k r a) = 1 := by
      unfold Hpk esI eI
      simp only [Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [this, one_mul]
  · intro j _ hj
    have hj' : j.val ≠ a.val := fun h => hj (Fin.ext h)
    have : Hpk k r (esI k r a) j = 0 := by
      unfold Hpk esI
      simp only [Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [this, zero_mul]
  · simp

/- English proof (translation)
Establish `key : (fun i : Fin (2 * r + k + 1) => if r ≤ i.val ∧ i.val ≤ r + k then (n *ᵥ v) i else 0) = (fun i : Fin (2 * r + k + 1) => if r ≤ i.val ∧ i.val ≤ r + k then v i else 0)`. Use extensionality with `i`. Use `split_ifs with hi`. Simplify using `only [Matrix.mulVec, dotProduct]`. Rewrite using `[Finset.sum_eq_single i]`.

Rewrite using `[hn.2.2 i i (by omega) (by omega) (by omega), if_pos rfl, one_mul]`. Introduce `j _ hji`. Distinguish the cases in `hj1 : j.val < r`. Establish `e : eI k r ⟨j.val, hj1⟩ = j` using `by ext; simp [eI]`. Use `hn.2.1 ⟨j.val, hj1⟩ i (by simp; omega)` as an intermediate fact.

Rewrite `this` using `[e, if_neg (Ne.symm hji)]`. Rewrite using `[this, zero_mul]`. Distinguish the cases in `hj2 : j.val ≤ r + k`. Rewrite using `[hn.2.2 i j (by omega) hj2 (by omega), if_neg (Ne.symm hji), zero_mul]`. Establish `hlt : 2 * r + k - j.val < r` using `by omega`.

Establish `e : esI k r ⟨2 * r + k - j.val, hlt⟩ = j` using `by ext; simp [esI]; omega`. Use `hv ⟨2 * r + k - j.val, hlt⟩` as an intermediate fact. Rewrite `this` using `[e]`. Rewrite using `[this, mul_zero]`. Simplify using the standard rewrite rules.

Both sides reduce to the same expression. Unfold `Formalism.FourierDecayAlt.D.prW`. Simplify using `only [key]`.
-/
lemma prW_mulVec {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) {n : Mx k r} (hn : n ∈ Formalism.QuantumDeterminants.Nset k r)
    {v : Fin (2 * r + k + 1) → ℂ} (hv : ∀ a : Fin r, v (esI k r a) = 0) :
    Formalism.FourierDecayAlt.D.prW k r z (n *ᵥ v) = Formalism.FourierDecayAlt.D.prW k r z v := by
  have key : (fun i : Fin (2 * r + k + 1) => if r ≤ i.val ∧ i.val ≤ r + k then (n *ᵥ v) i else 0) =
      (fun i : Fin (2 * r + k + 1) => if r ≤ i.val ∧ i.val ≤ r + k then v i else 0) := by
    ext i
    split_ifs with hi
    · simp only [Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single i]
      · rw [hn.2.2 i i (by omega) (by omega) (by omega), if_pos rfl, one_mul]
      · intro j _ hji
        by_cases hj1 : j.val < r
        · have e : eI k r ⟨j.val, hj1⟩ = j := by ext; simp [eI]
          have := hn.2.1 ⟨j.val, hj1⟩ i (by simp; omega)
          rw [e, if_neg (Ne.symm hji)] at this
          rw [this, zero_mul]
        · by_cases hj2 : j.val ≤ r + k
          · rw [hn.2.2 i j (by omega) hj2 (by omega), if_neg (Ne.symm hji), zero_mul]
          · have hlt : 2 * r + k - j.val < r := by omega
            have e : esI k r ⟨2 * r + k - j.val, hlt⟩ = j := by ext; simp [esI]; omega
            have := hv ⟨2 * r + k - j.val, hlt⟩
            rw [e] at this
            rw [this, mul_zero]
      · simp
    · rfl
  unfold Formalism.FourierDecayAlt.D.prW
  simp only [key]

/- English proof (translation)
Establish `hx : (∑ c, star ((Zhat k r z z' g).adjugate (Fin.last r) c) • fvec k r z c) = flagMat k r z *ᵥ star ((Zhat k r z z' g).adjugate (Fin.last r))`. Use extensionality with `i`. Simplify using `[flagMat, mulVec, dotProduct, Finset.sum_apply, mul_comm]`. Establish `hF : ∀ w : Fin (2 * r + k + 1) → ℂ, w (eI k r a) = ((flagMat k r z')ᴴ *ᵥ w) a.castSucc`. Introduce `w`.

Simplify using `[flagMat, mulVec, dotProduct, fvec, bvec, Pi.single_apply, apply_ite]`. Establish `hZ : (flagMat k r z')ᴴ * (gᴴ * Hpk k r * flagMat k r z) = (Zhat k r z z' g)ᴴ`. Rewrite using `[zhat_eq]`. Simplify using `only [conjTranspose_mul, conjTranspose_conjTranspose, hpk_conjTranspose, Matrix.mul_assoc]`. Rewrite using `[hx, Matrix.mul_assoc, ← mulVec_mulVec, hpk_mulVec_esI]`.

Use `(hF _).trans ?_` and prove the remaining obligations. Rewrite using `[mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc, hZ]`. Use `erw [← star_vecMul]`. Establish `h` using `congrFun (congrFun (Matrix.adjugate_mul (Zhat k r z z' g)) (Fin.last r)) a.castSucc`. Simplify using `only [Matrix.smul_apply, Matrix.one_apply_ne (Fin.castSucc_ne_last a).symm, smul_zero] at h`.

Establish `h2 : ((Zhat k r z z' g).adjugate (Fin.last r) ᵥ* Zhat k r z z' g) a.castSucc = 0` using `h`. Rewrite using `[Pi.star_apply, h2, star_zero]`.
-/
lemma cof_free (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mx k r) (a : Fin r) :
    ((Hpk k r * gᴴ * Hpk k r) *ᵥ
      ∑ c, star ((Zhat k r z z' g).adjugate (Fin.last r) c) • fvec k r z c) (esI k r a) = 0 := by
  have hx : (∑ c, star ((Zhat k r z z' g).adjugate (Fin.last r) c) • fvec k r z c) =
      flagMat k r z *ᵥ star ((Zhat k r z z' g).adjugate (Fin.last r)) := by
    ext i
    simp [flagMat, mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hF : ∀ w : Fin (2 * r + k + 1) → ℂ, w (eI k r a) = ((flagMat k r z')ᴴ *ᵥ w) a.castSucc := by
    intro w
    simp [flagMat, mulVec, dotProduct, fvec, bvec, Pi.single_apply, apply_ite]
  have hZ : (flagMat k r z')ᴴ * (gᴴ * Hpk k r * flagMat k r z) = (Zhat k r z z' g)ᴴ := by
    rw [zhat_eq]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hpk_conjTranspose, Matrix.mul_assoc]
  rw [hx, Matrix.mul_assoc, ← mulVec_mulVec, hpk_mulVec_esI]
  refine (hF _).trans ?_
  rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc, hZ]
  erw [← star_vecMul]
  have h := congrFun (congrFun (Matrix.adjugate_mul (Zhat k r z z' g)) (Fin.last r)) a.castSucc
  simp only [Matrix.smul_apply, Matrix.one_apply_ne (Fin.castSucc_ne_last a).symm, smul_zero] at h
  have h2 : ((Zhat k r z z' g).adjugate (Fin.last r) ᵥ* Zhat k r z z' g) a.castSucc = 0 := h
  rw [Pi.star_apply, h2, star_zero]

end OmgRight

open OmgRight

open Matrix in
variable {k r : ℕ} in
/- English proof (translation)
The claim follows from `_root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.inv_eq_UH hx`.
-/
private lemma inv_eq_hpk_mul_conjTranspose_mul_hpk_of_mem_UH {x : _root_.Formalism.FourierDecayAlt.Q.Mx k r} (hx : x ∈ _root_.Formalism.QuantumDeterminants.UH (_root_.Formalism.QuantumDeterminants.Hpk k r)) :
    x⁻¹ = _root_.Formalism.QuantumDeterminants.Hpk k r * xᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r :=
  _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.inv_eq_UH hx

open Matrix in
variable {k r : ℕ} in
/- English proof (translation)
Rewrite using `[← Matrix.mul_assoc, _root_.GlobalTheory.CompanionTheory.ZuckCasSplit.hpk_sq, Matrix.one_mul]`.
-/
private lemma hpk_mul_hpk_mul_eq_self (X : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) ℂ) :
    _root_.Formalism.QuantumDeterminants.Hpk k r * (_root_.Formalism.QuantumDeterminants.Hpk k r * X) = X := by
  rw [← Matrix.mul_assoc, _root_.GlobalTheory.CompanionTheory.ZuckCasSplit.hpk_sq, Matrix.one_mul]

open Matrix in
variable {k r : ℕ} in
/- English proof (translation)
The claim follows from `_root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.Hpk_conjTranspose`.
-/
private lemma hpk_conjTranspose_eq_self' : (_root_.Formalism.QuantumDeterminants.Hpk k r)ᴴ = _root_.Formalism.QuantumDeterminants.Hpk k r :=
  _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.Hpk_conjTranspose

open Matrix in
variable {k r : ℕ} in
/- English proof (translation)
Rewrite using `[adjugate_apply, det_of_upperTriangular]`. Simplify using `[updateRow_apply, Pi.single_apply, hU.2]`. Introduce `i j hij`. Simplify using `only [updateRow_apply]`. Use `split_ifs with h`.

Substitute `h` using the available equality. Rewrite using `[Pi.single_apply, if_neg]`. Conclude with `(hij.trans_le (Fin.le_last _)).ne`. Conclude with `hU.1 i j hij`.
-/
private lemma adjugate_upUni_last_apply {m : ℕ} {U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ}
    (hU : _root_.GlobalTheory.LeadingMinorInv.UpUni U) (a : Fin (m + 1)) :
    U.adjugate (Fin.last m) a = if a = Fin.last m then 1 else 0 := by
  rw [adjugate_apply, det_of_upperTriangular]
  · simp [updateRow_apply, Pi.single_apply, hU.2]
  · intro i j hij
    simp only [updateRow_apply]
    split_ifs with h
    · subst h
      rw [Pi.single_apply, if_neg]
      exact (hij.trans_le (Fin.le_last _)).ne
    · exact hU.1 i j hij

open Matrix in
variable {k r : ℕ} in
/- English proof (translation)
Use extensionality with `i`. Simplify using `[mulVec, dotProduct, _root_.GlobalTheory.LeadingMinorInv.flagMat, Finset.sum_apply, mul_comm]`.
-/
private lemma flagMat_mulVec_eq_sum_smul_fvec (z : Fin (2 * r + k + 1) → ℂ) (c : Fin (r + 1) → ℂ) :
    _root_.GlobalTheory.LeadingMinorInv.flagMat k r z *ᵥ c = ∑ a, c a • _root_.Formalism.QuantumDeterminants.fvec k r z a := by
  ext i
  simp [mulVec, dotProduct, _root_.GlobalTheory.LeadingMinorInv.flagMat, Finset.sum_apply, mul_comm]

open Matrix in
variable {k r : ℕ} in
/- English proof (translation)
Unfold `_root_.GlobalTheory.WigSh.omg`. Rewrite using `[← mulVec_mulVec _ (_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r) (_root_.GlobalTheory.LeadingMinorInv.flagMat k r z), flagMat_mulVec_eq_sum_smul_fvec]`. Simplify using `[mulVec_single_one, conjTranspose_apply]`.
-/
private lemma rW_mulVec_adjugate_zhat_single_last_eq (z z' : Fin (2 * r + k + 1) → ℂ) (g : _root_.Formalism.FourierDecayAlt.Q.Mx k r) :
    _root_.GlobalTheory.WigSh.omg k r z z' g = _root_.Formalism.FourierDecayAlt.D.prW k r z'
      ((_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z) *ᵥ
        ((_root_.Formalism.QuantumDeterminants.Zhat k r z z' g).adjugateᴴ *ᵥ Pi.single (Fin.last r) 1)) := by
  unfold _root_.GlobalTheory.WigSh.omg
  rw [← mulVec_mulVec _ (_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r) (_root_.GlobalTheory.LeadingMinorInv.flagMat k r z), flagMat_mulVec_eq_sum_smul_fvec]
  simp [mulVec_single_one, conjTranspose_apply]

open Matrix in
variable {k r : ℕ} in
/- English proof (translation)
Rewrite using `[_root_.GlobalTheory.LeadingMinorInv.zhat_eq]`. Simplify using `only [conjTranspose_mul, conjTranspose_conjTranspose, hpk_conjTranspose_eq_self', Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (_root_.Formalism.QuantumDeterminants.Hpk k r) (_root_.Formalism.QuantumDeterminants.Hpk k r), _root_.GlobalTheory.CompanionTheory.ZuckCasSplit.hpk_sq, Matrix.one_mul]`.
-/
private lemma gram_eq_conjTranspose_hpk_mul_flagMat_mul (z z' : Fin (2 * r + k + 1) → ℂ) (g : _root_.Formalism.FourierDecayAlt.Q.Mx k r) :
    _root_.Formalism.QuantumDeterminants.Zhat k r z z' g = (_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z)ᴴ *
      (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z') := by
  rw [_root_.GlobalTheory.LeadingMinorInv.zhat_eq]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, hpk_conjTranspose_eq_self',
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (_root_.Formalism.QuantumDeterminants.Hpk k r) (_root_.Formalism.QuantumDeterminants.Hpk k r), _root_.GlobalTheory.CompanionTheory.ZuckCasSplit.hpk_sq, Matrix.one_mul]

open Matrix in
variable {k r : ℕ} in
/- English proof (translation)
Establish `hNC` using `((_root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.mem_Nset_iff m).1 hm).2`. Establish `hb : (fun i : Fin (2 * r + k + 1) => if r ≤ ↑i ∧ ↑i ≤ r + k then (m *ᵥ p) i else 0) = (fun i : Fin (2 * r + k + 1) => if r ≤ ↑i ∧ ↑i ≤ r + k then p i else 0)`. Use extensionality with `i`. Use `split_ifs with hi`. Simplify using `only [mulVec, dotProduct]`.

Rewrite using `[Finset.sum_eq_single i]`. Rewrite using `[hNC i i hi.2 (min_le_left _ _)]`. Simplify using the standard rewrite rules. Introduce `j _ hji`. Distinguish the cases in `hj : (j : ℕ) ≤ r + k`.

Rewrite using `[hNC i j hj (le_trans (min_le_right _ _) hi.1), if_neg (Ne.symm hji)]`. Simplify using the standard rewrite rules. Rewrite using `[hp j (by omega)]`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Both sides reduce to the same expression. Simplify using `only [_root_.Formalism.FourierDecayAlt.D.prW]`. Rewrite using `[hb]`.
-/
private lemma prW_mulVec_eq_of_mem_nset_of_tail_eq_zero {z' : Fin (2 * r + k + 1) → ℂ} {m : _root_.Formalism.FourierDecayAlt.Q.Mx k r}
    (hm : m ∈ _root_.Formalism.QuantumDeterminants.Nset k r) {p : Fin (2 * r + k + 1) → ℂ}
    (hp : ∀ j : Fin (2 * r + k + 1), r + k < ↑j → p j = 0) :
    _root_.Formalism.FourierDecayAlt.D.prW k r z' (m *ᵥ p) = _root_.Formalism.FourierDecayAlt.D.prW k r z' p := by
  have hNC := ((_root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.mem_Nset_iff m).1 hm).2
  have hb : (fun i : Fin (2 * r + k + 1) => if r ≤ ↑i ∧ ↑i ≤ r + k then (m *ᵥ p) i else 0) =
      (fun i : Fin (2 * r + k + 1) => if r ≤ ↑i ∧ ↑i ≤ r + k then p i else 0) := by
    ext i
    split_ifs with hi
    · simp only [mulVec, dotProduct]
      rw [Finset.sum_eq_single i]
      · rw [hNC i i hi.2 (min_le_left _ _)]
        simp
      · intro j _ hji
        by_cases hj : (j : ℕ) ≤ r + k
        · rw [hNC i j hj (le_trans (min_le_right _ _) hi.1), if_neg (Ne.symm hji)]
          simp
        · rw [hp j (by omega)]
          simp
      · simp
    · rfl
  simp only [_root_.Formalism.FourierDecayAlt.D.prW]
  rw [hb]

open Matrix in
variable {k r : ℕ} in
/- English proof (translation)
Establish `hJP : ∀ (X : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) ℂ) i c, (_root_.Formalism.QuantumDeterminants.Hpk k r * X) i c = _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.epsI k r i * X (_root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.piI k r i) c`. Introduce `X i c`. Establish `hJa : ∀ i l, _root_.Formalism.QuantumDeterminants.Hpk k r i l = if l = _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.piI k r i then _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.epsI k r i else 0` using `fun i l => _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.Hpk_apply i l`. Rewrite using `[mul_apply]`. Simplify using `only [hJa, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]`.

Establish `hj2` using `j.isLt`. Take `⟨b, hb⟩ : ∃ b : Fin r, (b : ℕ) = 2 * r + k - j` from `⟨⟨2 * r + k - j, by omega⟩, rfl⟩`. Establish `hpi : _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.piI k r (_root_.Formalism.QuantumDeterminants.eI k r b) = j`. Establish `hb2` using `b.isLt`. Apply `Fin.ext` to reduce the goal to its premises.

Apply the tactic sequence `rw [_root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.piI_val, if_neg] <;> simp only [_root_.Formalism.QuantumDeterminants.eI] <;> omega`. Establish `key : (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z')ᴴ * (Q * (Qᴴ * (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z')).adjugateᴴ) = ((Qᴴ * (_root_.Formalism.QuantumDeterminants.H …`. Rewrite using `[conjTranspose_mul (adjugate _), conjTranspose_mul Qᴴ, conjTranspose_conjTranspose, Matrix.mul_assoc]`. Establish `h1` using `congrFun (congrFun key (Fin.castSucc b)) (Fin.last r)`. Rewrite `h1` using `[adjugate_mul]`.

Simplify using `only [conjTranspose_apply, Matrix.smul_apply, one_apply, if_neg (Fin.castSucc_lt_last b).ne', smul_zero, star_zero] at h1`. Rewrite `h1` using `[conjTranspose_mul, hpk_conjTranspose_eq_self', Matrix.mul_assoc, mul_apply, Finset.sum_eq_single (_root_.Formalism.QuantumDeterminants.eI k r b)]`. Rewrite `h1` using `[hJP, hpi]`. Establish `heps` using `_root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.epsI_mul_self (k := k) (r := r) (_root_.Formalism.QuantumDeterminants.eI k r b)`. Establish `hF : (_root_.GlobalTheory.LeadingMinorInv.flagMat k r z')ᴴ (Fin.castSucc b) (_root_.Formalism.QuantumDeterminants.eI k r b) = 1`.

Simplify using `[conjTranspose_apply, _root_.GlobalTheory.LeadingMinorInv.flagMat, _root_.Formalism.QuantumDeterminants.fvec, _root_.Formalism.QuantumDeterminants.bvec]`. Rewrite `h1` using `[hF, one_mul]`. Rewrite using `[mulVec_mulVec]`. Simplify using `only [mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Break down `mul_eq_zero.1 h1 with h | h` into its components or cases.

Rewrite `heps` using `[h, zero_mul]`. Conclude with `absurd heps zero_ne_one`. Conclude with `h`. Introduce `l _ hl`. Simplify using `[conjTranspose_apply, _root_.GlobalTheory.LeadingMinorInv.flagMat, _root_.Formalism.QuantumDeterminants.fvec, _root_.Formalism.QuantumDeterminants.bvec, Pi.single_apply, hl]`.

Simplify using the standard rewrite rules.
-/
private lemma mulVec_adjugate_single_last_apply_eq_zero_of_lt (z' : Fin (2 * r + k + 1) → ℂ)
    (Q : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) ℂ) (j : Fin (2 * r + k + 1))
    (hj : r + k < ↑j) :
    (Q *ᵥ ((Qᴴ * (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z')).adjugateᴴ *ᵥ
      Pi.single (Fin.last r) 1)) j = 0 := by
  have hJP : ∀ (X : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) ℂ) i c,
      (_root_.Formalism.QuantumDeterminants.Hpk k r * X) i c = _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.epsI k r i * X (_root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.piI k r i) c := by
    intro X i c
    have hJa : ∀ i l, _root_.Formalism.QuantumDeterminants.Hpk k r i l =
        if l = _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.piI k r i then _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.epsI k r i else 0 :=
      fun i l => _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.Hpk_apply i l
    rw [mul_apply]
    simp only [hJa, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
  have hj2 := j.isLt
  obtain ⟨b, hb⟩ : ∃ b : Fin r, (b : ℕ) = 2 * r + k - j := ⟨⟨2 * r + k - j, by omega⟩, rfl⟩
  have hpi : _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.piI k r (_root_.Formalism.QuantumDeterminants.eI k r b) = j := by
    have hb2 := b.isLt
    apply Fin.ext
    rw [_root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.piI_val, if_neg] <;> simp only [_root_.Formalism.QuantumDeterminants.eI] <;> omega
  have key : (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z')ᴴ *
      (Q * (Qᴴ * (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z')).adjugateᴴ) =
      ((Qᴴ * (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z')).adjugate *
        (Qᴴ * (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z')))ᴴ := by
    rw [conjTranspose_mul (adjugate _), conjTranspose_mul Qᴴ, conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  have h1 := congrFun (congrFun key (Fin.castSucc b)) (Fin.last r)
  rw [adjugate_mul] at h1
  simp only [conjTranspose_apply, Matrix.smul_apply, one_apply,
    if_neg (Fin.castSucc_lt_last b).ne', smul_zero, star_zero] at h1
  rw [conjTranspose_mul, hpk_conjTranspose_eq_self', Matrix.mul_assoc, mul_apply,
    Finset.sum_eq_single (_root_.Formalism.QuantumDeterminants.eI k r b)] at h1
  · rw [hJP, hpi] at h1
    have heps := _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.epsI_mul_self (k := k) (r := r) (_root_.Formalism.QuantumDeterminants.eI k r b)
    have hF : (_root_.GlobalTheory.LeadingMinorInv.flagMat k r z')ᴴ (Fin.castSucc b) (_root_.Formalism.QuantumDeterminants.eI k r b) = 1 := by
      simp [conjTranspose_apply, _root_.GlobalTheory.LeadingMinorInv.flagMat, _root_.Formalism.QuantumDeterminants.fvec, _root_.Formalism.QuantumDeterminants.bvec]
    rw [hF, one_mul] at h1
    rw [mulVec_mulVec]
    simp only [mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rcases mul_eq_zero.1 h1 with h | h
    · rw [h, zero_mul] at heps
      exact absurd heps zero_ne_one
    · exact h
  · intro l _ hl
    simp [conjTranspose_apply, _root_.GlobalTheory.LeadingMinorInv.flagMat, _root_.Formalism.QuantumDeterminants.fvec, _root_.Formalism.QuantumDeterminants.bvec, Pi.single_apply, hl]
  · simp

open Matrix in

/- English proof (translation)
Introduce `k r z z' g m _ hz' _ hm`. Take `⟨U, hU, hmF⟩` from `_root_.GlobalTheory.LeadingMinorInv.exists_N k r z' hz' m hm`. Establish `hmUH : m ∈ _root_.Formalism.QuantumDeterminants.UH (_root_.Formalism.QuantumDeterminants.Hpk k r)` using `((_root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.mem_Nset_iff m).1 hm).1`. Establish `hQm : _root_.Formalism.QuantumDeterminants.Hpk k r * (g * m)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z = m⁻¹ * (_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.Glob …`. Rewrite using `[inv_eq_hpk_mul_conjTranspose_mul_hpk_of_mem_UH hmUH]`.

Simplify using `only [conjTranspose_mul, Matrix.mul_assoc, hpk_mul_hpk_mul_eq_self]`. Establish `hC : (m⁻¹ * (_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z))ᴴ * (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z') = ((_root_.Fo …`. Rewrite using `[conjTranspose_mul m⁻¹, inv_eq_hpk_mul_conjTranspose_mul_hpk_of_mem_UH hmUH]`. Simplify using `only [conjTranspose_mul, conjTranspose_conjTranspose, hpk_conjTranspose_eq_self', Matrix.mul_assoc, hpk_mul_hpk_mul_eq_self, hmF]`. Establish `he : U.adjugateᴴ *ᵥ Pi.single (Fin.last r) 1 = Pi.single (Fin.last r) 1`.

Use extensionality with `a`. Simplify using `[mulVec_single_one, conjTranspose_apply, adjugate_upUni_last_apply hU, Pi.single_apply]`. Rewrite using `[rW_mulVec_adjugate_zhat_single_last_eq, rW_mulVec_adjugate_zhat_single_last_eq, gram_eq_conjTranspose_hpk_mul_flagMat_mul, gram_eq_conjTranspose_hpk_mul_flagMat_mul, hQm, hC, adjugate_mul_distrib, conjTranspose_mul, ← mulVec_mulVec _ (adjugate _)ᴴ, he, ← mulVec_mulVec _ m⁻¹]`. Conclude with `prW_mulVec_eq_of_mem_nset_of_tail_eq_zero ((_root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.nilpotent_subgroup k r).2.2 m hm) (mulVec_adjugate_single_last_apply_eq_zero_of_lt _ _)`.
-/
theorem _root_.GlobalTheory.WigSh.omg_mul_N : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ))
    (g m : _root_.Formalism.FourierDecayAlt.Q.Mx k r), _root_.Formalism.QuantumDeterminants.inWb k r z → _root_.Formalism.QuantumDeterminants.inWb k r z' →
    g ∈ _root_.Formalism.QuantumDeterminants.UH (_root_.Formalism.QuantumDeterminants.Hpk k r) → m ∈ _root_.Formalism.QuantumDeterminants.Nset k r →
    _root_.GlobalTheory.WigSh.omg k r z z' (g * m) = _root_.GlobalTheory.WigSh.omg k r z z' g := by
  intro k r z z' g m _ hz' _ hm
  obtain ⟨U, hU, hmF⟩ := _root_.GlobalTheory.LeadingMinorInv.exists_N k r z' hz' m hm
  have hmUH : m ∈ _root_.Formalism.QuantumDeterminants.UH (_root_.Formalism.QuantumDeterminants.Hpk k r) := ((_root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.mem_Nset_iff m).1 hm).1
  have hQm : _root_.Formalism.QuantumDeterminants.Hpk k r * (g * m)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z =
      m⁻¹ * (_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z) := by
    rw [inv_eq_hpk_mul_conjTranspose_mul_hpk_of_mem_UH hmUH]
    simp only [conjTranspose_mul, Matrix.mul_assoc, hpk_mul_hpk_mul_eq_self]
  have hC : (m⁻¹ * (_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z))ᴴ *
      (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z') =
      ((_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z)ᴴ *
        (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z')) * U := by
    rw [conjTranspose_mul m⁻¹, inv_eq_hpk_mul_conjTranspose_mul_hpk_of_mem_UH hmUH]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hpk_conjTranspose_eq_self',
      Matrix.mul_assoc, hpk_mul_hpk_mul_eq_self, hmF]
  have he : U.adjugateᴴ *ᵥ Pi.single (Fin.last r) 1 = Pi.single (Fin.last r) 1 := by
    ext a
    simp [mulVec_single_one, conjTranspose_apply, adjugate_upUni_last_apply hU, Pi.single_apply]
  rw [rW_mulVec_adjugate_zhat_single_last_eq, rW_mulVec_adjugate_zhat_single_last_eq, gram_eq_conjTranspose_hpk_mul_flagMat_mul, gram_eq_conjTranspose_hpk_mul_flagMat_mul, hQm, hC, adjugate_mul_distrib, conjTranspose_mul,
    ← mulVec_mulVec _ (adjugate _)ᴴ, he, ← mulVec_mulVec _ m⁻¹]
  exact prW_mulVec_eq_of_mem_nset_of_tail_eq_zero ((_root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.nilpotent_subgroup k r).2.2 m hm)
    (mulVec_adjugate_single_last_apply_eq_zero_of_lt _ _)

end GlobalTheory.WigSh
