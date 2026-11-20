import Formalism.HermitianCurvature.StatementJCT
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InvariantOperatorUnderJacquet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QNFAsm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelTransfer.SecondCapelliMinorLevel
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelLiftBasics.LevelGroupUnitaryHermitian
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelImageArithmetic.GlevImageOf

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.JCTx5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section typ

variable {k i r' : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `j`. Establish `hjl` using `j.isLt`. Establish `hj` using `congrFun h ⟨j.val + i, by omega⟩`. Establish `hc : i ≤ j.val + i ∧ j.val + i < 2 * r' + k + 1 + i` using `⟨Nat.le_add_left _ _, by omega⟩`. Simplify using `only [liftVec, Fin.val_mk, dif_pos hc] at hj`.

Use `first`. Consider the case `simpa using hj`. Consider the case `(simp at hj; rwa [if_pos (by omega)] at hj)`.
-/
theorem liftVec_inj {v w : Fin (2 * r' + k + 1) → ℂ} (h : liftVec k i r' v = liftVec k i r' w) : v = w := by
  funext j
  have hjl := j.isLt
  have hj := congrFun h ⟨j.val + i, by omega⟩
  have hc : i ≤ j.val + i ∧ j.val + i < 2 * r' + k + 1 + i := ⟨Nat.le_add_left _ _, by omega⟩
  simp only [liftVec, Fin.val_mk, dif_pos hc] at hj
  first
    | simpa using hj
    | (simp at hj; rwa [if_pos (by omega)] at hj)

/- English proof (translation)
Introduce `a b h`. Apply `Fin.ext` to reduce the goal to its premises. Establish `h'` using `congrArg Fin.val h`. Simplify using `only [levPos, Fin.val_mk] at h'`. Use linear arithmetic over natural numbers and integers.
-/
private theorem levPos_injective : Function.Injective (levPos k i r') := by
  intro a b h
  apply Fin.ext
  have h' := congrArg Fin.val h
  simp only [levPos, Fin.val_mk] at h'
  omega

/- English proof (translation)
Establish `hj` using `j.isLt`. Establish `hj' : (j : ℕ) ≤ 2 * r' + k` using `by omega`. Simplify using `[liftVec, levPos, hj']`. Apply the tactic sequence `all_goals first`. Consider the case `(intro h; omega)`.

Consider the case `rw [if_pos hj']`. Consider the case `rfl`.
-/
private theorem liftVec_apply_levPos (x : Fin (2 * r' + k + 1) → ℂ) (j : Fin (2 * r' + k + 1)) :
    liftVec k i r' x (levPos k i r' j) = x j := by
  have hj := j.isLt
  have hj' : (j : ℕ) ≤ 2 * r' + k := by omega
  simp [liftVec, levPos, hj']
  all_goals first
    | (intro h; omega)
    | rw [if_pos hj']
    | rfl

/- English proof (translation)
Simplify using `only [liftVec]`. Use `split_ifs with hc`. It suffices to derive a contradiction. Apply `hp` to reduce the goal to its premises. Use `⟨⟨p.val - i, by omega⟩, ?_⟩` and prove the remaining obligations.

Apply `Fin.ext` to reduce the goal to its premises. Simplify using `only [levPos, Fin.val_mk]`. Use linear arithmetic over natural numbers and integers. Both sides reduce to the same expression.
-/
private theorem liftVec_apply_eq_zero_of_not_mem_range (x : Fin (2 * r' + k + 1) → ℂ) (p : Fin (2 * (i + r') + k + 1))
    (hp : p ∉ Set.range (levPos k i r')) : liftVec k i r' x p = 0 := by
  simp only [liftVec]
  split_ifs with hc
  · exfalso
    apply hp
    refine ⟨⟨p.val - i, by omega⟩, ?_⟩
    apply Fin.ext
    simp only [levPos, Fin.val_mk]
    omega
  · rfl

/- English proof (translation)
Unfold `dotProduct`. Use `symm`. Apply `Fintype.sum_of_injective (levPos k i r') levPos_injective` to reduce the goal to its premises. Introduce `p hp`. Simplify using `only [liftVec_apply_eq_zero_of_not_mem_range x p hp, zero_mul]`.

Introduce `j`. Simplify using `only [liftVec_apply_levPos]`.
-/
private theorem liftVec_dotProduct_eq_dotProduct_levPos (x : Fin (2 * r' + k + 1) → ℂ) (w : Fin (2 * (i + r') + k + 1) → ℂ) :
    liftVec k i r' x ⬝ᵥ w = x ⬝ᵥ (fun j => w (levPos k i r' j)) := by
  unfold dotProduct
  symm
  apply Fintype.sum_of_injective (levPos k i r') levPos_injective
  · intro p hp
    simp only [liftVec_apply_eq_zero_of_not_mem_range x p hp, zero_mul]
  · intro j
    simp only [liftVec_apply_levPos]

/- English proof (translation)
Take `⟨jv, hjv⟩` from `j`. Take `⟨qv, hqv⟩` from `q`. Simplify using `only [Hpk, levPos, Fin.ext_iff, Fin.val_mk]`. Establish `e1 : (jv + i < i + r' ∧ jv + i + (qv + i) = 2 * (i + r') + k) ↔ (jv < r' ∧ jv + qv = 2 * r' + k)`. Use linear arithmetic over natural numbers and integers.

Establish `e2 : (qv + i < i + r' ∧ jv + i + (qv + i) = 2 * (i + r') + k) ↔ (qv < r' ∧ jv + qv = 2 * r' + k)`. Use linear arithmetic over natural numbers and integers. Establish `e3 : (i + r' ≤ jv + i ∧ jv + i ≤ i + r' + k ∧ jv + i = qv + i) ↔ (r' ≤ jv ∧ jv ≤ r' + k ∧ jv = qv)`. Use linear arithmetic over natural numbers and integers. Establish `e4 : (jv + i = i + r' + k) ↔ (jv = r' + k)`.

Use linear arithmetic over natural numbers and integers. Simplify using `only [e1, e2, e3, e4]`.
-/
private theorem hpk_levPos_levPos (j q : Fin (2 * r' + k + 1)) :
    Hpk k (i + r') (levPos k i r' j) (levPos k i r' q) = Hpk k r' j q := by
  obtain ⟨jv, hjv⟩ := j
  obtain ⟨qv, hqv⟩ := q
  simp only [Hpk, levPos, Fin.ext_iff, Fin.val_mk]
  have e1 : (jv + i < i + r' ∧ jv + i + (qv + i) = 2 * (i + r') + k) ↔ (jv < r' ∧ jv + qv = 2 * r' + k) := by
    omega
  have e2 : (qv + i < i + r' ∧ jv + i + (qv + i) = 2 * (i + r') + k) ↔ (qv < r' ∧ jv + qv = 2 * r' + k) := by
    omega
  have e3 : (i + r' ≤ jv + i ∧ jv + i ≤ i + r' + k ∧ jv + i = qv + i) ↔ (r' ≤ jv ∧ jv ≤ r' + k ∧ jv = qv) := by
    omega
  have e4 : (jv + i = i + r' + k) ↔ (jv = r' + k) := by
    omega
  simp only [e1, e2, e3, e4]

/- English proof (translation)
Establish `hj` using `j.isLt`. Establish `hq'` using `q.isLt`. Simplify using `only [Hpk, levPos, Fin.ext_iff, Fin.val_mk]`. Apply the tactic sequence `split_ifs <;> (try split_ifs) <;> (try split_ifs) <;> first | rfl | (exfalso; omega)`.
-/
private theorem hpk_levPos_apply_eq_zero_of_outside (j : Fin (2 * r' + k + 1)) (q : Fin (2 * (i + r') + k + 1))
    (hq : ¬(i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i)) :
    Hpk k (i + r') (levPos k i r' j) q = 0 := by
  have hj := j.isLt
  have hq' := q.isLt
  simp only [Hpk, levPos, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> (try split_ifs) <;> (try split_ifs) <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Simplify using `only [Matrix.mulVec]`. Rewrite using `[dotProduct_comm, liftVec_dotProduct_eq_dotProduct_levPos]`. Simplify using `only [hpk_levPos_levPos]`. Conclude with `dotProduct_comm _ _`.
-/
private theorem hpk_mulVec_liftVec_apply_levPos (x : Fin (2 * r' + k + 1) → ℂ) (j : Fin (2 * r' + k + 1)) :
    (Hpk k (i + r') *ᵥ liftVec k i r' x) (levPos k i r' j) = (Hpk k r' *ᵥ x) j := by
  simp only [Matrix.mulVec]
  rw [dotProduct_comm, liftVec_dotProduct_eq_dotProduct_levPos]
  simp only [hpk_levPos_levPos]
  exact dotProduct_comm _ _

/- English proof (translation)
Use function extensionality and compare the values at `p`. Simplify using `only [liftVec, Pi.star_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem star_liftVec (y : Fin (2 * r' + k + 1) → ℂ) :
    star (liftVec k i r' y) = liftVec k i r' (star y) := by
  funext p
  simp only [liftVec, Pi.star_apply]
  split_ifs <;> simp

/- English proof (translation)
Unfold `herm`. Rewrite using `[star_liftVec, liftVec_dotProduct_eq_dotProduct_levPos]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Conclude with `hpk_mulVec_liftVec_apply_levPos x j`.
-/
private theorem herm_hpk_liftVec_liftVec (x y : Fin (2 * r' + k + 1) → ℂ) :
    herm (Hpk k (i + r')) (liftVec k i r' x) (liftVec k i r' y) = herm (Hpk k r') x y := by
  unfold herm
  rw [star_liftVec, liftVec_dotProduct_eq_dotProduct_levPos]
  congr 1
  funext j
  exact hpk_mulVec_liftVec_apply_levPos x j

/- English proof (translation)
Unfold `herm`. Rewrite using `[star_liftVec, liftVec_dotProduct_eq_dotProduct_levPos]`. Establish `h0 : (fun j => (Hpk k (i + r') *ᵥ bvec q) (levPos k i r' j)) = 0`. Use function extensionality and compare the values at `j`. Simplify using `[bvec, Matrix.mulVec, dotProduct, Pi.single_apply, hpk_levPos_apply_eq_zero_of_outside j q hq]`.

Rewrite using `[h0, dotProduct_zero]`.
-/
private theorem herm_bvec_liftVec_eq_zero_of_outside (y : Fin (2 * r' + k + 1) → ℂ) (q : Fin (2 * (i + r') + k + 1))
    (hq : ¬(i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i)) :
    herm (Hpk k (i + r')) (bvec q) (liftVec k i r' y) = 0 := by
  unfold herm
  rw [star_liftVec, liftVec_dotProduct_eq_dotProduct_levPos]
  have h0 : (fun j => (Hpk k (i + r') *ᵥ bvec q) (levPos k i r' j)) = 0 := by
    funext j
    simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply, hpk_levPos_apply_eq_zero_of_outside j q hq]
  rw [h0, dotProduct_zero]

/- English proof (translation)
Simplify using `only [liftVec]`. Rewrite using `[dif_pos hp]`.
-/
private theorem liftVec_apply_of_mid (x : Fin (2 * r' + k + 1) → ℂ) (p : Fin (2 * (i + r') + k + 1))
    (hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i) : liftVec k i r' x p = x ⟨p.val - i, by omega⟩ := by
  simp only [liftVec]
  rw [dif_pos hp]

/- English proof (translation)
Use function extensionality and compare the values at `p`. Simplify using `only [bvec, liftVec, Pi.single_apply, Fin.ext_iff, Fin.val_mk]`. Apply the tactic sequence `split_ifs <;> (try split_ifs) <;> (try split_ifs) <;> first | rfl | (exfalso; omega)`.
-/
private theorem bvec_eq_liftVec_bvec_of_mid (q : Fin (2 * (i + r') + k + 1)) (hq : i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i) :
    bvec q = liftVec k i r' (bvec (⟨q.val - i, by omega⟩ : Fin (2 * r' + k + 1))) := by
  funext p
  simp only [bvec, liftVec, Pi.single_apply, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> (try split_ifs) <;> (try split_ifs) <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Unfold `unitB`. Use extensionality with `p q`. Unfold `PIQnLT.Lz`. Simplify using `only [Matrix.of_apply]`. Distinguish the cases in `hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i`.

Distinguish the cases in `hq : i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i`. Rewrite using `[dif_pos hp, dif_pos hq, liftVec_apply_of_mid _ p hp, bvec_eq_liftVec_bvec_of_mid q hq, herm_hpk_liftVec_liftVec]`. Rewrite using `[dif_pos hp, dif_neg hq, herm_bvec_liftVec_eq_zero_of_outside _ q hq, mul_zero]`. Rewrite using `[dif_neg hp]`. Establish `h0 : liftVec k i r' (Bs a) p = 0`.

Simplify using `only [liftVec]`. Rewrite using `[dif_neg hp]`. Rewrite using `[h0, zero_mul]`.
-/
theorem unitB_lift {m : ℕ} (Bs : Fin m → Fin (2 * r' + k + 1) → ℂ) (a b : Fin m) :
    unitB (Hpk k (i + r')) (fun c => liftVec k i r' (Bs c)) a b =
      PIQnLT.Lz k i r' (unitB (Hpk k r') Bs a b) := by
  unfold unitB
  ext p q
  unfold PIQnLT.Lz
  simp only [Matrix.of_apply]
  by_cases hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i
  · by_cases hq : i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i
    · rw [dif_pos hp, dif_pos hq, liftVec_apply_of_mid _ p hp, bvec_eq_liftVec_bvec_of_mid q hq, herm_hpk_liftVec_liftVec]
    · rw [dif_pos hp, dif_neg hq, herm_bvec_liftVec_eq_zero_of_outside _ q hq, mul_zero]
  · rw [dif_neg hp]
    have h0 : liftVec k i r' (Bs a) p = 0 := by
      simp only [liftVec]
      rw [dif_neg hp]
    rw [h0, zero_mul]

/- English proof (translation)
Unfold `hpart1`. Rewrite using `[PIQnLT.hpk_inv, PIQnLT.hpk_inv, PIQnLT.Lz_conjTranspose, PIQnLT.hpk_mul_Lz, PIQnLT.Lz_mul_hpk, PIQnLT.Lz_smul, PIQnLT.Lz_sub]`.
-/
theorem hpart1_Lz (Z : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    hpart1 (Hpk k (i + r')) (PIQnLT.Lz k i r' Z) = PIQnLT.Lz k i r' (hpart1 (Hpk k r') Z) := by
  unfold hpart1
  rw [PIQnLT.hpk_inv, PIQnLT.hpk_inv, PIQnLT.Lz_conjTranspose, PIQnLT.hpk_mul_Lz, PIQnLT.Lz_mul_hpk,
    PIQnLT.Lz_smul, PIQnLT.Lz_sub]

/- English proof (translation)
Unfold `hpart2`. Rewrite using `[PIQnLT.hpk_inv, PIQnLT.hpk_inv, PIQnLT.Lz_conjTranspose, PIQnLT.hpk_mul_Lz, PIQnLT.Lz_mul_hpk, PIQnLT.Lz_smul, PIQnLT.Lz_add]`.
-/
theorem hpart2_Lz (Z : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    hpart2 (Hpk k (i + r')) (PIQnLT.Lz k i r' Z) = PIQnLT.Lz k i r' (hpart2 (Hpk k r') Z) := by
  unfold hpart2
  rw [PIQnLT.hpk_inv, PIQnLT.hpk_inv, PIQnLT.Lz_conjTranspose, PIQnLT.hpk_mul_Lz, PIQnLT.Lz_mul_hpk,
    PIQnLT.Lz_smul, PIQnLT.Lz_add]

variable {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]

/- English proof (translation)
Unfold `dRep`. Use `congr 1`. Use function extensionality and compare the values at `t`. Rewrite using `[← PIQnLT.Lz_smul, PIQnLT.exp_Lz PI.QnLevBasicsW.level_group_homomorphism]`.
-/
theorem dRep_Lz (π0 : Mx k (i + r') → (Wp →L[ℂ] Wp)) (X : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ)
    (v : Wp) : dRep π0 (PIQnLT.Lz k i r' X) v = dRep (fun y => π0 (ιLev k i r' y)) X v := by
  unfold dRep
  congr 1
  funext t
  rw [← PIQnLT.Lz_smul, PIQnLT.exp_Lz PI.QnLevBasicsW.level_group_homomorphism]

/- English proof (translation)
Unfold `EcRep`. Rewrite using `[hpart1_Lz, hpart2_Lz, dRep_Lz, dRep_Lz]`.
-/
theorem ecRep_Lz (π0 : Mx k (i + r') → (Wp →L[ℂ] Wp)) (Z : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ)
    (v : Wp) : EcRep (Hpk k (i + r')) π0 (PIQnLT.Lz k i r' Z) v =
      EcRep (Hpk k r') (fun y => π0 (ιLev k i r' y)) Z v := by
  unfold EcRep
  rw [hpart1_Lz, hpart2_Lz, dRep_Lz, dRep_Lz]

/- English proof (translation)
Unfold `capRep`. Establish `e : (fun a b => EcRep (Hpk k (i + r')) π0 (unitB (Hpk k (i + r')) (fun c => liftVec k i r' (Bs c)) a b)) = (fun a b => EcRep (Hpk k r') (fun y => π0 (ιLev k i r' y)) (unitB (Hpk k r') Bs a b))`. Use function extensionality and compare the values at `a b x`. Rewrite using `[unitB_lift, ecRep_Lz]`. Rewrite using `[e]`.
-/
theorem capRep_lift {m : ℕ} (π0 : Mx k (i + r') → (Wp →L[ℂ] Wp)) (Bs : Fin m → Fin (2 * r' + k + 1) → ℂ)
    (w : ℂ) (v : Wp) :
    capRep k (i + r') π0 (fun c => liftVec k i r' (Bs c)) w v = capRep k r' (fun y => π0 (ιLev k i r' y)) Bs w v := by
  unfold capRep
  have e : (fun a b => EcRep (Hpk k (i + r')) π0 (unitB (Hpk k (i + r')) (fun c => liftVec k i r' (Bs c)) a b)) =
      (fun a b => EcRep (Hpk k r') (fun y => π0 (ιLev k i r' y)) (unitB (Hpk k r') Bs a b)) := by
    funext a b x
    rw [unitB_lift, ecRep_Lz]
  rw [e]

/- English proof (translation)
Unfold `IsFrameOf at h ⊢`. Take `⟨h1, h2, h3⟩` from `h`. Use `⟨fun a => ?_, fun a b => ?_, fun a v hv => ?_⟩` and prove the remaining obligations. Unfold `inWb at h1 ⊢`. Introduce `p hp`.

Simplify using `only`. Distinguish the cases in `hm : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i`. Rewrite using `[liftVec_apply_of_mid _ p hm]`. Conclude with `h1 a _ (show p.val - i < r' ∨ r' + k < p.val - i by omega)`. Simplify using `only [liftVec]`.

Rewrite using `[dif_neg hm]`. Simplify using `only [herm_hpk_liftVec_liftVec]`. Conclude with `h2 a b`. Simplify using `only [List.mem_singleton] at hv`. Substitute `hv` using the available equality.

Simplify using `only [herm_hpk_liftVec_liftVec]`. Conclude with `h3 a z (List.mem_singleton_self z)`.
-/
theorem frame_lift {m : ℕ} (z : Fin (2 * r' + k + 1) → ℂ) (Bs : Fin m → Fin (2 * r' + k + 1) → ℂ)
    (h : IsFrameOf k r' [z] Bs) : IsFrameOf k (i + r') [liftVec k i r' z] (fun c => liftVec k i r' (Bs c)) := by
  unfold IsFrameOf at h ⊢
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun a => ?_, fun a b => ?_, fun a v hv => ?_⟩
  · unfold inWb at h1 ⊢
    intro p hp
    dsimp only
    by_cases hm : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i
    · rw [liftVec_apply_of_mid _ p hm]
      exact h1 a _ (show p.val - i < r' ∨ r' + k < p.val - i by omega)
    · simp only [liftVec]
      rw [dif_neg hm]
  · simp only [herm_hpk_liftVec_liftVec]
    exact h2 a b
  · simp only [List.mem_singleton] at hv
    subst hv
    simp only [herm_hpk_liftVec_liftVec]
    exact h3 a z (List.mem_singleton_self z)

/- English proof (translation)
Use `continuous_matrix fun p q => ?_` and prove the remaining obligations. Simplify using `only [ιLev]`. Use `split_ifs`. Apply the tactic sequence `all_goals first`. Consider the case `exact continuous_const`.

Consider the case `exact continuous_id.matrix_elem _ _`. Consider the case `exact (continuous_apply _).comp (continuous_apply _)`. Consider the case `fun_prop`.
-/
theorem continuous_ιLev : Continuous (ιLev k i r') := by
  refine continuous_matrix fun p q => ?_
  simp only [ιLev]
  split_ifs
  all_goals first
    | exact continuous_const
    | exact continuous_id.matrix_elem _ _
    | exact (continuous_apply _).comp (continuous_apply _)
    | fun_prop

/- English proof (translation)
Establish `hG : g ∈ Glev k (i + r') ⟨i, by omega⟩` using `⟨hg.1, fun a _ => hg.2.1 a⟩`. Rewrite `hG` using `[QnGlevImageW.glevImage_of PI.QnLevBasicsW.level_group_homomorphism PI.QnLevBasicsW.level_group_unitary_hermitian k i r']`. Take `⟨y, hy, rfl⟩` from `hG`. Use `⟨y, ⟨hy, fun a => ?_, ?_⟩, rfl⟩` and prove the remaining obligations. Establish `ha` using `a.isLt`.

Take `⟨h1, h2⟩` from `hg.2.1 ⟨a.val + i, by omega⟩`. Establish `e1 : bvec (eI k (i + r') ⟨a.val + i, by omega⟩) = liftVec k i r' (bvec (eI k r' a))`. Rewrite using `[← PIQnLT.bvec_lev]`. Use `congr 1`. Apply the tactic sequence `all_goals (ext; simp [eI, levPos])`.

Establish `e2 : bvec (esI k (i + r') ⟨a.val + i, by omega⟩) = liftVec k i r' (bvec (esI k r' a))`. Rewrite using `[← PIQnLT.bvec_lev]`. Use `congr 1`. Apply the tactic sequence `all_goals (ext; simp [esI, levPos]; try omega)`. Rewrite `h1` using `[e1, PIQnLT.mulVec_liftVec]`.

Rewrite `h2` using `[e2, PIQnLT.mulVec_liftVec]`. Conclude with `⟨liftVec_inj h1, liftVec_inj h2⟩`. Establish `h` using `hg.2.2`. Rewrite `h` using `[PIQnLT.mulVec_liftVec]`. Conclude with `liftVec_inj h`.
-/
theorem uw_onto (z : Fin (2 * r' + k + 1) → ℂ) (g : Mx k (i + r')) (hg : g ∈ UWset k (i + r') (liftVec k i r' z)) :
    ∃ y ∈ UWset k r' z, ιLev k i r' y = g := by
  have hG : g ∈ Glev k (i + r') ⟨i, by omega⟩ := ⟨hg.1, fun a _ => hg.2.1 a⟩
  rw [QnGlevImageW.glevImage_of PI.QnLevBasicsW.level_group_homomorphism PI.QnLevBasicsW.level_group_unitary_hermitian k i r'] at hG
  obtain ⟨y, hy, rfl⟩ := hG
  refine ⟨y, ⟨hy, fun a => ?_, ?_⟩, rfl⟩
  · have ha := a.isLt
    obtain ⟨h1, h2⟩ := hg.2.1 ⟨a.val + i, by omega⟩
    have e1 : bvec (eI k (i + r') ⟨a.val + i, by omega⟩) = liftVec k i r' (bvec (eI k r' a)) := by
      rw [← PIQnLT.bvec_lev]; congr 1; all_goals (ext; simp [eI, levPos])
    have e2 : bvec (esI k (i + r') ⟨a.val + i, by omega⟩) = liftVec k i r' (bvec (esI k r' a)) := by
      rw [← PIQnLT.bvec_lev]; congr 1; all_goals (ext; simp [esI, levPos]; try omega)
    rw [e1, PIQnLT.mulVec_liftVec] at h1
    rw [e2, PIQnLT.mulVec_liftVec] at h2
    exact ⟨liftVec_inj h1, liftVec_inj h2⟩
  · have h := hg.2.2
    rw [PIQnLT.mulVec_liftVec] at h
    exact liftVec_inj h

/- English proof (translation)
Take `⟨hnt, hrep, hcont, huni, hirr, hcap⟩` from `h0`. Establish `hmem : ∀ y ∈ UWset k r' z, ιLev k i r' y ∈ UWset k (i + r') (liftVec k i r' z)` using `fun y hy => PI.QnLevBasicsW.level_group_unitary_weyl k i r' z y hy`. Use `⟨hnt, ⟨?_, fun a ha b hb => ?_⟩, ?_, fun h hh v => huni _ (hmem h hh) v, fun S hS => hirr S ?_, ?_⟩` and prove the remaining obligations. Use `show π0 (ιLev k i r' 1) = 1`. Rewrite using `[(PI.QnLevBasicsW.level_group_homomorphism k i r').1]`.

Conclude with `hrep.1`. Use `show π0 (ιLev k i r' (a * b)) = (π0 (ιLev k i r' a)).comp (π0 (ιLev k i r' b))`. Rewrite using `[(PI.QnLevBasicsW.level_group_homomorphism k i r').2]`. Conclude with `hrep.2 _ (hmem a ha) _ (hmem b hb)`. Conclude with `hcont.comp continuous_ιLev.continuousOn (fun y hy => hmem y hy)`.

Introduce `h hh v hv`. Take `⟨y, hy, rfl⟩` from `uw_onto z h hh`. Conclude with `hS y hy v hv`. Introduce `Bs hBs w v`. Rewrite using `[← capRep_lift]`.

Conclude with `hcap _ (frame_lift z Bs hBs) w v`.
-/
theorem isType_lev (z : Fin (2 * r' + k + 1) → ℂ) (π0 : Mx k (i + r') → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ)
    (h0 : IsType k (i + r') (liftVec k i r' z) π0 u) :
    IsType k r' z (fun y => π0 (ιLev k i r' y)) u := by
  obtain ⟨hnt, hrep, hcont, huni, hirr, hcap⟩ := h0
  have hmem : ∀ y ∈ UWset k r' z, ιLev k i r' y ∈ UWset k (i + r') (liftVec k i r' z) :=
    fun y hy => PI.QnLevBasicsW.level_group_unitary_weyl k i r' z y hy
  refine ⟨hnt, ⟨?_, fun a ha b hb => ?_⟩, ?_, fun h hh v => huni _ (hmem h hh) v, fun S hS => hirr S ?_, ?_⟩
  · show π0 (ιLev k i r' 1) = 1
    rw [(PI.QnLevBasicsW.level_group_homomorphism k i r').1]; exact hrep.1
  · show π0 (ιLev k i r' (a * b)) = (π0 (ιLev k i r' a)).comp (π0 (ιLev k i r' b))
    rw [(PI.QnLevBasicsW.level_group_homomorphism k i r').2]; exact hrep.2 _ (hmem a ha) _ (hmem b hb)
  · exact hcont.comp continuous_ιLev.continuousOn (fun y hy => hmem y hy)
  · intro h hh v hv
    obtain ⟨y, hy, rfl⟩ := uw_onto z h hh
    exact hS y hy v hv
  · intro Bs hBs w v
    rw [← capRep_lift]
    exact hcap _ (frame_lift z Bs hBs) w v

end typ

section cast

variable {k : ℕ}

/- English proof (translation)
Use `first`. Consider the case `rfl`. Consider the case `(funext j; simp [Formalism.FourierDecayAlt.D.castV])`.
-/
theorem castV_rfl {a : ℕ} (v : Fin (2 * a + k + 1) → ℂ) : Formalism.FourierDecayAlt.D.castV (k := k) (rfl : a = a) v = v := by
  first
    | rfl
    | (funext j; simp [Formalism.FourierDecayAlt.D.castV])

/- English proof (translation)
Use `first`. Consider the case `rfl`. Consider the case `(ext p q; simp [Formalism.FourierDecayAlt.D.castM])`.
-/
theorem castM_rfl {a : ℕ} (g : Formalism.FourierDecayAlt.B.Mat k a) : Formalism.FourierDecayAlt.D.castM (rfl : a = a) g = g := by
  first
    | rfl
    | (ext p q; simp [Formalism.FourierDecayAlt.D.castM])

/- English proof (translation)
Substitute `h` using the available equality. Simplify `hT` using `only [castV_rfl, castM_rfl]`.
-/
theorem isType_cast {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] {a b : ℕ} (h : a = b)
    (z : Fin (2 * a + k + 1) → ℂ) (π : Mx k b → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ)
    (hT : IsType k b (Formalism.FourierDecayAlt.D.castV h z) π u) : IsType k a z (fun g => π (Formalism.FourierDecayAlt.D.castM h g)) u := by
  subst h
  simpa only [castV_rfl, castM_rfl] using hT

/- English proof (translation)
Substitute `h` using the available equality. Rewrite using `[castV_rfl]`.
-/
theorem tz_cast {a b : ℕ} (h : a = b) (z : Fin (2 * a + k + 1) → ℂ) :
    Tz k b (Formalism.FourierDecayAlt.D.castV h z) = Tz k a z := by
  subst h
  rw [castV_rfl]

end cast

/- English proof (translation)
Take `⟨hOK, -, -, hT, hT', hty, hty'⟩` from `h0`. Establish `hjr : (j : ℕ) ≤ P.r` using `Nat.lt_succ_iff.mp j.isLt`. Establish `hj : (j : ℕ) + (P.r - j) = P.r` using `by omega`. Establish `ez : Formalism.FourierDecayAlt.D.castV hj (liftVec P.k j (P.r - j) (T.bs j).z) = T.base.z` using `T.z_lev j hjr`. Establish `ez' : Formalism.FourierDecayAlt.D.castV hj (liftVec P.k j (P.r - j) (T.bs j).z') = T.base.z'` using `T.z'_lev j hjr`.

Establish `hπ : (T.bs j).π = fun y => T.base.π (Formalism.FourierDecayAlt.D.castM hj (ιLev P.k j (P.r - j) y))`. Use function extensionality and compare the values at `fun y => T.π_lev j hjr y`. Establish `hπ' : (T.bs j).π' = fun y => T.base.π' (Formalism.FourierDecayAlt.D.castM hj (ιLev P.k j (P.r - j) y))`. Use function extensionality and compare the values at `fun y => T.π'_lev j hjr y`. Establish `hWb` using `PI.QnLevBasicsW.level_group_isotropic_vector P.k j (P.r - j) (T.bs j).z (T.bs j).z_mem`.

Establish `hWb'` using `PI.QnLevBasicsW.level_group_isotropic_vector P.k j (P.r - j) (T.bs j).z' (T.bs j).z'_mem`. Use `⟨⟨hOK.k_pos, hOK.T_pos, hOK.T'_pos, hOK.int_u, hOK.int_u', hOK.gap⟩, (T.bs j).z_mem, (T.bs j).z'_mem, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show Tz P.k (P.r - j) (T.bs j).z = P.T`. Rewrite using `[← hWb.2, ← tz_cast hj, ez, hT]`. Use `show Tz P.k (P.r - j) (T.bs j).z' = P.T'`.

Rewrite using `[← hWb'.2, ← tz_cast hj, ez', hT']`. Rewrite using `[hπ]`. Conclude with `isType_lev (i := j) (r' := P.r - j) (T.bs j).z (fun g => T.base.π (Formalism.FourierDecayAlt.D.castM hj g)) P.u (isType_cast hj (liftVec P.k j (P.r - j) (T.bs j).z) T.base.π P.u (by rw [ez]; exact hty))`. Rewrite using `[hπ']`. Conclude with `isType_lev (i := j) (r' := P.r - j) (T.bs j).z' (fun g => T.base.π' (Formalism.FourierDecayAlt.D.castM hj g)) P.u' (isType_cast hj (liftVec P.k j (P.r - j) (T.bs j).z') T.base.π' P.u' (by rw [ez']; exact hty'))`.
-/
theorem isPlace_lev {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (P : M.Par) (T : Formalism.FourierDecayAlt.D.LevTower P.k P.r Wp Wq) (j : Fin (P.r + 1))
    (h0 : IsPlace P T.base.z T.base.z' T.base.π T.base.π') :
    IsPlace (Formalism.FourierDecayAlt.JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' := by
  obtain ⟨hOK, -, -, hT, hT', hty, hty'⟩ := h0
  have hjr : (j : ℕ) ≤ P.r := Nat.lt_succ_iff.mp j.isLt
  have hj : (j : ℕ) + (P.r - j) = P.r := by omega
  have ez : Formalism.FourierDecayAlt.D.castV hj (liftVec P.k j (P.r - j) (T.bs j).z) = T.base.z := T.z_lev j hjr
  have ez' : Formalism.FourierDecayAlt.D.castV hj (liftVec P.k j (P.r - j) (T.bs j).z') = T.base.z' := T.z'_lev j hjr
  have hπ : (T.bs j).π = fun y => T.base.π (Formalism.FourierDecayAlt.D.castM hj (ιLev P.k j (P.r - j) y)) :=
    funext fun y => T.π_lev j hjr y
  have hπ' : (T.bs j).π' = fun y => T.base.π' (Formalism.FourierDecayAlt.D.castM hj (ιLev P.k j (P.r - j) y)) :=
    funext fun y => T.π'_lev j hjr y
  have hWb := PI.QnLevBasicsW.level_group_isotropic_vector P.k j (P.r - j) (T.bs j).z (T.bs j).z_mem
  have hWb' := PI.QnLevBasicsW.level_group_isotropic_vector P.k j (P.r - j) (T.bs j).z' (T.bs j).z'_mem
  refine ⟨⟨hOK.k_pos, hOK.T_pos, hOK.T'_pos, hOK.int_u, hOK.int_u', hOK.gap⟩, (T.bs j).z_mem, (T.bs j).z'_mem,
    ?_, ?_, ?_, ?_⟩
  · show Tz P.k (P.r - j) (T.bs j).z = P.T
    rw [← hWb.2, ← tz_cast hj, ez, hT]
  · show Tz P.k (P.r - j) (T.bs j).z' = P.T'
    rw [← hWb'.2, ← tz_cast hj, ez', hT']
  · rw [hπ]
    exact isType_lev (i := j) (r' := P.r - j) (T.bs j).z (fun g => T.base.π (Formalism.FourierDecayAlt.D.castM hj g)) P.u
      (isType_cast hj (liftVec P.k j (P.r - j) (T.bs j).z) T.base.π P.u (by rw [ez]; exact hty))
  · rw [hπ']
    exact isType_lev (i := j) (r' := P.r - j) (T.bs j).z' (fun g => T.base.π' (Formalism.FourierDecayAlt.D.castM hj g)) P.u'
      (isType_cast hj (liftVec P.k j (P.r - j) (T.bs j).z') T.base.π' P.u' (by rw [ez']; exact hty'))

section haar

/- English proof (translation)
Substitute `h` using the available equality. Use `first`. Consider the case `exact ⟨Bs.μG, Bs.haarG⟩`. Consider the case `(cases Bs`. Use `⟨_, ?_⟩` and prove the remaining obligations.

Use the proof step `assumption)`.
-/
theorem exists_haar_level_zero {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {k a : ℕ} (h : a = 0) (Bs : Formalism.FourierDecayAlt.B.RealPlaceData k a Wp Wq) :
    ∃ μ : Measure (Mt k 0), Formalism.FourierDecayAlt.B.IsHaarOn (Formalism.FourierDecayAlt.B.GV k 0) μ := by
  subst h
  first
    | exact ⟨Bs.μG, Bs.haarG⟩
    | (cases Bs
       refine ⟨_, ?_⟩
       assumption)

def embL (k r' : ℕ) (x : Mt k 0) : Mt k r' := ιLev k r' 0 x

def projL (k r' : ℕ) (x : Mt k r') : Mt k 0 := fun p q => x (levPos k r' 0 p) (levPos k r' 0 q)

variable {k r' : ℕ}

/- English proof (translation)
Use `first`. Consider the case `exact continuous_ιLev`. Consider the case `(unfold embL; exact continuous_ιLev)`.
-/
theorem continuous_embL : Continuous (embL k r') := by
  first
    | exact continuous_ιLev
    | (unfold embL; exact continuous_ιLev)

/- English proof (translation)
Unfold `projL`. Use `first`. Consider the case `fun_prop`. Consider the case `exact continuous_pi fun p => continuous_pi fun q => continuous_apply_apply _ _`.
-/
theorem continuous_projL : Continuous (projL k r') := by
  unfold projL
  first
    | fun_prop
    | exact continuous_pi fun p => continuous_pi fun q => continuous_apply_apply _ _

/- English proof (translation)
Use function extensionality and compare the values at `p q`. Establish `hp` using `p.isLt`. Establish `hq` using `q.isLt`. Establish `hp' : (p : ℕ) ≤ k` using `by omega`. Establish `hq' : (q : ℕ) ≤ k` using `by omega`.

Simplify using `[projL, embL, ιLev, levPos, hp', hq']`.
-/
theorem projL_embL (x : Mt k 0) : projL k r' (embL k r' x) = x := by
  funext p q
  have hp := p.isLt
  have hq := q.isLt
  have hp' : (p : ℕ) ≤ k := by omega
  have hq' : (q : ℕ) ≤ k := by omega
  simp [projL, embL, ιLev, levPos, hp', hq']

/- English proof (translation)
Unfold `Glev`. Simplify using `only [Set.setOf_and, Set.setOf_forall, Set.setOf_mem_eq]`. Use `IsClosed.inter ?_ (isClosed_iInter fun a => isClosed_iInter fun _ => IsClosed.inter ?_ ?_)` and prove the remaining obligations. Unfold `UH first`. Consider the case `exact isClosed_eq (by fun_prop) continuous_const`.

Consider the case `exact isClosed_eq (((continuous_id.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul continuous_id) continuous_const`. Apply the tactic sequence `all_goals first`. Consider the case `exact isClosed_eq (by fun_prop) continuous_const`. Consider the case `exact isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const`.
-/
theorem glev_closed (k r : ℕ) (i : Fin (r + 1)) : IsClosed (Glev k r i) := by
  unfold Glev
  simp only [Set.setOf_and, Set.setOf_forall, Set.setOf_mem_eq]
  refine IsClosed.inter ?_ (isClosed_iInter fun a => isClosed_iInter fun _ => IsClosed.inter ?_ ?_)
  · unfold UH
    first
      | exact isClosed_eq (by fun_prop) continuous_const
      | exact isClosed_eq (((continuous_id.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul continuous_id) continuous_const
  all_goals first
    | exact isClosed_eq (by fun_prop) continuous_const
    | exact isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const

/- English proof (translation)
Use `first`. Consider the case `exact (glev_closed k r i).measurableSet`. Consider the case `exact IsClosed.measurableSet (α := Mt k r) (glev_closed k r i)`. Consider the case `exact @IsClosed.measurableSet (Mt k r) _ _ _ _ (glev_closed k r i)`.
-/
theorem glev_measurable (k r : ℕ) (i : Fin (r + 1)) : @MeasurableSet (Mt k r) _ (Glev k r i) := by
  first
    | exact (glev_closed k r i).measurableSet
    | exact IsClosed.measurableSet (α := Mt k r) (glev_closed k r i)
    | exact @IsClosed.measurableSet (Mt k r) _ _ _ _ (glev_closed k r i)

/- English proof (translation)
Establish `hU : Glev k r' (Fin.last r') = ιLev k r' 0 '' UH (Hpk k 0)` using `QnGlevImageW.glevImage_of PI.QnLevBasicsW.level_group_homomorphism PI.QnLevBasicsW.level_group_unitary_hermitian k r' 0`. Establish `hm : Measurable (embL k r')` using `continuous_embL.measurable`. Establish `hhom` using `PI.QnLevBasicsW.level_group_homomorphism k r' 0`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `(Measure.map_apply hm (glev_measurable k r' (Fin.last r')).compl).trans ?_` and prove the remaining obligations.

Apply `measure_mono_null _ h0.conc` to reduce the goal to its premises. Introduce `x hx hxG`. Apply `hx` to reduce the goal to its premises. Rewrite using `[hU]`. Conclude with `⟨x, hxG, rfl⟩`.

Introduce `a ha`. Rewrite `ha` using `[hU]`. Take `⟨a0, ha0, rfl⟩` from `ha`. Establish `hl : Measurable (lmulM (k` using `k) (r := r') (ιLev k r' 0 a0)) := Continuous.measurable (by unfold lmulM; exact continuous_const.matrix_mul continuous_id)`. Establish `hl0 : Measurable (lmulM (k` using `k) (r := 0) a0) := Continuous.measurable (by unfold lmulM; exact continuous_const.matrix_mul continuous_id)`.

Rewrite using `[Measure.map_map hl hm]`. Establish `e : lmulM (ιLev k r' 0 a0) ∘ embL k r' = embL k r' ∘ lmulM a0`. Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp_apply, lmulM, embL]`. Rewrite using `[hhom.2]`.

Both sides reduce to the same expression. Rewrite using `[e, ← Measure.map_map hm hl0, h0.left a0 ha0]`. Introduce `a ha`. Rewrite `ha` using `[hU]`. Take `⟨a0, ha0, rfl⟩` from `ha`.

Establish `hl : Measurable (Formalism.FourierDecayAlt.B.rmulF (n` using `2 * r' + k + 1) (ιLev k r' 0 a0)) := Continuous.measurable (by unfold Formalism.FourierDecayAlt.B.rmulF; exact continuous_id.matrix_mul continuous_const)`. Establish `hl0 : Measurable (Formalism.FourierDecayAlt.B.rmulF (n` using `2 * 0 + k + 1) a0) := Continuous.measurable (by unfold Formalism.FourierDecayAlt.B.rmulF; exact continuous_id.matrix_mul continuous_const)`. Rewrite using `[Measure.map_map hl hm]`. Establish `e : Formalism.FourierDecayAlt.B.rmulF (ιLev k r' 0 a0) ∘ embL k r' = embL k r' ∘ Formalism.FourierDecayAlt.B.rmulF a0`. Use function extensionality and compare the values at `x`.

Simplify using `only [Function.comp_apply, Formalism.FourierDecayAlt.B.rmulF, embL]`. Rewrite using `[hhom.2]`. Both sides reduce to the same expression. Rewrite using `[e, ← Measure.map_map hm hl0, h0.right a0 ha0]`. Introduce `K hK`.

Rewrite using `[Measure.map_apply hm hK.isClosed.measurableSet]`. Use `lt_of_le_of_lt (measure_mono ?_) (h0.finite_compact _ (hK.image continuous_projL))` and prove the remaining obligations. Introduce `x hx`. Conclude with `⟨embL k r' x, hx, projL_embL x⟩`. Introduce `h`.

Conclude with `h0.ne_zero ((Measure.map_eq_zero_iff hm.aemeasurable).mp h)`.
-/
theorem haar_glev (μ0 : Measure (Mt k 0)) (h0 : Formalism.FourierDecayAlt.B.IsHaarOn (Formalism.FourierDecayAlt.B.GV k 0) μ0) :
    Formalism.FourierDecayAlt.B.IsHaarOn (Glev k r' (Fin.last r')) (μ0.map (embL k r')) := by
  have hU : Glev k r' (Fin.last r') = ιLev k r' 0 '' UH (Hpk k 0) :=
    QnGlevImageW.glevImage_of PI.QnLevBasicsW.level_group_homomorphism PI.QnLevBasicsW.level_group_unitary_hermitian k r' 0
  have hm : Measurable (embL k r') := continuous_embL.measurable
  have hhom := PI.QnLevBasicsW.level_group_homomorphism k r' 0
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine (Measure.map_apply hm (glev_measurable k r' (Fin.last r')).compl).trans ?_
    apply measure_mono_null _ h0.conc
    intro x hx hxG
    apply hx
    rw [hU]; exact ⟨x, hxG, rfl⟩
  · intro a ha
    rw [hU] at ha
    obtain ⟨a0, ha0, rfl⟩ := ha
    have hl : Measurable (lmulM (k := k) (r := r') (ιLev k r' 0 a0)) :=
      Continuous.measurable (by unfold lmulM; exact continuous_const.matrix_mul continuous_id)
    have hl0 : Measurable (lmulM (k := k) (r := 0) a0) :=
      Continuous.measurable (by unfold lmulM; exact continuous_const.matrix_mul continuous_id)
    rw [Measure.map_map hl hm]
    have e : lmulM (ιLev k r' 0 a0) ∘ embL k r' = embL k r' ∘ lmulM a0 := by
      funext x; simp only [Function.comp_apply, lmulM, embL]; rw [hhom.2]; rfl
    rw [e, ← Measure.map_map hm hl0, h0.left a0 ha0]
  · intro a ha
    rw [hU] at ha
    obtain ⟨a0, ha0, rfl⟩ := ha
    have hl : Measurable (Formalism.FourierDecayAlt.B.rmulF (n := 2 * r' + k + 1) (ιLev k r' 0 a0)) :=
      Continuous.measurable (by unfold Formalism.FourierDecayAlt.B.rmulF; exact continuous_id.matrix_mul continuous_const)
    have hl0 : Measurable (Formalism.FourierDecayAlt.B.rmulF (n := 2 * 0 + k + 1) a0) :=
      Continuous.measurable (by unfold Formalism.FourierDecayAlt.B.rmulF; exact continuous_id.matrix_mul continuous_const)
    rw [Measure.map_map hl hm]
    have e : Formalism.FourierDecayAlt.B.rmulF (ιLev k r' 0 a0) ∘ embL k r' = embL k r' ∘ Formalism.FourierDecayAlt.B.rmulF a0 := by
      funext x; simp only [Function.comp_apply, Formalism.FourierDecayAlt.B.rmulF, embL]; rw [hhom.2]; rfl
    rw [e, ← Measure.map_map hm hl0, h0.right a0 ha0]
  · intro K hK
    rw [Measure.map_apply hm hK.isClosed.measurableSet]
    refine lt_of_le_of_lt (measure_mono ?_) (h0.finite_compact _ (hK.image continuous_projL))
    intro x hx
    exact ⟨embL k r' x, hx, projL_embL x⟩
  · intro h
    exact h0.ne_zero ((Measure.map_eq_zero_iff hm.aemeasurable).mp h)

end haar

section cut

/- English proof (translation)
Introduce `a b ha hab`. Proceed by induction on `b, hab using Nat.le_induction with`. Consider the case `base => intro _`. Conclude with `le_rfl`. Consider the case `succ n hn ih`.

Introduce `hbk`. Conclude with `le_trans (hU n (by omega) (by omega)) (ih (by omega))`.
-/
theorem anti_of (U : ℕ → ℝ) (k : ℕ) (hU : ∀ i, 1 ≤ i → i ≤ k - 1 → U (i + 1) ≤ U i) :
    ∀ a b, 1 ≤ a → a ≤ b → b ≤ k → U b ≤ U a := by
  intro a b ha hab
  induction b, hab using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ n hn ih =>
    intro hbk
    exact le_trans (hU n (by omega) (by omega)) (ih (by omega))

/- English proof (translation)
Establish `hA : ∀ a b, 1 ≤ a → a ≤ b → b ≤ k → U b ≤ U a` using `anti_of U k (fun i h1 h2 => by linarith [(hgap i h1 h2).1])`. Establish `hA' : ∀ a b, 1 ≤ a → a ≤ b → b ≤ k → U' b ≤ U' a` using `anti_of U' k (fun i h1 h2 => by linarith [(hgap i h1 h2).2.1])`. Take `⟨hy1, hy2⟩` from `hy`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `i hi1 hik ρi h1 h2 h3 h4 e he1 he2 h`.

Break down `Nat.lt_or_ge i l with hli | hli` into its components or cases. Establish `h5` using `hA' (i + 1) l (by omega) (by omega) hlk`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h5` using `hA l i hl1 hli (by omega)`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `i hi1 hik e he1 he2`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Break down `Nat.lt_or_ge i l with hli | hli` into its components or cases. Establish `h5` using `hA' (i + 1) l (by omega) (by omega) hlk`.

Establish `h6` using `(hgap i hi1 (by omega)).2.2.2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h5` using `hA l i hl1 hli hik`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `h`.

Break down `Nat.lt_or_ge l i with hli | hli` into its components or cases. Establish `h5` using `hA l (i - 1) hl1 (by omega) (by omega)`. Establish `h6` using `(hgap (i - 1) (by omega) (by omega)).2.2.2`. Rewrite `h6` using `[Nat.sub_add_cancel (by omega : 1 ≤ i)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h5` using `hA' i l hi1 hli hlk`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cut_facts (U U' : ℕ → ℝ) (k l : ℕ) (hl1 : 1 ≤ l) (hlk : l ≤ k)
    (hgap : ∀ i, 1 ≤ i → i ≤ k - 1 →
      U (i + 1) ≤ U i - 1 ∧ U' (i + 1) ≤ U' i - 1 ∧ U (i + 1) ≤ U' i - 1 ∧ U' (i + 1) ≤ U i - 1)
    (y : ℝ) (hy : U l + 2 ≤ -y ∧ -y ≤ U' l - 2) :
    (∀ i, 1 ≤ i → i ≤ k - 1 → ∀ ρi : ℝ, U (i + 1) + 1 / 2 ≤ ρi → U' (i + 1) + 1 / 2 ≤ ρi →
      ρi ≤ U i - 1 / 2 → ρi ≤ U' i - 1 / 2 → ∀ e : ℝ, -1 ≤ e → e ≤ 1 → y + e + ρi ≠ 0) ∧
    (∀ i, 1 ≤ i → i ≤ k → ∀ e : ℝ, -1 ≤ e → e ≤ 0 → y + e + 1 / 2 + U i ≠ 0 ∧ y + e + 1 / 2 + U' i ≠ 0) := by
  have hA : ∀ a b, 1 ≤ a → a ≤ b → b ≤ k → U b ≤ U a :=
    anti_of U k (fun i h1 h2 => by linarith [(hgap i h1 h2).1])
  have hA' : ∀ a b, 1 ≤ a → a ≤ b → b ≤ k → U' b ≤ U' a :=
    anti_of U' k (fun i h1 h2 => by linarith [(hgap i h1 h2).2.1])
  obtain ⟨hy1, hy2⟩ := hy
  refine ⟨?_, ?_⟩
  · intro i hi1 hik ρi h1 h2 h3 h4 e he1 he2 h
    rcases Nat.lt_or_ge i l with hli | hli
    · have h5 := hA' (i + 1) l (by omega) (by omega) hlk
      linarith
    · have h5 := hA l i hl1 hli (by omega)
      linarith
  · intro i hi1 hik e he1 he2
    constructor
    · intro h
      rcases Nat.lt_or_ge i l with hli | hli
      · have h5 := hA' (i + 1) l (by omega) (by omega) hlk
        have h6 := (hgap i hi1 (by omega)).2.2.2
        linarith
      · have h5 := hA l i hl1 hli hik
        linarith
    · intro h
      rcases Nat.lt_or_ge l i with hli | hli
      · have h5 := hA l (i - 1) hl1 (by omega) (by omega)
        have h6 := (hgap (i - 1) (by omega) (by omega)).2.2.2
        rw [Nat.sub_add_cancel (by omega : 1 ≤ i)] at h6
        linarith
      · have h5 := hA' i l hi1 hli hlk
        linarith

variable (P : M.Par)

/- English proof (translation)
Take `⟨_, _, _, _, _, hg⟩` from `hOK`. Establish `hgi` using `hg i (by simp; omega)`. Unfold `M.Par.lo M.Par.hi at hgi`. Establish `h3` using `le_max_left (P.u (i + 1)) (P.u' (i + 1))`. Establish `h4` using `le_max_right (P.u (i + 1)) (P.u' (i + 1))`.

Establish `h5` using `min_le_left (P.u i) (P.u' i)`. Establish `h6` using `min_le_right (P.u i) (P.u' i)`. Conclude with `⟨by linarith, by linarith, by linarith, by linarith⟩`.
-/
theorem gap4 (hOK : P.OK) (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ P.k - 1) :
    P.u (i + 1) ≤ P.u i - 1 ∧ P.u' (i + 1) ≤ P.u' i - 1 ∧ P.u (i + 1) ≤ P.u' i - 1 ∧
      P.u' (i + 1) ≤ P.u i - 1 := by
  obtain ⟨_, _, _, _, _, hg⟩ := hOK
  have hgi := hg i (by simp; omega)
  unfold M.Par.lo M.Par.hi at hgi
  have h3 := le_max_left (P.u (i + 1)) (P.u' (i + 1))
  have h4 := le_max_right (P.u (i + 1)) (P.u' (i + 1))
  have h5 := min_le_left (P.u i) (P.u' i)
  have h6 := min_le_right (P.u i) (P.u' i)
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/- English proof (translation)
Take `⟨_, _, _, _, _, hg⟩` from `hOK`. Establish `hgi` using `hg i (by simp; omega)`. Establish `hw` using `(ρ ⟨i - 1, by omega⟩).isLt`. Establish `he : i - 1 + 1 = i` using `by omega`. Simplify using `only [M.Par.wid, Fin.val_mk, he] at hw`.

Establish `hfl : ((⌊P.hi i - P.lo i⌋₊ : ℕ) : ℝ) ≤ P.hi i - P.lo i` using `Nat.floor_le (by linarith)`. Establish `hv' : ((ρ ⟨i - 1, by omega⟩ : ℕ)) ≤ ⌊P.hi i - P.lo i⌋₊` using `by first`. Consider the case `exact Nat.lt_succ_iff.mp hw`. Consider the case `omega`. Establish `hv : ((ρ ⟨i - 1, by omega⟩ : ℕ) : ℝ) ≤ ((⌊P.hi i - P.lo i⌋₊ : ℕ) : ℝ)` using `by exact_mod_cast hv'`.

Establish `h0 : (0 : ℝ) ≤ ((ρ ⟨i - 1, by omega⟩ : ℕ) : ℝ)` using `Nat.cast_nonneg _`. Unfold `M.rho`. Rewrite using `[dif_pos ⟨hi1, hi2⟩]`. Prove the components needed by the constructor for the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem rho_bounds (hOK : P.OK) (ρ : M.Ty P) (i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ P.k - 1) :
    P.lo i ≤ M.rho P ρ i ∧ M.rho P ρ i ≤ P.hi i := by
  obtain ⟨_, _, _, _, _, hg⟩ := hOK
  have hgi := hg i (by simp; omega)
  have hw := (ρ ⟨i - 1, by omega⟩).isLt
  have he : i - 1 + 1 = i := by omega
  simp only [M.Par.wid, Fin.val_mk, he] at hw
  have hfl : ((⌊P.hi i - P.lo i⌋₊ : ℕ) : ℝ) ≤ P.hi i - P.lo i := Nat.floor_le (by linarith)
  have hv' : ((ρ ⟨i - 1, by omega⟩ : ℕ)) ≤ ⌊P.hi i - P.lo i⌋₊ := by
    first
      | exact Nat.lt_succ_iff.mp hw
      | omega
  have hv : ((ρ ⟨i - 1, by omega⟩ : ℕ) : ℝ) ≤ ((⌊P.hi i - P.lo i⌋₊ : ℕ) : ℝ) := by exact_mod_cast hv'
  have h0 : (0 : ℝ) ≤ ((ρ ⟨i - 1, by omega⟩ : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold M.rho
  rw [dif_pos ⟨hi1, hi2⟩]
  constructor
  · linarith
  · linarith

/- English proof (translation)
Unfold `M.xC`. Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_Icc]`. Establish `hb` using `rho_bounds P hOK ρ i hi.1 hi.2`.

Establish `hg4` using `gap4 P hOK`. Unfold `M.Par.lo M.Par.hi at hb`. Establish `a1` using `le_max_left (P.u (i + 1)) (P.u' (i + 1))`. Establish `a2` using `le_max_right (P.u (i + 1)) (P.u' (i + 1))`. Establish `a3` using `min_le_left (P.u i) (P.u' i)`.

Establish `a4` using `min_le_right (P.u i) (P.u' i)`. Establish `key : y + e + M.rho P ρ i ≠ 0`. Unfold `I.OnCut at hy`. Break down `hy with hy | hy` into its components or cases. Conclude with `(cut_facts P.u P.u' P.k l hl1 hlk hg4 y hy).1 i hi.1 hi.2 _ (by linarith) (by linarith) (by linarith) (by linarith) e he1 he2`.

Conclude with `(cut_facts P.u' P.u P.k l hl1 hlk (fun j hj1 hj2 => ⟨(hg4 j hj1 hj2).2.1, (hg4 j hj1 hj2).1, (hg4 j hj1 hj2).2.2.2, (hg4 j hj1 hj2).2.2.1⟩) y hy).1 i hi.1 hi.2 _ (by linarith) (by linarith) (by linarith) (by linarith) e he1 he2`. Introduce `h0`. Apply `key` to reduce the goal to its premises. Conclude with `h0` after adjusting the coercions.
-/
theorem xC_ne (hOK : P.OK) (l : ℕ) (hl1 : 1 ≤ l) (hlk : l ≤ P.k) (y : ℝ) (hy : I.OnCut P.u P.u' l y)
    (e : ℝ) (he1 : -1 ≤ e) (he2 : e ≤ 1) (ρ : M.Ty P) : M.xC P ρ ((y + e : ℝ) : ℂ) ≠ 0 := by
  unfold M.xC
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  rw [Finset.mem_Icc] at hi
  have hb := rho_bounds P hOK ρ i hi.1 hi.2
  have hg4 := gap4 P hOK
  unfold M.Par.lo M.Par.hi at hb
  have a1 := le_max_left (P.u (i + 1)) (P.u' (i + 1))
  have a2 := le_max_right (P.u (i + 1)) (P.u' (i + 1))
  have a3 := min_le_left (P.u i) (P.u' i)
  have a4 := min_le_right (P.u i) (P.u' i)
  have key : y + e + M.rho P ρ i ≠ 0 := by
    unfold I.OnCut at hy
    rcases hy with hy | hy
    · exact (cut_facts P.u P.u' P.k l hl1 hlk hg4 y hy).1 i hi.1 hi.2 _
        (by linarith) (by linarith) (by linarith) (by linarith) e he1 he2
    · exact (cut_facts P.u' P.u P.k l hl1 hlk
        (fun j hj1 hj2 => ⟨(hg4 j hj1 hj2).2.1, (hg4 j hj1 hj2).1, (hg4 j hj1 hj2).2.2.2, (hg4 j hj1 hj2).2.2.1⟩)
        y hy).1 i hi.1 hi.2 _ (by linarith) (by linarith) (by linarith) (by linarith) e he1 he2
  intro h0
  apply key
  exact_mod_cast h0

/- English proof (translation)
Establish `hg4` using `gap4 P hOK`. Take `⟨_, hT, hT', _, _, _⟩` from `hOK`. Unfold `M.qC`. Use `mul_ne_zero ?_ ?_` and prove the remaining obligations. Establish `h1 : (P.T : ℂ) ≠ 0` using `by exact_mod_cast hT.ne'`.

Establish `h2 : (P.T' : ℂ) ≠ 0` using `by exact_mod_cast hT'.ne'`. Conclude with `neg_ne_zero.mpr (mul_ne_zero h1 h2)`. Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_Icc]`.

Establish `key : y + e + 1 / 2 + P.u i ≠ 0 ∧ y + e + 1 / 2 + P.u' i ≠ 0`. Unfold `I.OnCut at hy`. Break down `hy with hy | hy` into its components or cases. Conclude with `(cut_facts P.u P.u' P.k l hl1 hlk hg4 y hy).2 i hi.1 hi.2 e he1 he2`. Establish `h3` using `(cut_facts P.u' P.u P.k l hl1 hlk (fun j hj1 hj2 => ⟨(hg4 j hj1 hj2).2.1, (hg4 j hj1 hj2).1, (hg4 j hj1 hj2).2.2.2, (hg4 j hj1 hj2).2.2.1⟩) y hy).2 i hi.1 hi.2 e he1 he2`.

Conclude with `⟨h3.2, h3.1⟩`. Use `mul_ne_zero ?_ ?_` and prove the remaining obligations. Introduce `h0`. Apply `key.1` to reduce the goal to its premises. Use `first`.

Consider the case `exact_mod_cast h0`. Consider the case `(have h1 := congrArg Complex.re h0`. Simplify using `at h1`. Use the proof step `linarith)`. Introduce `h0`.

Apply `key.2` to reduce the goal to its premises. Use `first`. Consider the case `exact_mod_cast h0`. Consider the case `(have h1 := congrArg Complex.re h0`. Simplify using `at h1`.

Use the proof step `linarith)`.
-/
theorem qC_ne (hOK : P.OK) (l : ℕ) (hl1 : 1 ≤ l) (hlk : l ≤ P.k) (y : ℝ) (hy : I.OnCut P.u P.u' l y)
    (e : ℝ) (he1 : -1 ≤ e) (he2 : e ≤ 0) : M.qC P ((y + e : ℝ) : ℂ) ≠ 0 := by
  have hg4 := gap4 P hOK
  obtain ⟨_, hT, hT', _, _, _⟩ := hOK
  unfold M.qC
  refine mul_ne_zero ?_ ?_
  · have h1 : (P.T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
    have h2 : (P.T' : ℂ) ≠ 0 := by exact_mod_cast hT'.ne'
    exact neg_ne_zero.mpr (mul_ne_zero h1 h2)
  · rw [Finset.prod_ne_zero_iff]
    intro i hi
    rw [Finset.mem_Icc] at hi
    have key : y + e + 1 / 2 + P.u i ≠ 0 ∧ y + e + 1 / 2 + P.u' i ≠ 0 := by
      unfold I.OnCut at hy
      rcases hy with hy | hy
      · exact (cut_facts P.u P.u' P.k l hl1 hlk hg4 y hy).2 i hi.1 hi.2 e he1 he2
      · have h3 := (cut_facts P.u' P.u P.k l hl1 hlk
          (fun j hj1 hj2 => ⟨(hg4 j hj1 hj2).2.1, (hg4 j hj1 hj2).1, (hg4 j hj1 hj2).2.2.2, (hg4 j hj1 hj2).2.2.1⟩)
          y hy).2 i hi.1 hi.2 e he1 he2
        exact ⟨h3.2, h3.1⟩
    refine mul_ne_zero ?_ ?_
    · intro h0
      apply key.1
      first
        | exact_mod_cast h0
        | (have h1 := congrArg Complex.re h0
           simp at h1
           linarith)
    · intro h0
      apply key.2
      first
        | exact_mod_cast h0
        | (have h1 := congrArg Complex.re h0
           simp at h1
           linarith)

end cut

/- English proof (translation)
Establish `hmem : ∀ x ∈ Formalism.FourierDecayAlt.D.positionted w, ∃ a : Fin w.length, x = (⟨(w.get a).1, a, ((w.get a).2 : ℂ)⟩ : Formalism.FourierDecayAlt.Wd.Letter ℂ (Fin w.length))`. Introduce `x hx`. Unfold `Formalism.FourierDecayAlt.D.positionted at hx`. Take `⟨a, rfl⟩` from `List.mem_ofFn.1 hx`. Conclude with `⟨a, rfl⟩`.

Use `⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Unfold `Formalism.FourierDecayAlt.D.positionted`. Rewrite using `[List.map_ofFn]`. Conclude with `List.nodup_ofFn.2 (fun a b h => h)`. Introduce `x hx`.

Take `⟨a, rfl⟩` from `hmem x hx`. Simplify using the standard rewrite rules. Introduce `x hx`. Take `⟨a, rfl⟩` from `hmem x hx`. Establish `hc` using `hcut a`.

Establish `hx : ∀ e : ℝ, -1 ≤ e → e ≤ 1 → ∀ ρ, M.xC P ρ (((w.get a).2 + e : ℝ) : ℂ) ≠ 0` using `fun e h1 h2 ρ => xC_ne P hOK l0 hl1 hlk _ hc e h1 h2 ρ`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hinv]; intro ρ; simpa using hx 0 (by norm_num) (by norm_num) ρ`. Rewrite using `[hinv]; intro ρ; simpa using hx 1 (by norm_num) (by norm_num) ρ`. Rewrite using `[hinv]; intro ρ; simpa [sub_eq_add_neg] using hx (-1) (by norm_num) (by norm_num) ρ`.

Rewrite using `[hq]; simpa using qC_ne P hOK l0 hl1 hlk _ hc 0 (by norm_num) (by norm_num)`. Rewrite using `[hq]; simpa [sub_eq_add_neg] using qC_ne P hOK l0 hl1 hlk _ hc (-1) (by norm_num) (by norm_num)`. Unfold `Formalism.FourierDecayAlt.D.positionted`. Rewrite using `[List.pairwise_ofFn]`. Introduce `a b hab n hn h`.

Establish `h' : ((w.get a).2 : ℂ) - ((w.get b).2 : ℂ) = (n : ℂ)` using `h`. Establish `h1 : (w.get a).2 - (w.get b).2 = (n : ℝ)` using `by exact_mod_cast h'`. Establish `h2 : |(n : ℝ)| ≤ 2` using `by exact_mod_cast hn`. Use `hsep a b (ne_of_lt hab)` as an intermediate fact. Rewrite `this` using `[h1]`.

Combine the linear equalities and inequalities to obtain the conclusion. Introduce `x hx`. Take `⟨a, rfl⟩` from `hmem x hx`. Conclude with `⟨by simp, by simpa using hcut a⟩`. Unfold `Formalism.FourierDecayAlt.D.positionted`.

Rewrite using `[List.pairwise_ofFn]`. Introduce `a b hab`. Simplify using `using hsep a b (ne_of_lt hab)`.
-/
theorem wordOK_of {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (st : Formalism.FourierDecayAlt.Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (hOK : P.OK) (hl1 : 1 ≤ l0) (hlk : l0 ≤ P.k) (hq : st.q = M.qC P)
    (hinv : st.inv = {Y | ∀ ρ : M.Ty P, M.xC P ρ Y ≠ 0}) (w : List Formalism.FourierDecayAlt.C.Letter)
    (hcut : ∀ a : Fin w.length, I.OnCut P.u P.u' l0 (w.get a).2)
    (hsep : ∀ a b : Fin w.length, a ≠ b → 2 < |(w.get a).2 - (w.get b).2|) :
    Formalism.FourierDecayAlt.P5.WordOK P z z' π π' st l0 (Formalism.FourierDecayAlt.D.positionted w) := by
  have hmem : ∀ x ∈ Formalism.FourierDecayAlt.D.positionted w, ∃ a : Fin w.length,
      x = (⟨(w.get a).1, a, ((w.get a).2 : ℂ)⟩ : Formalism.FourierDecayAlt.Wd.Letter ℂ (Fin w.length)) := by
    intro x hx
    unfold Formalism.FourierDecayAlt.D.positionted at hx
    obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hx
    exact ⟨a, rfl⟩
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · unfold Formalism.FourierDecayAlt.D.positionted
    rw [List.map_ofFn]
    exact List.nodup_ofFn.2 (fun a b h => h)
  · intro x hx
    obtain ⟨a, rfl⟩ := hmem x hx
    simp
  · intro x hx
    obtain ⟨a, rfl⟩ := hmem x hx
    have hc := hcut a
    have hx : ∀ e : ℝ, -1 ≤ e → e ≤ 1 → ∀ ρ, M.xC P ρ (((w.get a).2 + e : ℝ) : ℂ) ≠ 0 :=
      fun e h1 h2 ρ => xC_ne P hOK l0 hl1 hlk _ hc e h1 h2 ρ
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hinv]; intro ρ; simpa using hx 0 (by norm_num) (by norm_num) ρ
    · rw [hinv]; intro ρ; simpa using hx 1 (by norm_num) (by norm_num) ρ
    · rw [hinv]; intro ρ; simpa [sub_eq_add_neg] using hx (-1) (by norm_num) (by norm_num) ρ
    · rw [hq]; simpa using qC_ne P hOK l0 hl1 hlk _ hc 0 (by norm_num) (by norm_num)
    · rw [hq]; simpa [sub_eq_add_neg] using qC_ne P hOK l0 hl1 hlk _ hc (-1) (by norm_num) (by norm_num)
  · unfold Formalism.FourierDecayAlt.D.positionted
    rw [List.pairwise_ofFn]
    intro a b hab n hn h
    have h' : ((w.get a).2 : ℂ) - ((w.get b).2 : ℂ) = (n : ℂ) := h
    have h1 : (w.get a).2 - (w.get b).2 = (n : ℝ) := by exact_mod_cast h'
    have h2 : |(n : ℝ)| ≤ 2 := by exact_mod_cast hn
    have := hsep a b (ne_of_lt hab)
    rw [h1] at this
    linarith
  · intro x hx
    obtain ⟨a, rfl⟩ := hmem x hx
    exact ⟨by simp, by simpa using hcut a⟩
  · unfold Formalism.FourierDecayAlt.D.positionted
    rw [List.pairwise_ofFn]
    intro a b hab
    simpa using hsep a b (ne_of_lt hab)

/- English proof (translation)
Use `⟨0, ?_⟩` and prove the remaining obligations. Introduce `E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hP`. Take `⟨_, _, _, hB, hl1, hlk, hG, _, _, _, _, _, hOn⟩` from `hP`. Introduce `v j`. Establish `hPl0` using `(hB.2 v).2.2.2.1`.

Establish `hPl` using `isPlace_lev (Formalism.FourierDecayAlt.D.parOf S v) (T v) j hPl0`. Take `⟨X⟩` from `Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl`. Take `⟨L, st, h1, h2, h3, h4, h5, h6⟩` from `Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl X (S.l + 1)`. Take `⟨μ0, hμ0⟩` from `exists_haar_level_zero (Nat.sub_self S.G.r) ((T v).bs S.G.r)`. Use `⟨X, μ0.map (embL S.G.k (S.G.r - j)), L, st, ⟨hPl, haar_glev μ0 hμ0, h1, h2, h3, h4, h5, h6⟩, ?_⟩` and prove the remaining obligations.

Introduce `w hw`. Take `⟨W, rfl⟩` from `hw`. Take `⟨-, -, -, -, -, h6G⟩` from `hG v`. Use `wordOK_of _ _ _ _ _ st (S.l + 1) hPl.1 (by omega) (by change S.l + 1 ≤ S.G.k; omega) h3 h4 (W.1 v) (fun a => ?_) (fun a b hab => ?_)` and prove the remaining obligations. Establish `hn` using `W.2.1.1 v a.val a.isLt`.

Establish `hin : ∀ y, y ∈ S.grid v ((W.1 v).length - a.val) ∪ S.grid1 v → y ∈ (S.G.place (S.pl v)).cutI S.l ∧ y + 1 ∈ (S.G.place (S.pl v)).cutI S.l`. Introduce `y hy`. Break down `Finset.mem_union.1 hy with h | h` into its components or cases. Conclude with `⟨(h6G y (Or.inl ⟨_, h⟩)).1, (h6G y (Or.inl ⟨_, h⟩)).2.1⟩`. Conclude with `⟨(h6G y (Or.inr h)).1, (h6G y (Or.inr h)).2.1⟩`.

Establish `hpt : ((W.1 v).get a).2 ∈ (S.G.place (S.pl v)).cutI S.l`. Rewrite using `[List.get_eq_getElem]`. Distinguish the cases in `hp : ((W.1 v)[a.val]'a.isLt).1 = true`. Rewrite `hn` using `[if_pos hp]`. Conclude with `(hin _ hn).1`.

Rewrite `hn` using `[if_neg hp]`. Use `(hin _ hn).2` as an intermediate fact. Simplify using `using this`. Apply `hOn v` to reduce the goal to its premises. Simplify using `only [Formalism.FourierDecayAlt.Sz.Cfg.cutI, Set.mem_ofPred_eq] at hpt`.

Simplify using `only [Formalism.FourierDecayAlt.C.HidaSetting.cutLo, Formalism.FourierDecayAlt.C.HidaSetting.cutHi, Set.mem_Icc]`. Apply the tactic sequence `constructor <;> linarith [hpt.1, hpt.2]`. Use `W.2.1.2 v a.val b.val a.isLt b.isLt (fun h => hab (Fin.ext h)) 0 (by norm_num) (by norm_num)` as an intermediate fact. Simplify `this` using `[List.get_eq_getElem]`.
-/
theorem levelsActualBuilt : Formalism.FourierDecayAlt.JCT.LevelsActualBuilt := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hP
  obtain ⟨_, _, _, hB, hl1, hlk, hG, _, _, _, _, _, hOn⟩ := hP
  intro v j
  have hPl0 := (hB.2 v).2.2.2.1
  have hPl := isPlace_lev (Formalism.FourierDecayAlt.D.parOf S v) (T v) j hPl0
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl
  obtain ⟨L, st, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl X (S.l + 1)
  obtain ⟨μ0, hμ0⟩ := exists_haar_level_zero (Nat.sub_self S.G.r) ((T v).bs S.G.r)
  refine ⟨X, μ0.map (embL S.G.k (S.G.r - j)), L, st, ⟨hPl, haar_glev μ0 hμ0, h1, h2, h3, h4, h5, h6⟩, ?_⟩
  intro w hw
  obtain ⟨W, rfl⟩ := hw
  obtain ⟨-, -, -, -, -, h6G⟩ := hG v
  refine wordOK_of _ _ _ _ _ st (S.l + 1) hPl.1 (by omega) (by change S.l + 1 ≤ S.G.k; omega) h3 h4 (W.1 v) (fun a => ?_) (fun a b hab => ?_)
  · have hn := W.2.1.1 v a.val a.isLt
    have hin : ∀ y, y ∈ S.grid v ((W.1 v).length - a.val) ∪ S.grid1 v →
        y ∈ (S.G.place (S.pl v)).cutI S.l ∧ y + 1 ∈ (S.G.place (S.pl v)).cutI S.l := by
      intro y hy
      rcases Finset.mem_union.1 hy with h | h
      · exact ⟨(h6G y (Or.inl ⟨_, h⟩)).1, (h6G y (Or.inl ⟨_, h⟩)).2.1⟩
      · exact ⟨(h6G y (Or.inr h)).1, (h6G y (Or.inr h)).2.1⟩
    have hpt : ((W.1 v).get a).2 ∈ (S.G.place (S.pl v)).cutI S.l := by
      rw [List.get_eq_getElem]
      by_cases hp : ((W.1 v)[a.val]'a.isLt).1 = true
      · rw [if_pos hp] at hn
        exact (hin _ hn).1
      · rw [if_neg hp] at hn
        have := (hin _ hn).2
        simpa using this
    apply hOn v
    simp only [Formalism.FourierDecayAlt.Sz.Cfg.cutI, Set.mem_ofPred_eq] at hpt
    simp only [Formalism.FourierDecayAlt.C.HidaSetting.cutLo, Formalism.FourierDecayAlt.C.HidaSetting.cutHi, Set.mem_Icc]
    constructor <;> linarith [hpt.1, hpt.2]
  · have := W.2.1.2 v a.val b.val a.isLt b.isLt (fun h => hab (Fin.ext h)) 0 (by norm_num) (by norm_num)
    simpa [List.get_eq_getElem] using this

end Formalism.FourierDecayAlt.P.JCTx5

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
Conclude with `Formalism.FourierDecayAlt.P.JCTx5.levelsActualBuilt`.
-/
theorem levels_of_built_setting : Formalism.FourierDecayAlt.JCT.LevelsActualBuilt := by
  exact Formalism.FourierDecayAlt.P.JCTx5.levelsActualBuilt

end Formalism.FourierDecayAlt.P
