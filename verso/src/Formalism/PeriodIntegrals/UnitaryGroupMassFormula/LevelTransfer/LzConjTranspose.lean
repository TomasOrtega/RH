import Mathlib
import Formalism.HermitianCurvature.StatementQ
import Formalism.FormalDegreeBessel.FinalG
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelTransfer.ExpLz

open Matrix

noncomputable section

namespace PIQnLT

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k i r' : ℕ}

/- English proof (translation)
Use `j.isLt` as an intermediate fact. Simplify using `only [levPos]`. Use linear arithmetic over natural numbers and integers.
-/
theorem lev_in (j : Fin (2 * r' + k + 1)) :
    i ≤ (levPos k i r' j).val ∧ (levPos k i r' j).val < 2 * r' + k + 1 + i := by
  have := j.isLt
  simp only [levPos]
  omega

/- English proof (translation)
Distinguish the cases in `h : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i`. Use `left`. Conclude with `⟨⟨p.val - i, by omega⟩, Fin.ext (by simp [levPos]; omega)⟩`. Use `right`. Conclude with `h`.
-/
theorem cases_lev (p : Fin (2 * (i + r') + k + 1)) :
    (∃ p', p = levPos k i r' p') ∨ ¬ (i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i) := by
  by_cases h : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i
  · left
    exact ⟨⟨p.val - i, by omega⟩, Fin.ext (by simp [levPos]; omega)⟩
  · right
    exact h

/- English proof (translation)
Use extensionality with `p q`. Simplify using `only [Lz, Matrix.sub_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem Lz_sub (X Y : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    Lz k i r' (X - Y) = Lz k i r' X - Lz k i r' Y := by
  ext p q
  simp only [Lz, Matrix.sub_apply]
  split_ifs <;> simp

/- English proof (translation)
Use extensionality with `p q`. Simplify using `only [Lz, Matrix.add_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem Lz_add (X Y : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    Lz k i r' (X + Y) = Lz k i r' X + Lz k i r' Y := by
  ext p q
  simp only [Lz, Matrix.add_apply]
  split_ifs <;> simp

/- English proof (translation)
Use extensionality with `p q`. Simplify using `only [Lz, Matrix.smul_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem Lz_smul (c : ℂ) (X : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    Lz k i r' (c • X) = c • Lz k i r' X := by
  ext p q
  simp only [Lz, Matrix.smul_apply]
  split_ifs <;> simp

/- English proof (translation)
Use extensionality with `p q`. Rewrite using `[Matrix.mul_apply, sum_lev (fun s => Hpk k (i + r') p s * Lz k i r' W s q) (fun s hs => by simp only [Lz_out_left W s q hs, mul_zero])]`. Break down `cases_lev p with ⟨p', rfl⟩ | hp` into its components or cases. Break down `cases_lev q with ⟨q', rfl⟩ | hq` into its components or cases. Simplify using `only [hpk_lev, Lz_lev, Matrix.mul_apply]`.

Simplify using `only [Lz_out_right _ _ _ hq, mul_zero, Finset.sum_const_zero]`. Simplify using `only [hpk_out_in p _ hp (lev_in _), zero_mul, Finset.sum_const_zero, Lz_out_left _ _ _ hp]`.
-/
theorem hpk_mul_Lz (W : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    Hpk k (i + r') * Lz k i r' W = Lz k i r' (Hpk k r' * W) := by
  ext p q
  rw [Matrix.mul_apply, sum_lev (fun s => Hpk k (i + r') p s * Lz k i r' W s q)
    (fun s hs => by simp only [Lz_out_left W s q hs, mul_zero])]
  rcases cases_lev p with ⟨p', rfl⟩ | hp
  · rcases cases_lev q with ⟨q', rfl⟩ | hq
    · simp only [hpk_lev, Lz_lev, Matrix.mul_apply]
    · simp only [Lz_out_right _ _ _ hq, mul_zero, Finset.sum_const_zero]
  · simp only [hpk_out_in p _ hp (lev_in _), zero_mul, Finset.sum_const_zero, Lz_out_left _ _ _ hp]

/- English proof (translation)
Use extensionality with `p q`. Rewrite using `[Matrix.mul_apply, sum_lev (fun s => Lz k i r' W p s * Hpk k (i + r') s q) (fun s hs => by simp only [Lz_out_right W p s hs, zero_mul])]`. Break down `cases_lev q with ⟨q', rfl⟩ | hq` into its components or cases. Break down `cases_lev p with ⟨p', rfl⟩ | hp` into its components or cases. Simplify using `only [hpk_lev, Lz_lev, Matrix.mul_apply]`.

Simplify using `only [Lz_out_left _ _ _ hp, zero_mul, Finset.sum_const_zero]`. Simplify using `only [hpk_in_out _ q (lev_in _) hq, mul_zero, Finset.sum_const_zero, Lz_out_right _ _ _ hq]`.
-/
theorem Lz_mul_hpk (W : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    Lz k i r' W * Hpk k (i + r') = Lz k i r' (W * Hpk k r') := by
  ext p q
  rw [Matrix.mul_apply, sum_lev (fun s => Lz k i r' W p s * Hpk k (i + r') s q)
    (fun s hs => by simp only [Lz_out_right W p s hs, zero_mul])]
  rcases cases_lev q with ⟨q', rfl⟩ | hq
  · rcases cases_lev p with ⟨p', rfl⟩ | hp
    · simp only [hpk_lev, Lz_lev, Matrix.mul_apply]
    · simp only [Lz_out_left _ _ _ hp, zero_mul, Finset.sum_const_zero]
  · simp only [hpk_in_out _ q (lev_in _) hq, mul_zero, Finset.sum_const_zero, Lz_out_right _ _ _ hq]

/- English proof (translation)
Use extensionality with `p q`. Simplify using `only [Matrix.conjTranspose_apply, Lz]`. Apply the tactic sequence `split_ifs <;> simp_all`.
-/
theorem Lz_conjTranspose (W : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    (Lz k i r' W)ᴴ = Lz k i r' Wᴴ := by
  ext p q
  simp only [Matrix.conjTranspose_apply, Lz]
  split_ifs <;> simp_all

/- English proof (translation)
Use extensionality with `p q`. Establish `ha` using `a.isLt`. Establish `hb` using `b.isLt`. Simplify using `only [Lz, Matrix.single_apply, levPos, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
theorem single_lev (a b : Fin (2 * r' + k + 1)) :
    Matrix.single (levPos k i r' a) (levPos k i r' b) (1 : ℂ) = Lz k i r' (Matrix.single a b 1) := by
  ext p q
  have ha := a.isLt
  have hb := b.isLt
  simp only [Lz, Matrix.single_apply, levPos, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
The claim follows from `Matrix.inv_eq_left_inv (Formalism.QuantumDeterminants.GBasic.Hpk_sq k r)`.
-/
theorem hpk_inv (k r : ℕ) : (Hpk k r)⁻¹ = Hpk k r :=
  Matrix.inv_eq_left_inv (Formalism.QuantumDeterminants.GBasic.Hpk_sq k r)

/- English proof (translation)
Unfold `hpart1`. Rewrite using `[hpk_inv, hpk_inv, single_lev, Lz_conjTranspose, hpk_mul_Lz, Lz_mul_hpk, Lz_smul, Lz_sub]`.
-/
theorem hpart1_lev (a b : Fin (2 * r' + k + 1)) :
    hpart1 (Hpk k (i + r')) (Matrix.single (levPos k i r' a) (levPos k i r' b) 1) =
      Lz k i r' (hpart1 (Hpk k r') (Matrix.single a b 1)) := by
  unfold hpart1
  rw [hpk_inv, hpk_inv, single_lev, Lz_conjTranspose, hpk_mul_Lz, Lz_mul_hpk, Lz_smul, Lz_sub]

/- English proof (translation)
Unfold `hpart2`. Rewrite using `[hpk_inv, hpk_inv, single_lev, Lz_conjTranspose, hpk_mul_Lz, Lz_mul_hpk, Lz_smul, Lz_add]`.
-/
theorem hpart2_lev (a b : Fin (2 * r' + k + 1)) :
    hpart2 (Hpk k (i + r')) (Matrix.single (levPos k i r' a) (levPos k i r' b) 1) =
      Lz k i r' (hpart2 (Hpk k r') (Matrix.single a b 1)) := by
  unfold hpart2
  rw [hpk_inv, hpk_inv, single_lev, Lz_conjTranspose, hpk_mul_Lz, Lz_mul_hpk, Lz_smul, Lz_add]

section Transport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (hL : LevHom)
include hL

/- English proof (translation)
Unfold `RdV`. Use `congr 1`. Use function extensionality and compare the values at `t`. Rewrite using `[← Lz_smul, exp_Lz hL, ← (hL k i r').2]`.
-/
theorem RdV_Lz (X : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ)
    (F : Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ → E)
    (x : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    RdV (Lz k i r' X) F (ιLev k i r' x) = RdV X (fun y => F (ιLev k i r' y)) x := by
  unfold RdV
  congr 1
  funext t
  rw [← Lz_smul, exp_Lz hL, ← (hL k i r').2]

/- English proof (translation)
Simplify using `only [EabH]`. Rewrite using `[hpart1_lev, hpart2_lev, RdV_Lz hL, RdV_Lz hL]`.
-/
theorem EabH_lev (a b : Fin (2 * r' + k + 1))
    (F : Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ → E)
    (x : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    EabH (Hpk k (i + r')) (levPos k i r' a) (levPos k i r' b) F (ιLev k i r' x) =
      EabH (Hpk k r') a b (fun y => F (ιLev k i r' y)) x := by
  simp only [EabH]
  rw [hpart1_lev, hpart2_lev, RdV_Lz hL, RdV_Lz hL]

/- English proof (translation)
Simplify using `only [Formalism.QuantumDeterminants.Top, Formalism.FourierDecayAlt.Q.EH]`. Rewrite using `[EabH_lev hL]`. Simplify using `only [lev_inj.eq_iff]`.
-/
theorem Top_lev (u : ℂ) (a b : Fin (2 * r' + k + 1))
    (F : Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ → E)
    (x : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    Formalism.QuantumDeterminants.Top (Formalism.FourierDecayAlt.Q.EH k (i + r')) u (levPos k i r' a) (levPos k i r' b) F (ιLev k i r' x) =
      Formalism.QuantumDeterminants.Top (Formalism.FourierDecayAlt.Q.EH k r') u a b (fun y => F (ιLev k i r' y)) x := by
  simp only [Formalism.QuantumDeterminants.Top, Formalism.FourierDecayAlt.Q.EH]
  rw [EabH_lev hL]
  simp only [lev_inj.eq_iff]

omit hL in
/- English proof (translation)
Proceed by induction on `t generalizing F with`. Consider the case `zero => simp`. Consider the case `succ t ih`. Rewrite using `[List.ofFn_succ, List.ofFn_succ, List.foldr_cons, List.foldr_cons, h]`. Conclude with `congrArg _ (ih (fun j => Tb j.succ) (fun j => Ts j.succ) (fun j G => h j.succ G) F)`.
-/
theorem foldr_ofFn {α β : Type*} {t : ℕ} (R : α → β) (Tb : Fin t → α → α) (Ts : Fin t → β → β)
    (h : ∀ j G, R (Tb j G) = Ts j (R G)) (F : α) :
    R ((List.ofFn Tb).foldr (fun T h => T h) F) = (List.ofFn Ts).foldr (fun T h => T h) (R F) := by
  induction t generalizing F with
  | zero => simp
  | succ t ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.foldr_cons, List.foldr_cons, h]
    exact congrArg _ (ih (fun j => Tb j.succ) (fun j => Ts j.succ) (fun j G => h j.succ G) F)

/- English proof (translation)
Unfold `qminorOp`. Simplify using `only [Finset.sum_apply, Pi.smul_apply]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Use `congr 1`. Use `foldr_ofFn (fun (G : Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ → E) y => G (ιLev k i r' y)) (fun j : Fin t => Formalism.QuantumDeterminants.Top (Formalism.FourierDecayAlt.Q.EH k (i + r')) (u - ((j : ℕ) : ℂ)) (levPos k i r' (a (σ j))) (levPos k i r' (b j)) …` as an intermediate fact.

Conclude with `congrFun this x`.
-/
theorem qminorOp_lev {t : ℕ} (a b : Fin t → Fin (2 * r' + k + 1)) (u : ℂ)
    (F : Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ → E)
    (x : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    qminorOp (Formalism.FourierDecayAlt.Q.EH k (i + r')) (levPos k i r' ∘ a) (levPos k i r' ∘ b) u F (ιLev k i r' x) =
      qminorOp (Formalism.FourierDecayAlt.Q.EH k r') a b u (fun y => F (ιLev k i r' y)) x := by
  unfold qminorOp
  simp only [Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  have := foldr_ofFn (fun (G : Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ → E) y =>
      G (ιLev k i r' y))
    (fun j : Fin t => Formalism.QuantumDeterminants.Top (Formalism.FourierDecayAlt.Q.EH k (i + r')) (u - ((j : ℕ) : ℂ)) (levPos k i r' (a (σ j))) (levPos k i r' (b j)))
    (fun j : Fin t => Formalism.QuantumDeterminants.Top (Formalism.FourierDecayAlt.Q.EH k r') (u - ((j : ℕ) : ℂ)) (a (σ j)) (b j))
    (fun j G => funext fun y => Top_lev hL _ _ _ G y) F
  exact congrFun this x

end Transport

end PIQnLT
