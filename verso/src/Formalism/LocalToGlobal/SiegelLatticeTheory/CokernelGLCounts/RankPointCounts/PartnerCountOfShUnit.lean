import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountOfModUnits

noncomputable section

namespace Formalism.L2.SG.Pf.PCount

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc

section Mono

variable {K : Type*} [CommRing K]

/- English proof (translation)
Set `P : Matrix (Fin m) (Fin m) K` to `Matrix.of fun a b => if b = σ a then 1 else 0`. Establish `hAP : A = Matrix.diagonal v * P`. Use extensionality with `a b`. Rewrite using `[hA, Matrix.diagonal_mul]`. Simplify using `[P]`.

Establish `hPP : P * P = 1`. Use extensionality with `a c`. Simplify using `only [P, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul]`. Rewrite using `[Finset.sum_eq_single (σ a)]`. Simplify using `only [if_true, hσ]`.

Distinguish the cases in `h : c = a`. Rewrite using `[if_pos h, if_pos h.symm]`. Rewrite using `[if_neg h, if_neg (fun h' => h h'.symm)]`. Introduce `b _ hb`. Rewrite using `[if_neg hb]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Establish `hP : IsUnit P.det` using `isUnit_iff_exists_inv.2 ⟨P.det, by rw [← Matrix.det_mul, hPP, Matrix.det_one]⟩`. Rewrite using `[hAP, Matrix.det_mul, Matrix.det_diagonal]`. Establish `hprod : IsUnit (∏ a, v a)` using `⟨∏ a, (hv a).unit, by simp [Units.coe_prod]⟩`.

Conclude with `hprod.mul hP`.
-/
theorem isUnit_det_monomial {m : ℕ} (σ : Fin m → Fin m) (hσ : ∀ a, σ (σ a) = a) (v : Fin m → K)
    (hv : ∀ a, IsUnit (v a)) (A : Matrix (Fin m) (Fin m) K) (hA : ∀ a b, A a b = if b = σ a then v a else 0) :
    IsUnit A.det := by
  let P : Matrix (Fin m) (Fin m) K := Matrix.of fun a b => if b = σ a then 1 else 0
  have hAP : A = Matrix.diagonal v * P := by
    ext a b
    rw [hA, Matrix.diagonal_mul]
    simp [P]
  have hPP : P * P = 1 := by
    ext a c
    simp only [P, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_eq_single (σ a)]
    · simp only [if_true, hσ]
      by_cases h : c = a
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (fun h' => h h'.symm)]
    · intro b _ hb; rw [if_neg hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hP : IsUnit P.det := isUnit_iff_exists_inv.2 ⟨P.det, by rw [← Matrix.det_mul, hPP, Matrix.det_one]⟩
  rw [hAP, Matrix.det_mul, Matrix.det_diagonal]
  have hprod : IsUnit (∏ a, v a) := ⟨∏ a, (hv a).unit, by simp [Units.coe_prod]⟩
  exact hprod.mul hP

/- English proof (translation)
Establish `hne : ∀ a : Fin r, σ (Fin.castLE (Nat.le_succ r) a) ≠ Fin.last r` using `fun a h => castLE_ne_last a (by rw [← hσ (Fin.castLE (Nat.le_succ r) a), h, hl])`. Set `σ' : Fin r → Fin r` to `fun a => ⟨(σ (Fin.castLE (Nat.le_succ r) a)).val, Fin.val_lt_last (hne a)⟩`. Establish `hcast : ∀ a : Fin r, Fin.castLE (Nat.le_succ r) (σ' a) = σ (Fin.castLE (Nat.le_succ r) a)` using `fun a => Fin.ext rfl`. Establish `hσ' : ∀ a, σ' (σ' a) = a` using `fun a => by`. Apply `Fin.ext` to reduce the goal to its premises.

Use `show (σ (Fin.castLE (Nat.le_succ r) (σ' a))).val = a.val`. Rewrite using `[hcast, hσ]`. Both sides reduce to the same expression. Unfold `leadM`. Rewrite using `[dif_pos (Nat.le_succ r)]`.

Use `isUnit_det_monomial σ' hσ' (fun a => v (Fin.castLE (Nat.le_succ r) a)) (fun a => ?_) _ (fun a b => ?_)` and prove the remaining obligations. Rewrite using `[show Fin.castLE (Nat.le_succ r) a = a.castSucc from Fin.ext rfl]`. Conclude with `hv a`. Simplify using `only [Matrix.submatrix_apply]`. Rewrite using `[hA]`.

Distinguish the cases in `h : b = σ' a`. Rewrite using `[if_pos h, if_pos (by rw [h, hcast])]`. Rewrite using `[if_neg h, if_neg (fun h' => h (Fin.castLE_injective _ (h'.trans (hcast a).symm)))]`.
-/
theorem isUnit_lead_monomial {r : ℕ} (σ : Fin (r + 1) → Fin (r + 1)) (hσ : ∀ a, σ (σ a) = a)
    (hl : σ (Fin.last r) = Fin.last r) (v : Fin (r + 1) → K) (hv : ∀ a : Fin r, IsUnit (v a.castSucc))
    (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (hA : ∀ a b, A a b = if b = σ a then v a else 0) :
    IsUnit (leadM A r) := by
  have hne : ∀ a : Fin r, σ (Fin.castLE (Nat.le_succ r) a) ≠ Fin.last r := fun a h =>
    castLE_ne_last a (by rw [← hσ (Fin.castLE (Nat.le_succ r) a), h, hl])
  let σ' : Fin r → Fin r := fun a => ⟨(σ (Fin.castLE (Nat.le_succ r) a)).val, Fin.val_lt_last (hne a)⟩
  have hcast : ∀ a : Fin r, Fin.castLE (Nat.le_succ r) (σ' a) = σ (Fin.castLE (Nat.le_succ r) a) :=
    fun a => Fin.ext rfl
  have hσ' : ∀ a, σ' (σ' a) = a := fun a => by
    apply Fin.ext
    show (σ (Fin.castLE (Nat.le_succ r) (σ' a))).val = a.val
    rw [hcast, hσ]
    rfl
  unfold leadM
  rw [dif_pos (Nat.le_succ r)]
  refine isUnit_det_monomial σ' hσ' (fun a => v (Fin.castLE (Nat.le_succ r) a)) (fun a => ?_) _ (fun a b => ?_)
  · rw [show Fin.castLE (Nat.le_succ r) a = a.castSucc from Fin.ext rfl]; exact hv a
  · simp only [Matrix.submatrix_apply]
    rw [hA]
    by_cases h : b = σ' a
    · rw [if_pos h, if_pos (by rw [h, hcast])]
    · rw [if_neg h, if_neg (fun h' => h (Fin.castLE_injective _ (h'.trans (hcast a).symm)))]

end Mono

section Units

variable {D : Formalism.BasicNotions.D7}

/- English proof (translation)
Unfold `twist`. Break down `hs : (D.s.atP p).split with _ | sg` into its components or cases. Conclude with `hx`. Establish `hx' : IsUnit (sg.e x)` using `hx.map sg.e`. Rewrite `hx'` using `[Prod.isUnit_iff]`.

Establish `hy : IsUnit (((sg.e x).1, (-1) ^ s * (sg.e x).2) : (D.s.atP p).Fp × (D.s.atP p).Fp)` using `Prod.isUnit_iff.2 ⟨hx'.1, ((isUnit_neg_one).pow s).mul hx'.2⟩`. Conclude with `hy.map sg.e.symm`.
-/
theorem twist_isUnit (p : PlF D) (s : ℕ) {x : (D.s.atP p).Ep} (hx : IsUnit x) : IsUnit (twist p s x) := by
  unfold twist
  rcases hs : (D.s.atP p).split with _ | sg
  · exact hx
  · have hx' : IsUnit (sg.e x) := hx.map sg.e
    rw [Prod.isUnit_iff] at hx'
    have hy : IsUnit (((sg.e x).1, (-1) ^ s * (sg.e x).2) : (D.s.atP p).Fp × (D.s.atP p).Fp) :=
      Prod.isUnit_iff.2 ⟨hx'.1, ((isUnit_neg_one).pow s).mul hx'.2⟩
    exact hy.map sg.e.symm

/- English proof (translation)
Unfold `qE`. Break down `hs : (D.s.atP p).split with _ | sg` into its components or cases. Conclude with `isUnit_one`. Establish `hq : ((sg.q : (D.s.atP p).Fp)) ≠ 0` using `fun h => sg.q_irr.ne_zero (Subtype.ext h)`. Conclude with `(isUnit_iff_ne_zero.2 hq).map _`.
-/
theorem qE_isUnit (p : PlF D) : IsUnit (qE p) := by
  unfold qE
  rcases hs : (D.s.atP p).split with _ | sg
  · exact isUnit_one
  · have hq : ((sg.q : (D.s.atP p).Fp)) ≠ 0 := fun h => sg.q_irr.ne_zero (Subtype.ext h)
    exact (isUnit_iff_ne_zero.2 hq).map _

variable (Zd : LocDat D)

/- English proof (translation)
Rewrite using `[modMat_blk Zd T T' p w a, if_neg (fun h => ha h.1), sub_zero]`. Establish `hy` using `yP_ne Zd p`. Establish `hcf : ∀ b, cf Zd p b ≠ 0` using `fun b => pow_ne_zero _ (inv_ne_zero hy)`. Use `((isUnit_iff_ne_zero.2 (mul_ne_zero (hcf a) (hcf _))).map _).mul ?_ |>.mul ?_` and prove the remaining obligations. Conclude with `twist_isUnit p _ ((isUnit_iff_ne_zero.2 (pTau_ne' w a)).map _)`.

Take `⟨u, hu⟩` from `qE_isUnit p`. Rewrite using `[← hu, Ring.inverse_unit]`. Conclude with `u⁻¹.isUnit`.
-/
theorem blkMod_isUnit (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (a : Fin (D.R.rS + 1))
    (ha : a ≠ Fin.last D.R.rS) :
    IsUnit (blkMod Zd.δ T T' p (1 + pSt w.1 a.val) (pSz w.1 a.val) (pTau w.1 a.val)) := by
  rw [modMat_blk Zd T T' p w a, if_neg (fun h => ha h.1), sub_zero]
  have hy := yP_ne Zd p
  have hcf : ∀ b, cf Zd p b ≠ 0 := fun b => pow_ne_zero _ (inv_ne_zero hy)
  refine ((isUnit_iff_ne_zero.2 (mul_ne_zero (hcf a) (hcf _))).map _).mul ?_ |>.mul ?_
  · exact twist_isUnit p _ ((isUnit_iff_ne_zero.2 (pTau_ne' w a)).map _)
  · obtain ⟨u, hu⟩ := qE_isUnit p
    rw [← hu, Ring.inverse_unit]
    exact u⁻¹.isUnit

def ShUnit (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p : PlF D) (c : (D.s.atP p).Ep), ∃ n : Fin 3, IsUnit (c + (((n : Fin 3) : ℕ) : (D.s.atP p).Ep))

/- English proof (translation)
Unfold `nSh`. Rewrite using `[dif_pos h]`. Conclude with `h.choose_spec`.
-/
theorem nSh_isUnit {A : Type} [Ring A] (c : A) (h : ∃ n : Fin 3, IsUnit (c + (((n : Fin 3) : ℕ) : A))) :
    IsUnit (c + ((nSh c : ℕ) : A)) := by
  unfold nSh
  rw [dif_pos h]
  exact h.choose_spec

/- English proof (translation)
Introduce `p T T' w hl`. Use `⟨?_, ?_, nSh_isUnit _ (hS p _)⟩` and prove the remaining obligations. Establish `h` using `isUnit_lead_monomial (sgF w) (sgF_sgF w) hl (fun a => pTau w.1 a.val) (fun a => isUnit_iff_ne_zero.2 (pTau_ne' w _)) (ptMat w) (ptMat_apply' w)`. Conclude with `h.ne_zero`. Conclude with `isUnit_lead_monomial (sgF w) (sgF_sgF w) hl _ (fun a => blkMod_isUnit Zd T T' p w a.castSucc (Fin.castSucc_ne_last a)) _ (modMat_apply' Zd.δ T T' p w)`.
-/
theorem modUnits_of (hS : ShUnit D) : ModUnits Zd := by
  intro p T T' w hl
  refine ⟨?_, ?_, nSh_isUnit _ (hS p _)⟩
  · have h := isUnit_lead_monomial (sgF w) (sgF_sgF w) hl (fun a => pTau w.1 a.val)
      (fun a => isUnit_iff_ne_zero.2 (pTau_ne' w _)) (ptMat w) (ptMat_apply' w)
    exact h.ne_zero
  · exact isUnit_lead_monomial (sgF w) (sgF_sgF w) hl _
      (fun a => blkMod_isUnit Zd T T' p w a.castSucc (Fin.castSucc_ne_last a)) _ (modMat_apply' Zd.δ T T' p w)

/- English proof (translation)
The claim follows from `partnerCount_of_modUnits Zd hT2 hI (modUnits_of Zd hS) hB`.
-/
theorem partnerCount_of_shUnit (hT2 : Formalism.MainNotions.ThinScalesBound.T2 D) (hI : IntGenP Zd) (hS : ShUnit D) (hB : BridgeBA) : PartnerIsomorphismCount Zd :=
  partnerCount_of_modUnits Zd hT2 hI (modUnits_of Zd hS) hB

end Units

end Formalism.L2.SG.Pf.PCount
