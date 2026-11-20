import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LeadMAddCorner

noncomputable section

namespace Formalism.L2.SG.Pf.PCount

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc

section Shape

variable {K : Type*} [CommRing K] {r : ℕ}

/- English proof (translation)
Establish `hk' : k.val < r` using `Fin.val_lt_last hk`. Unfold `leadM`. Rewrite using `[dif_pos (Nat.le_succ r)]`. Use `Matrix.det_eq_zero_of_row_eq_zero ⟨k.val, hk'⟩ fun b => ?_` and prove the remaining obligations. Simplify using `only [Matrix.submatrix_apply]`.

Establish `e : Fin.castLE (Nat.le_succ r) ⟨k.val, hk'⟩ = k` using `Fin.ext rfl`. Rewrite using `[e]`. Conclude with `h _ (castLE_ne_last b)`.
-/
theorem leadM_zero_row (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (k : Fin (r + 1)) (hk : k ≠ Fin.last r)
    (h : ∀ b, b ≠ Fin.last r → A k b = 0) : leadM A r = 0 := by
  have hk' : k.val < r := Fin.val_lt_last hk
  unfold leadM
  rw [dif_pos (Nat.le_succ r)]
  refine Matrix.det_eq_zero_of_row_eq_zero ⟨k.val, hk'⟩ fun b => ?_
  simp only [Matrix.submatrix_apply]
  have e : Fin.castLE (Nat.le_succ r) ⟨k.val, hk'⟩ = k := Fin.ext rfl
  rw [e]
  exact h _ (castLE_ne_last b)

/- English proof (translation)
Establish `hA : A = (A + (-A (Fin.last r) (Fin.last r)) • Ecorner r) + A (Fin.last r) (Fin.last r) • Ecorner r`. Rewrite using `[add_assoc, ← add_smul, neg_add_cancel, zero_smul, add_zero]`. Establish `h0 : (A + (-A (Fin.last r) (Fin.last r)) • Ecorner r).det = 0`. Use `Matrix.det_eq_zero_of_row_eq_zero (Fin.last r) fun b => ?_` and prove the remaining obligations. Distinguish the cases in `hb : b = Fin.last r`.

Substitute `hb` using the available equality. Simplify using `[Ecorner]`. Take `⟨b', rfl⟩` from `Fin.exists_castSucc_eq.2 hb`. Simplify using `[Ecorner, (h b').2, Fin.castSucc_ne_last]`. Use `conv_lhs => rw [hA]`.

Rewrite using `[det_add_corner, h0, zero_add, leadM_add_corner]`.
-/
theorem det_of_corner (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K)
    (h : ∀ a : Fin r, A a.castSucc (Fin.last r) = 0 ∧ A (Fin.last r) a.castSucc = 0) :
    A.det = A (Fin.last r) (Fin.last r) * leadM A r := by
  have hA : A = (A + (-A (Fin.last r) (Fin.last r)) • Ecorner r) + A (Fin.last r) (Fin.last r) • Ecorner r := by
    rw [add_assoc, ← add_smul, neg_add_cancel, zero_smul, add_zero]
  have h0 : (A + (-A (Fin.last r) (Fin.last r)) • Ecorner r).det = 0 := by
    refine Matrix.det_eq_zero_of_row_eq_zero (Fin.last r) fun b => ?_
    by_cases hb : b = Fin.last r
    · subst hb; simp [Ecorner]
    · obtain ⟨b', rfl⟩ := Fin.exists_castSucc_eq.2 hb
      simp [Ecorner, (h b').2, Fin.castSucc_ne_last]
  conv_lhs => rw [hA]
  rw [det_add_corner, h0, zero_add, leadM_add_corner]

end Shape

section ModShape

variable {D : Formalism.BasicNotions.D7}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Conclude with `leadM_zero_row _ (sgF w (Fin.last _)) h fun b hb => by`. Rewrite using `[modMat_apply', if_neg (by rw [sgF_sgF]; exact hb)]`. Conclude with `leadM_zero_row (ptMat w) (sgF w (Fin.last _)) h fun b hb => by`. Rewrite using `[ptMat_apply', if_neg (by rw [sgF_sgF]; exact hb)]`.
-/
theorem lead_zero_of_sg (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1))
    (h : sgF w (Fin.last D.R.rS) ≠ Fin.last D.R.rS) :
    leadM (modMat δ T T' p w) D.R.rS = 0 ∧ Dmin w D.R.rS = 0 := by
  constructor
  · exact leadM_zero_row _ (sgF w (Fin.last _)) h fun b hb => by
      rw [modMat_apply', if_neg (by rw [sgF_sgF]; exact hb)]
  · exact leadM_zero_row (ptMat w) (sgF w (Fin.last _)) h fun b hb => by
      rw [ptMat_apply', if_neg (by rw [sgF_sgF]; exact hb)]

/- English proof (translation)
Establish `hne : ∀ a : Fin D.R.rS, a.castSucc ≠ sgF w (Fin.last _)` using `fun a => by`. Rewrite using `[h]`. Conclude with `Fin.castSucc_ne_last a`. Establish `hne' : ∀ a : Fin D.R.rS, Fin.last _ ≠ sgF w a.castSucc` using `fun a e => by`. Use `congrArg (sgF w) e` as an intermediate fact.

Rewrite `this` using `[sgF_sgF, h]`. Conclude with `Fin.castSucc_ne_last a this.symm`. Establish `hp : pSig w.1 D.R.rS = D.R.rS`. Use `congrArg Fin.val h` as an intermediate fact. Simplify `this` using `[sgF]`.

Establish `hsum` using `w.2.2`. Take `⟨-, -, h3, -, h5⟩` from `pBlock w.1 D.R.rS (by rw [hsum]; omega)`. Establish `h5'` using `h5 (by rw [hsum])`. Rewrite `h5'` using `[hsum]`. Rewrite `h3` using `[hp]`.

Use `⟨fun a => ⟨?_, ?_⟩, fun a => ⟨?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[modMat_apply', if_neg (hne' a)]`. Rewrite using `[modMat_apply', if_neg (hne a)]`. Rewrite using `[ptMat_apply', if_neg (hne' a)]`. Rewrite using `[ptMat_apply', if_neg (hne a)]`.

Rewrite using `[modMat_apply', if_pos h.symm]`. Simplify using `only [Fin.val_last]`. Rewrite using `[show 1 + pSt w.1 D.R.rS = D.R.rS + 1 by omega, show pSz w.1 D.R.rS = 1 by omega]`. Rewrite using `[ptMat_apply', if_pos h.symm]`. Simplify using `only [Fin.val_last]`.
-/
theorem shape_of_sg (δ : ∀ p, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1))
    (h : sgF w (Fin.last D.R.rS) = Fin.last D.R.rS) :
    (∀ a : Fin D.R.rS, modMat δ T T' p w a.castSucc (Fin.last _) = 0 ∧
      modMat δ T T' p w (Fin.last _) a.castSucc = 0) ∧
    (∀ a : Fin D.R.rS, ptMat w a.castSucc (Fin.last _) = 0 ∧ ptMat w (Fin.last _) a.castSucc = 0) ∧
    modMat δ T T' p w (Fin.last _) (Fin.last _) = blkMod δ T T' p (D.R.rS + 1) 1 (pTau w.1 D.R.rS) ∧
    ptMat w (Fin.last _) (Fin.last _) = pTau w.1 D.R.rS := by
  have hne : ∀ a : Fin D.R.rS, a.castSucc ≠ sgF w (Fin.last _) := fun a => by
    rw [h]; exact Fin.castSucc_ne_last a
  have hne' : ∀ a : Fin D.R.rS, Fin.last _ ≠ sgF w a.castSucc := fun a e => by
    have := congrArg (sgF w) e
    rw [sgF_sgF, h] at this
    exact Fin.castSucc_ne_last a this.symm
  have hp : pSig w.1 D.R.rS = D.R.rS := by
    have := congrArg Fin.val h
    simpa [sgF] using this
  have hsum := w.2.2
  obtain ⟨-, -, h3, -, h5⟩ := pBlock w.1 D.R.rS (by rw [hsum]; omega)
  have h5' := h5 (by rw [hsum])
  rw [hsum] at h5'
  rw [hp] at h3
  refine ⟨fun a => ⟨?_, ?_⟩, fun a => ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [modMat_apply', if_neg (hne' a)]
  · rw [modMat_apply', if_neg (hne a)]
  · rw [ptMat_apply', if_neg (hne' a)]
  · rw [ptMat_apply', if_neg (hne a)]
  · rw [modMat_apply', if_pos h.symm]
    simp only [Fin.val_last]
    rw [show 1 + pSt w.1 D.R.rS = D.R.rS + 1 by omega, show pSz w.1 D.R.rS = 1 by omega]
  · rw [ptMat_apply', if_pos h.symm]
    simp only [Fin.val_last]

variable (Zd : LocDat D)

def ModUnits : Prop :=
  ∀ (p : PlF D) (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)), sgF w (Fin.last D.R.rS) = Fin.last D.R.rS →
    Dmin w D.R.rS ≠ 0 ∧ IsUnit (leadM (modMat Zd.δ T T' p w) D.R.rS) ∧
    IsUnit (blkMod Zd.δ T T' p (D.R.rS + 1) 1 (pTau w.1 D.R.rS) +
      ((nSh (blkMod Zd.δ T T' p (D.R.rS + 1) 1 (pTau w.1 D.R.rS)) : ℕ) : (D.s.atP p).Ep))

/- English proof (translation)
Introduce `p T T' w`. Distinguish the cases in `hs : sgF w (Fin.last D.R.rS) = Fin.last D.R.rS`. Take `⟨hD, hu, hn⟩` from `hU p T T' w hs`. Take `⟨hm, hpt, hc, hpc⟩` from `shape_of_sg Zd.δ T T' p w hs`. Establish `hz : zetaOf w = pTau w.1 D.R.rS`.

Unfold `zetaOf`. Establish `e : Dmin w (D.R.rS + 1) = pTau w.1 D.R.rS * Dmin w D.R.rS` using `by show leadM (ptMat w) (D.R.rS + 1) = _ * leadM (ptMat w) D.R.rS`. Rewrite using `[leadM_top, det_of_corner _ hpt, hpc]`. Rewrite using `[e, mul_div_cancel_right₀ _ hD]`. Apply the tactic sequence `refine ⟨fun h => absurd h hD, fun _ => ⟨hu, hm, ?_, ?_⟩⟩ <;> rw [hz]`.

Conclude with `hc`. Conclude with `hn`. Take `⟨h1, h2⟩` from `lead_zero_of_sg Zd.δ T T' p w hs`. Conclude with `⟨fun _ => h1, fun h => absurd h2 h⟩`.
-/
theorem modKind_of (hU : ModUnits Zd) : ModKind Zd := by
  intro p T T' w
  by_cases hs : sgF w (Fin.last D.R.rS) = Fin.last D.R.rS
  · obtain ⟨hD, hu, hn⟩ := hU p T T' w hs
    obtain ⟨hm, hpt, hc, hpc⟩ := shape_of_sg Zd.δ T T' p w hs
    have hz : zetaOf w = pTau w.1 D.R.rS := by
      unfold zetaOf
      have e : Dmin w (D.R.rS + 1) = pTau w.1 D.R.rS * Dmin w D.R.rS := by
        show leadM (ptMat w) (D.R.rS + 1) = _ * leadM (ptMat w) D.R.rS
        rw [leadM_top, det_of_corner _ hpt, hpc]
      rw [e, mul_div_cancel_right₀ _ hD]
    refine ⟨fun h => absurd h hD, fun _ => ⟨hu, hm, ?_, ?_⟩⟩ <;> rw [hz]
    · exact hc
    · exact hn
  · obtain ⟨h1, h2⟩ := lead_zero_of_sg Zd.δ T T' p w hs
    exact ⟨fun _ => h1, fun h => absurd h2 h⟩

/- English proof (translation)
The claim follows from `partnerIsomorphismCount_of_bounds Zd hT2 hI (leadZZ_holds Zd) (modKind_of Zd hU) hB`.
-/
theorem partnerCount_of_modUnits (hT2 : Formalism.MainNotions.ThinScalesBound.T2 D) (hI : IntGenP Zd) (hU : ModUnits Zd) (hB : BridgeBA) : PartnerIsomorphismCount Zd :=
  partnerIsomorphismCount_of_bounds Zd hT2 hI (leadZZ_holds Zd) (modKind_of Zd hU) hB

end ModShape

end Formalism.L2.SG.Pf.PCount
