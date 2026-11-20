import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TwistC

noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.BlockPermutation Formalism.L2.SG.Pf.StabIntSh

namespace Formalism.L2.SG.Pf.StabIntLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (w : Point D.host.E (D.R.rS + 1))

def coordX (X : MatR D) : FreeE w → D.host.E := fun q => X q.1.1 q.1.2

/- English proof (translation)
Use function extensionality and compare the values at `a c`. Distinguish the cases in `h : a = c`. Substitute `h` using the available equality. Simplify using `[Xmat, (hU a a).2 rfl]`. Simplify using `only [Xmat, h, if_false]`.

Distinguish the cases in `h2 : a < c ∧ blkOf w.1 a.val = blkOf w.1 c.val`. Rewrite using `[dif_pos h2]`. Both sides reduce to the same expression. Rewrite using `[dif_neg h2]`. Distinguish the cases in `h3 : a < c`.

Conclude with `(hB a c (fun e => h2 ⟨h3, e⟩)).symm`. Conclude with `((hU a c).1 (lt_of_le_of_ne (not_lt.1 h3) (Ne.symm h))).symm`.
-/
theorem Xmat_coordX {X : MatR D} (hU : UpU X) (hB : IsBlockDiagonalMatrix w X) : Xmat w (coordX w X) = X := by
  funext a c
  by_cases h : a = c
  · subst h; simp [Xmat, (hU a a).2 rfl]
  · simp only [Xmat, h, if_false]
    by_cases h2 : a < c ∧ blkOf w.1 a.val = blkOf w.1 c.val
    · rw [dif_pos h2]; rfl
    · rw [dif_neg h2]
      by_cases h3 : a < c
      · exact (hB a c (fun e => h2 ⟨h3, e⟩)).symm
      · exact ((hU a c).1 (lt_of_le_of_ne (not_lt.1 h3) (Ne.symm h))).symm

/- English proof (translation)
Use function extensionality and compare the values at `q`. Conclude with `Xmat_q w y q`.
-/
theorem coordX_Xmat (y : FreeE w → D.host.E) : coordX w (Xmat w y) = y := by
  funext q; exact Xmat_q w y q

/- English proof (translation)
Take `⟨-, hU, hB⟩` from `X_of_st w hβ hb hW`. Rewrite using `[mem_stabInt_iff_X δ M hA u u' w β hβ hb hW, ← Xmat_coordX w hU hB, coordX_Xmat]`. Conclude with `twistC δ M hA hodd w _`.
-/
theorem mem_stabInt_iff_twist (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (hA : ∀ p, Agree δ M p) (hodd : Odd (gS D))
    (u u' : D.what₂.Word) (β : GLR D) (hβ : IsLoUni (β : MatR D)) {b : MatR D} (hb : IsUpUni b)
    (hW : (β : MatR D) * ptMat w * b = ptMat w) :
    β ∈ stabInt D u u' δ M w ↔
      ∀ q, coordX w ((ptMat w)⁻¹ * (β : MatR D) * ptMat w) q -
        τA w q (coordX w ((ptMat w)⁻¹ * (β : MatR D) * ptMat w)) ∈ Λq w q := by
  obtain ⟨-, hU, hB⟩ := X_of_st w hβ hb hW
  rw [mem_stabInt_iff_X δ M hA u u' w β hβ hb hW, ← Xmat_coordX w hU hB, coordX_Xmat]
  exact twistC δ M hA hodd w _

/- English proof (translation)
Take `⟨hlo, hXi, hW, hdet⟩` from `st_of_X w (Xmat_upU w y) (Xmat_blk w y)`. Use `set B := ptMat w * Xmat w y * (ptMat w)⁻¹`. Establish `hd : IsUnit B.det` using `by rw [hdet]; exact isUnit_one`. Use `⟨⟨B, B⁻¹, Matrix.mul_nonsing_inv B hd, Matrix.nonsing_inv_mul B hd⟩, hlo, hXi, hW, ?_⟩` and prove the remaining obligations. Establish `hu` using `ptMat_isUnit w`.

Use `show (ptMat w)⁻¹ * (ptMat w * Xmat w y * (ptMat w)⁻¹) * ptMat w = Xmat w y`. Rewrite using `[show (ptMat w)⁻¹ * (ptMat w * Xmat w y * (ptMat w)⁻¹) * ptMat w = ((ptMat w)⁻¹ * ptMat w) * Xmat w y * ((ptMat w)⁻¹ * ptMat w) by simp only [Matrix.mul_assoc], Matrix.nonsing_inv_mul _ hu, Matrix.one_mul, Matrix.mul_one]`.
-/
theorem exists_of_coord (y : FreeE w → D.host.E) :
    ∃ β : GLR D, IsLoUni (β : MatR D) ∧ IsUpUni (Xmat w y)⁻¹ ∧
      (β : MatR D) * ptMat w * (Xmat w y)⁻¹ = ptMat w ∧ (ptMat w)⁻¹ * (β : MatR D) * ptMat w = Xmat w y := by
  obtain ⟨hlo, hXi, hW, hdet⟩ := st_of_X w (Xmat_upU w y) (Xmat_blk w y)
  set B := ptMat w * Xmat w y * (ptMat w)⁻¹
  have hd : IsUnit B.det := by rw [hdet]; exact isUnit_one
  refine ⟨⟨B, B⁻¹, Matrix.mul_nonsing_inv B hd, Matrix.nonsing_inv_mul B hd⟩, hlo, hXi, hW, ?_⟩
  have hu := ptMat_isUnit w
  show (ptMat w)⁻¹ * (ptMat w * Xmat w y * (ptMat w)⁻¹) * ptMat w = Xmat w y
  rw [show (ptMat w)⁻¹ * (ptMat w * Xmat w y * (ptMat w)⁻¹) * ptMat w =
      ((ptMat w)⁻¹ * ptMat w) * Xmat w y * ((ptMat w)⁻¹ * ptMat w) by simp only [Matrix.mul_assoc],
    Matrix.nonsing_inv_mul _ hu, Matrix.one_mul, Matrix.mul_one]

/- English proof (translation)
Apply the tactic sequence `unfold hpr; split_ifs <;> omega`.
-/
theorem hpr_lt {p q : FreeE w} (h : hgt w q < hgt w p) : hpr w q < hpr w p := by
  unfold hpr; split_ifs <;> omega

/- English proof (translation)
Use function extensionality and compare the values at `p`. Unfold `trunc`. Use `split_ifs with hp`. Conclude with `h p (hpr_lt w hp)`. Both sides reduce to the same expression.
-/
theorem trunc_eq {y y' : FreeE w → D.host.E} (q : FreeE w) (h : ∀ p, hpr w p < hpr w q → y p = y' p) :
    trunc w y (hgt w q) = trunc w y' (hgt w q) := by
  funext p
  unfold trunc
  split_ifs with hp
  · exact h p (hpr_lt w hp)
  · rfl

/- English proof (translation)
Unfold `τA`. Distinguish the cases in `h1 : selfP w q`. Simplify using `only [h1, if_true, cf, trunc_eq w q h]`. Distinguish the cases in `h2 : upperM w q`. Take `⟨hp1, hp2⟩` from `upper_qbar w h2`.

Establish `hlt : hpr w (qbar w q) < hpr w q`. Unfold `hpr`. Rewrite using `[hgt_qbar]`. Simplify using `only [h2, hp2, if_true, if_false]`. Use linear arithmetic over natural numbers and integers.

Establish `hc : cf w y (qbar w q) = cf w y' (qbar w q)`. Unfold `cf`. Rewrite using `[trunc_eq w (qbar w q) (fun p hp => h p (lt_trans hp hlt))]`. Simplify using `only [h1, h2, if_false, if_true, h _ hlt, hc]`. Simplify using `only [h1, h2, if_false]`.
-/
theorem τA_lowdep (q : FreeE w) {y y' : FreeE w → D.host.E} (h : ∀ p, hpr w p < hpr w q → y p = y' p) :
    τA w q y = τA w q y' := by
  unfold τA
  by_cases h1 : selfP w q
  · simp only [h1, if_true, cf, trunc_eq w q h]
  · by_cases h2 : upperM w q
    · obtain ⟨hp1, hp2⟩ := upper_qbar w h2
      have hlt : hpr w (qbar w q) < hpr w q := by
        unfold hpr; rw [hgt_qbar]; simp only [h2, hp2, if_true, if_false]; omega
      have hc : cf w y (qbar w q) = cf w y' (qbar w q) := by
        unfold cf
        rw [trunc_eq w (qbar w q) (fun p hp => h p (lt_trans hp hlt))]
      simp only [h1, h2, if_false, if_true, h _ hlt, hc]
    · simp only [h1, h2, if_false]

end Formalism.L2.SG.Pf.StabIntLat
