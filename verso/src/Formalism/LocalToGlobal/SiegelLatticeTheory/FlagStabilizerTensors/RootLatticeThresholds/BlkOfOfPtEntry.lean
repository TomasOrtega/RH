import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.VolumeDictionaryLuDecomposition
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IndexCocycleOrbits.PtEntryExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.AdmNPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipBasis
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem

noncomputable section

open scoped Classical
open NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp Formalism.L2.SG.PairVal Formalism.L2.SG.Pf.StabilizerIndexVolumes

namespace Formalism.L2.SG.Pf.VolPinAsm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section GlobalTheory

variable {K : Type*} [Zero K]

/- English proof (translation)
The claim follows from `| [], _, _, _ => le_rfl | (_, s) :: bs, i, j, h => by simp only [Formalism.L2.SG.RealObj.blkOf] split_ifs with h1 h2 h2 · exact le_rfl · exact Nat.zero_le _ · omega · exact Nat.succ_le_succ (blkOf_mono bs _ _ (by omega))`.
-/
theorem blkOf_mono : ∀ (bs : List (K × ℕ)) (i j : ℕ), i ≤ j → Formalism.L2.SG.RealObj.blkOf bs i ≤ Formalism.L2.SG.RealObj.blkOf bs j
  | [], _, _, _ => le_rfl
  | (_, s) :: bs, i, j, h => by
    simp only [Formalism.L2.SG.RealObj.blkOf]
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exact Nat.zero_le _
    · omega
    · exact Nat.succ_le_succ (blkOf_mono bs _ _ (by omega))

/- English proof (translation)
The claim follows from `| [], _, _, h => (h rfl).elim | (t, s) :: bs, i, j, h => by simp only [ptEntry] at h simp only [Formalism.L2.SG.RealObj.blkOf] split_ifs at h with h1 h2 <;> first | exact (h rfl).elim | (split_ifs <;> first | rfl | omega) | (split_ifs with h3 h4 h4 <;> first | rfl | omega | (rw [ …`.
-/
theorem blkOf_of_ptEntry : ∀ (bs : List (K × ℕ)) (i j : ℕ), ptEntry bs i j ≠ 0 →
    Formalism.L2.SG.RealObj.blkOf bs i = Formalism.L2.SG.RealObj.blkOf bs j
  | [], _, _, h => (h rfl).elim
  | (t, s) :: bs, i, j, h => by
    simp only [ptEntry] at h
    simp only [Formalism.L2.SG.RealObj.blkOf]
    split_ifs at h with h1 h2 <;> first | exact (h rfl).elim | (split_ifs <;> first | rfl | omega) |
      (split_ifs with h3 h4 h4 <;> first | rfl | omega | (rw [blkOf_of_ptEntry bs _ _ h]))

end GlobalTheory

section Rat

variable {D : D7}

/- English proof (translation)
Unfold `sgnM`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `b`. Rewrite using `[← mul_pow]`.

Simplify using the standard rewrite rules.
-/
private theorem sgnM_mul_self' {r : ℕ} {K : Type*} [Field K] :
    (sgnM r : Matrix (Fin (r + 1)) (Fin (r + 1)) K) * sgnM r = 1 := by
  unfold sgnM
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext b
  rw [← mul_pow]
  simp

/- English proof (translation)
Establish `hbt : N.BlockTriangular id`. Introduce `i j hij`. Conclude with `(hN i j).1 hij`. Establish `hdet : N.det = 1`. Rewrite using `[Matrix.det_of_upperTriangular hbt]`.

Conclude with `Finset.prod_eq_one fun i _ => (hN i i).2 rfl`. Establish `hu : IsUnit N.det` using `by rw [hdet]; exact isUnit_one`. Use `haveI : Invertible N := Matrix.invertibleOfIsUnitDet N hu`. Establish `hbt' : N⁻¹.BlockTriangular id` using `Matrix.blockTriangular_inv_of_blockTriangular hbt`. Use `⟨fun i j => ⟨fun hji => hbt' hji, fun hij => ?_⟩, hu⟩` and prove the remaining obligations.

Substitute `hij` using the available equality. Establish `h1 : (N⁻¹ * N) i i = 1` using `by rw [Matrix.nonsing_inv_mul N hu, Matrix.one_apply_eq]`. Rewrite `h1` using `[Matrix.mul_apply, Finset.sum_eq_single i]`. Rewrite `h1` using `[(hN i i).2 rfl, mul_one]`. Then use the resulting hypothesis. Introduce `c _ hc`.

Break down `lt_or_gt_of_ne hc with h | h` into its components or cases. Rewrite using `[hbt' h, zero_mul]`. Rewrite using `[(hN c i).1 h, mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`.
-/
private theorem isUpUni_inv_and_isUnit_det_of_isUpUni {n : ℕ} {K : Type*} [Field K] {N : Matrix (Fin n) (Fin n) K} (hN : IsUpUni N) :
    IsUpUni N⁻¹ ∧ IsUnit N.det := by
  have hbt : N.BlockTriangular id := by
    intro i j hij
    exact (hN i j).1 hij
  have hdet : N.det = 1 := by
    rw [Matrix.det_of_upperTriangular hbt]
    exact Finset.prod_eq_one fun i _ => (hN i i).2 rfl
  have hu : IsUnit N.det := by rw [hdet]; exact isUnit_one
  haveI : Invertible N := Matrix.invertibleOfIsUnitDet N hu
  have hbt' : N⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hbt
  refine ⟨fun i j => ⟨fun hji => hbt' hji, fun hij => ?_⟩, hu⟩
  subst hij
  have h1 : (N⁻¹ * N) i i = 1 := by rw [Matrix.nonsing_inv_mul N hu, Matrix.one_apply_eq]
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at h1
  · rwa [(hN i i).2 rfl, mul_one] at h1
  · intro c _ hc
    rcases lt_or_gt_of_ne hc with h | h
    · rw [hbt' h, zero_mul]
    · rw [(hN c i).1 h, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

/- English proof (translation)
Establish `hWu : IsUnit (ptMat w).det` using `isUnit_iff_ne_zero.mpr (Formalism.L2.SG.Pf.StabilizerIndexVolumes.ptMat_det w)`. Establish `hLu : IsUnit L.det`. Establish `hbt : Lᵀ.BlockTriangular id`. Introduce `i j h`. Conclude with `(hL j i).1 h`.

Rewrite using `[← Matrix.det_transpose, Matrix.det_of_upperTriangular hbt]`. Rewrite using `[Finset.prod_eq_one (fun i _ => (show Lᵀ i i = 1 from (hL i i).2 rfl))]`. Conclude with `isUnit_one`. Establish `hs : (sgnM D.R.rS : MatR D) * sgnM D.R.rS = 1` using `sgnM_mul_self'`. Establish `hb2 : (ptMat w)⁻¹ * B⁻¹ * ptMat w = b`.

Establish `e : B⁻¹ * ptMat w = ptMat w * b`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, e, ← mul_assoc, Matrix.nonsing_inv_mul _ hWu, one_mul]`. Establish `hZ : Zhat F0 F'' = L * ptMat w * U * sgnM D.R.rS`. Rewrite using `[← hZ1, mul_assoc, hs, mul_one]`.

Establish `hsi : (sgnM D.R.rS : MatR D)⁻¹ = sgnM D.R.rS` using `Matrix.inv_eq_left_inv hs`. Establish `hL' : ∀ Z : MatR D, L⁻¹ * (L * Z) = Z`. Introduce `Z`. Rewrite using `[← mul_assoc, Matrix.nonsing_inv_mul L hLu, one_mul]`. Establish `hb3 : ∀ Z : MatR D, (ptMat w)⁻¹ * (B⁻¹ * (ptMat w * Z)) = b * Z`.

Introduce `Z`. Rewrite using `[← hb2]`. Simplify using `only [mul_assoc]`. Unfold `Formalism.L2.SG.Pf.StabilizerIndexVolumes.P'm`. Rewrite using `[hZ]`.

Simplify using `only [Matrix.mul_inv_rev, hsi, mul_assoc, hL', hb3]`.
-/
theorem P'm_eq {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {F'' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} {w : Point D.host.E (D.R.rS + 1)} {L U : MatR D}
    (hL : IsLoUni L) (hU : IsUpUni U) (hZu : IsUnit (Zhat F0 F'').det)
    (hZ1 : Zhat F0 F'' * sgnM D.R.rS = L * ptMat w * U) {B b : MatR D} (hBu : IsUnit B.det)
    (hab : B * ptMat w * b = ptMat w) :
    P'm F0 F'' L B = sgnM D.R.rS * (U⁻¹ * b * U) * sgnM D.R.rS := by
  have hWu : IsUnit (ptMat w).det := isUnit_iff_ne_zero.mpr (Formalism.L2.SG.Pf.StabilizerIndexVolumes.ptMat_det w)
  have hLu : IsUnit L.det := by
    have hbt : Lᵀ.BlockTriangular id := by
      intro i j h
      exact (hL j i).1 h
    rw [← Matrix.det_transpose, Matrix.det_of_upperTriangular hbt]
    rw [Finset.prod_eq_one (fun i _ => (show Lᵀ i i = 1 from (hL i i).2 rfl))]
    exact isUnit_one
  have hs : (sgnM D.R.rS : MatR D) * sgnM D.R.rS = 1 := sgnM_mul_self'
  have hb2 : (ptMat w)⁻¹ * B⁻¹ * ptMat w = b := by
    have e : B⁻¹ * ptMat w = ptMat w * b := by
      calc B⁻¹ * ptMat w = B⁻¹ * (B * ptMat w * b) := by rw [hab]
        _ = ptMat w * b := by rw [← mul_assoc, ← mul_assoc, Matrix.nonsing_inv_mul B hBu, one_mul]
    rw [mul_assoc, e, ← mul_assoc, Matrix.nonsing_inv_mul _ hWu, one_mul]
  have hZ : Zhat F0 F'' = L * ptMat w * U * sgnM D.R.rS := by
    rw [← hZ1, mul_assoc, hs, mul_one]
  have hsi : (sgnM D.R.rS : MatR D)⁻¹ = sgnM D.R.rS := Matrix.inv_eq_left_inv hs
  have hL' : ∀ Z : MatR D, L⁻¹ * (L * Z) = Z := by
    intro Z; rw [← mul_assoc, Matrix.nonsing_inv_mul L hLu, one_mul]
  have hb3 : ∀ Z : MatR D, (ptMat w)⁻¹ * (B⁻¹ * (ptMat w * Z)) = b * Z := by
    intro Z; rw [← hb2]; simp only [mul_assoc]
  unfold Formalism.L2.SG.Pf.StabilizerIndexVolumes.P'm
  rw [hZ]
  simp only [Matrix.mul_inv_rev, hsi, mul_assoc, hL', hb3]

/- English proof (translation)
Take `⟨-, b, hb, hbW⟩` from `hβ`. Establish `hWu : IsUnit (ptMat w).det` using `isUnit_iff_ne_zero.mpr (Formalism.L2.SG.Pf.StabilizerIndexVolumes.ptMat_det w)`. Take `⟨hbi, hbu⟩` from `isUpUni_inv_and_isUnit_det_of_isUpUni hb`. Establish `hβu : IsUnit (β : MatR D).det` using `(Matrix.isUnit_iff_isUnit_det _).mp β.isUnit`. Establish `h1 : (β : MatR D) * ptMat w = ptMat w * b⁻¹` using `by conv_rhs => rw [← hbW]`.

Rewrite using `[mul_assoc ((β : MatR D) * ptMat w), Matrix.mul_nonsing_inv b hbu, mul_one]`. Establish `key : (ptMat w)⁻¹ * (β : MatR D) * ptMat w = b⁻¹`. Rewrite using `[mul_assoc, h1, ← mul_assoc, Matrix.nonsing_inv_mul _ hWu, one_mul]`. Use `⟨by rw [key]; exact hbi, ?_⟩` and prove the remaining obligations. Rewrite using `[key, mul_assoc, ← h1, ← mul_assoc, Matrix.nonsing_inv_mul _ hβu, one_mul]`.
-/
theorem conjW_up {w : Point D.host.E (D.R.rS + 1)} {β : GLR D} (hβ : β ∈ StSet (ptMat w)) :
    IsUpUni ((ptMat w)⁻¹ * (β : MatR D) * ptMat w) ∧
      (β : MatR D)⁻¹ * ptMat w * ((ptMat w)⁻¹ * (β : MatR D) * ptMat w) = ptMat w := by
  obtain ⟨-, b, hb, hbW⟩ := hβ
  have hWu : IsUnit (ptMat w).det := isUnit_iff_ne_zero.mpr (Formalism.L2.SG.Pf.StabilizerIndexVolumes.ptMat_det w)
  obtain ⟨hbi, hbu⟩ := isUpUni_inv_and_isUnit_det_of_isUpUni hb
  have hβu : IsUnit (β : MatR D).det := (Matrix.isUnit_iff_isUnit_det _).mp β.isUnit
  have h1 : (β : MatR D) * ptMat w = ptMat w * b⁻¹ := by
    conv_rhs => rw [← hbW]
    rw [mul_assoc ((β : MatR D) * ptMat w), Matrix.mul_nonsing_inv b hbu, mul_one]
  have key : (ptMat w)⁻¹ * (β : MatR D) * ptMat w = b⁻¹ := by
    rw [mul_assoc, h1, ← mul_assoc, Matrix.nonsing_inv_mul _ hWu, one_mul]
  refine ⟨by rw [key]; exact hbi, ?_⟩
  rw [key, mul_assoc, ← h1, ← mul_assoc, Matrix.nonsing_inv_mul _ hβu, one_mul]

end Rat

section FinTwoTypeFamily

variable {D : D7}

/- English proof (translation)
Take `⟨hlo, -⟩` from `hβ`. Establish `hWu : IsUnit (ptMat w).det` using `isUnit_iff_ne_zero.mpr (Formalism.L2.SG.Pf.StabilizerIndexVolumes.ptMat_det w)`. Use `haveI : Invertible (ptMat w) := Matrix.invertibleOfIsUnitDet _ hWu`. Apply the tactic sequence `have hWb : ∀ i j : Fin (D.R.rS + 1), ptMat w i j ≠ 0 → Formalism.L2.SG.RealObj.blkOf w.1 i.1 = Formalism.L2.SG.RealObj.blkOf w.1 j.1 := fun i j h => blkOf_of_ptEntry w.1 i.1 j.1 h`. Establish `bt1 : (ptMat w).BlockTriangular (fun i : Fin (D.R.rS + 1) => Formalism.L2.SG.RealObj.blkOf w.1 i.1)`.

Introduce `i j h`. Assume the negation of the conclusion as `hne`. Conclude with `h.ne' (hWb i j hne)`. Establish `bt2 : (ptMat w).BlockTriangular (fun i : Fin (D.R.rS + 1) => OrderDual.toDual (Formalism.L2.SG.RealObj.blkOf w.1 i.1))`. Introduce `i j h`.

Assume the negation of the conclusion as `hne`. Conclude with `(show Formalism.L2.SG.RealObj.blkOf w.1 i.1 < Formalism.L2.SG.RealObj.blkOf w.1 j.1 from h).ne (hWb i j hne)`. Establish `bi1` using `Matrix.blockTriangular_inv_of_blockTriangular bt1`. Establish `bi2` using `Matrix.blockTriangular_inv_of_blockTriangular bt2`. Establish `hWi : ∀ i j : Fin (D.R.rS + 1), (ptMat w)⁻¹ i j ≠ 0 → Formalism.L2.SG.RealObj.blkOf w.1 i.1 = Formalism.L2.SG.RealObj.blkOf w.1 j.1`.

Introduce `i j h`. Break down `lt_trichotomy (Formalism.L2.SG.RealObj.blkOf w.1 i.1) (Formalism.L2.SG.RealObj.blkOf w.1 j.1) with hl | he | hg` into its components or cases. Conclude with `absurd (bi2 hl) h`. Conclude with `he`. Conclude with `absurd (bi1 hg) h`.

Establish `hcd' : Formalism.L2.SG.RealObj.blkOf w.1 c.1 < Formalism.L2.SG.RealObj.blkOf w.1 d.1` using `lt_of_le_of_ne (blkOf_mono w.1 c.1 d.1 hcd.le) hb`. Rewrite using `[Matrix.mul_apply]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `d' _`. Rewrite using `[Matrix.mul_apply, Finset.sum_mul]`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `c' _`. Distinguish the cases in `h1 : (ptMat w)⁻¹ c c' = 0`. Rewrite using `[h1, zero_mul, zero_mul]`. Distinguish the cases in `h2 : ptMat w d' d = 0`.

Rewrite using `[h2, mul_zero]`. Establish `e1` using `hWi c c' h1`. Establish `e2` using `hWb d' d h2`. Establish `hlt : c' < d'`. Assume the negation of the conclusion as `hle`.

Use `push_neg at hle`. Use `blkOf_mono w.1 d'.1 c'.1 hle` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[(hlo c' d').1 hlt, mul_zero, zero_mul]`.
-/
theorem conjW_blk {w : Point D.host.E (D.R.rS + 1)} {β : GLR D} (hβ : β ∈ StSet (ptMat w))
    (c d : Fin (D.R.rS + 1)) (hcd : c < d)
    (hb : Formalism.L2.SG.RealObj.blkOf w.1 c.1 ≠ Formalism.L2.SG.RealObj.blkOf w.1 d.1) :
    ((ptMat w)⁻¹ * (β : MatR D) * ptMat w) c d = 0 := by
  obtain ⟨hlo, -⟩ := hβ
  have hWu : IsUnit (ptMat w).det := isUnit_iff_ne_zero.mpr (Formalism.L2.SG.Pf.StabilizerIndexVolumes.ptMat_det w)
  haveI : Invertible (ptMat w) := Matrix.invertibleOfIsUnitDet _ hWu
  have hWb : ∀ i j : Fin (D.R.rS + 1), ptMat w i j ≠ 0 →
      Formalism.L2.SG.RealObj.blkOf w.1 i.1 = Formalism.L2.SG.RealObj.blkOf w.1 j.1 :=
    fun i j h => blkOf_of_ptEntry w.1 i.1 j.1 h
  have bt1 : (ptMat w).BlockTriangular (fun i : Fin (D.R.rS + 1) => Formalism.L2.SG.RealObj.blkOf w.1 i.1) := by
    intro i j h
    by_contra hne
    exact h.ne' (hWb i j hne)
  have bt2 : (ptMat w).BlockTriangular
      (fun i : Fin (D.R.rS + 1) => OrderDual.toDual (Formalism.L2.SG.RealObj.blkOf w.1 i.1)) := by
    intro i j h
    by_contra hne
    exact (show Formalism.L2.SG.RealObj.blkOf w.1 i.1 < Formalism.L2.SG.RealObj.blkOf w.1 j.1 from h).ne (hWb i j hne)
  have bi1 := Matrix.blockTriangular_inv_of_blockTriangular bt1
  have bi2 := Matrix.blockTriangular_inv_of_blockTriangular bt2
  have hWi : ∀ i j : Fin (D.R.rS + 1), (ptMat w)⁻¹ i j ≠ 0 →
      Formalism.L2.SG.RealObj.blkOf w.1 i.1 = Formalism.L2.SG.RealObj.blkOf w.1 j.1 := by
    intro i j h
    rcases lt_trichotomy (Formalism.L2.SG.RealObj.blkOf w.1 i.1) (Formalism.L2.SG.RealObj.blkOf w.1 j.1) with hl | he | hg
    · exact absurd (bi2 hl) h
    · exact he
    · exact absurd (bi1 hg) h
  have hcd' : Formalism.L2.SG.RealObj.blkOf w.1 c.1 < Formalism.L2.SG.RealObj.blkOf w.1 d.1 :=
    lt_of_le_of_ne (blkOf_mono w.1 c.1 d.1 hcd.le) hb
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro d' _
  rw [Matrix.mul_apply, Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro c' _
  by_cases h1 : (ptMat w)⁻¹ c c' = 0
  · rw [h1, zero_mul, zero_mul]
  by_cases h2 : ptMat w d' d = 0
  · rw [h2, mul_zero]
  have e1 := hWi c c' h1
  have e2 := hWb d' d h2
  have hlt : c' < d' := by
    by_contra hle
    push_neg at hle
    have := blkOf_mono w.1 d'.1 c'.1 hle
    omega
  rw [(hlo c' d').1 hlt, mul_zero, zero_mul]

end FinTwoTypeFamily

section FrameC

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {m : ℕ}

def FM (e : Fin m → V) (g : V → V) (G : Matrix (Fin m) (Fin m) K) : Prop := ∀ b, g (e b) = ∑ c, G c b • e c

/- English proof (translation)
Unfold `FM at hg hh ⊢`. Introduce `b`. Simplify using `only [Function.comp_apply, hh b, map_sum, map_smul, hg, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Rewrite using `[mul_comm]`.
-/
theorem FM_comp {e : Fin m → V} {g h : V →ₗ[K] V} {G H : Matrix (Fin m) (Fin m) K}
    (hg : FM e g G) (hh : FM e h H) : FM e (g ∘ h) (G * H) := by
  unfold FM at hg hh ⊢
  intro b
  simp only [Function.comp_apply, hh b, map_sum, map_smul, hg, Finset.smul_sum, smul_smul,
    Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  rw [mul_comm]

/- English proof (translation)
Unfold `FM at hg ⊢`. Introduce `b`. Apply `g.injective` to reduce the goal to its premises. Rewrite using `[LinearEquiv.apply_symm_apply]`. Simplify using `only [map_sum, map_smul, hg, Finset.smul_sum, smul_smul]`.

Rewrite using `[Finset.sum_comm]`. Establish `hGG : G * G⁻¹ = 1` using `Matrix.mul_nonsing_inv G hG`. Establish `hc : ∀ d, ∑ c, G⁻¹ c b * G d c = (G * G⁻¹) d b` using `fun d => by`. Rewrite using `[Matrix.mul_apply]`. Conclude with `Finset.sum_congr rfl fun c _ => mul_comm _ _`.

Simplify using `only [← Finset.sum_smul, hc, hGG, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.
-/
theorem FM_inv {e : Fin m → V} {g : V ≃ₗ[K] V} {G : Matrix (Fin m) (Fin m) K} (hg : FM e g G)
    (hG : IsUnit G.det) : FM e g.symm G⁻¹ := by
  unfold FM at hg ⊢
  intro b
  apply g.injective
  rw [LinearEquiv.apply_symm_apply]
  simp only [map_sum, map_smul, hg, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have hGG : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G hG
  have hc : ∀ d, ∑ c, G⁻¹ c b * G d c = (G * G⁻¹) d b := fun d => by
    rw [Matrix.mul_apply]; exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  simp only [← Finset.sum_smul, hc, hGG, Matrix.one_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

end FrameC

section InSFrame

/- English proof (translation)
Establish `hy : ∀ b : Fin (r + 1), ∃ y : Fin r → ℂ, (∀ i : Fin r, b.val ≤ i.val → y i = 0) ∧ g *ᵥ Formalism.L2.SG.RealObj.fam e z b = Formalism.L2.SG.RealObj.fam e z b + ∑ i, y i • e i`. Introduce `b`. Use `Fin.lastCases ?_ (fun j => ?_) b` and prove the remaining obligations. Establish `hm` using `h.2`. Unfold `Formalism.L2.SG.HidaSetting.spanLt at hm`.

Take `⟨l, hl, hx⟩` from `(Finsupp.mem_span_image_iff_linearCombination ℂ).mp hm`. Use `⟨fun i => l i, fun i hi => absurd hi (by simp), ?_⟩` and prove the remaining obligations. Rewrite `hx` using `[Finsupp.linearCombination_apply]`. Establish `hx' : ∑ i, l i • e i = (g - 1) *ᵥ z` using `by rw [← hx, Finsupp.sum_fintype]; simp`. Simplify using `only [Formalism.L2.SG.RealObj.fam, Fin.snoc_last]`.

Rewrite using `[hx', Matrix.sub_mulVec, Matrix.one_mulVec]`. Normalize the expressions using the abelian group laws. Establish `hm` using `h.1 j`. Unfold `Formalism.L2.SG.HidaSetting.spanLt at hm`. Take `⟨l, hl, hx⟩` from `(Finsupp.mem_span_image_iff_linearCombination ℂ).mp hm`.

Use `⟨fun i => l i, fun i hi => ?_, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `h3 : i ∈ (↑l.support : Set (Fin r))` using `by simpa using hne`. Establish `h4` using `hl h3`. Simplify using `only [Set.mem_setOf_eq] at h4`.

Simplify using `at hi`. Use linear arithmetic over natural numbers and integers. Rewrite `hx` using `[Finsupp.linearCombination_apply]`. Establish `hx' : ∑ i, l i • e i = (g - 1) *ᵥ e j` using `by rw [← hx, Finsupp.sum_fintype]; simp`. Simplify using `only [Formalism.L2.SG.RealObj.fam, Fin.snoc_castSucc]`.

Rewrite using `[hx', Matrix.sub_mulVec, Matrix.one_mulVec]`. Normalize the expressions using the abelian group laws. Use `choose y hy0 hyeq using hy`. Use `⟨fun c b => (if c = b then 1 else 0) + (if h : c.val < r then y b ⟨c.val, h⟩ else 0), ?_, ?_⟩` and prove the remaining obligations. Introduce `i j`.

Use `⟨fun hji => ?_, fun hij => ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[if_neg (ne_of_gt hji)]`. Use `split_ifs with h`. Rewrite using `[hy0 j ⟨i.val, h⟩ (le_of_lt hji)]`.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Substitute `hij dsimp only` using the available equality. Rewrite using `[if_pos rfl]`. Use `split_ifs with h`.

Rewrite using `[hy0 i ⟨i.val, h⟩ le_rfl]`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Introduce `b show g *ᵥ _ = _`. Simplify using `only [add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.

Rewrite using `[hyeq b, Fin.sum_univ_castSucc]`. Simplify using `[Formalism.L2.SG.RealObj.fam, Fin.snoc_castSucc]`.
-/
theorem inS_frame {n r : ℕ} {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {g : Matrix (Fin n) (Fin n) ℂ}
    (h : Formalism.L2.SG.HidaSetting.InS e z g) :
    ∃ S : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, IsUpUni S ∧
      FM (Formalism.L2.SG.RealObj.fam e z) (fun x => g *ᵥ x) S := by
  have hy : ∀ b : Fin (r + 1), ∃ y : Fin r → ℂ, (∀ i : Fin r, b.val ≤ i.val → y i = 0) ∧
      g *ᵥ Formalism.L2.SG.RealObj.fam e z b = Formalism.L2.SG.RealObj.fam e z b + ∑ i, y i • e i := by
    intro b
    refine Fin.lastCases ?_ (fun j => ?_) b
    · have hm := h.2
      unfold Formalism.L2.SG.HidaSetting.spanLt at hm
      obtain ⟨l, hl, hx⟩ := (Finsupp.mem_span_image_iff_linearCombination ℂ).mp hm
      refine ⟨fun i => l i, fun i hi => absurd hi (by simp), ?_⟩
      rw [Finsupp.linearCombination_apply] at hx
      have hx' : ∑ i, l i • e i = (g - 1) *ᵥ z := by rw [← hx, Finsupp.sum_fintype]; simp
      simp only [Formalism.L2.SG.RealObj.fam, Fin.snoc_last]
      rw [hx', Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    · have hm := h.1 j
      unfold Formalism.L2.SG.HidaSetting.spanLt at hm
      obtain ⟨l, hl, hx⟩ := (Finsupp.mem_span_image_iff_linearCombination ℂ).mp hm
      refine ⟨fun i => l i, fun i hi => ?_, ?_⟩
      · by_contra hne
        have h3 : i ∈ (↑l.support : Set (Fin r)) := by simpa using hne
        have h4 := hl h3
        simp only [Set.mem_setOf_eq] at h4
        simp at hi
        omega
      · rw [Finsupp.linearCombination_apply] at hx
        have hx' : ∑ i, l i • e i = (g - 1) *ᵥ e j := by rw [← hx, Finsupp.sum_fintype]; simp
        simp only [Formalism.L2.SG.RealObj.fam, Fin.snoc_castSucc]
        rw [hx', Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  choose y hy0 hyeq using hy
  refine ⟨fun c b => (if c = b then 1 else 0) + (if h : c.val < r then y b ⟨c.val, h⟩ else 0), ?_, ?_⟩
  · intro i j
    refine ⟨fun hji => ?_, fun hij => ?_⟩
    · dsimp only
      rw [if_neg (ne_of_gt hji)]
      split_ifs with h
      · rw [hy0 j ⟨i.val, h⟩ (le_of_lt hji)]; simp
      · simp
    · subst hij
      dsimp only
      rw [if_pos rfl]
      split_ifs with h
      · rw [hy0 i ⟨i.val, h⟩ le_rfl]; simp
      · simp
  · intro b
    show g *ᵥ _ = _
    simp only [add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [hyeq b, Fin.sum_univ_castSucc]
    simp [Formalism.L2.SG.RealObj.fam, Fin.snoc_castSucc]

end InSFrame

section MatC

variable {n m : ℕ}

/- English proof (translation)
Establish `hg' : ∀ b, g *ᵥ e b = ∑ c, G c b • e c` using `hg`. Establish `hh' : ∀ b, h *ᵥ e b = ∑ c, H c b • e c` using `hh`. Use `show ∀ b, (g * h) *ᵥ e b = ∑ c, (G * H) c b • e c`. Introduce `b`. Rewrite using `[← Matrix.mulVec_mulVec, hh' b]`.

Simplify using `only [Matrix.mulVec_sum, Matrix.mulVec_smul, hg', Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`.
-/
theorem FMm_mul {e : Fin m → Fin n → ℂ} {g h : Matrix (Fin n) (Fin n) ℂ} {G H : Matrix (Fin m) (Fin m) ℂ}
    (hg : FM e (fun x => g *ᵥ x) G) (hh : FM e (fun x => h *ᵥ x) H) : FM e (fun x => (g * h) *ᵥ x) (G * H) := by
  have hg' : ∀ b, g *ᵥ e b = ∑ c, G c b • e c := hg
  have hh' : ∀ b, h *ᵥ e b = ∑ c, H c b • e c := hh
  show ∀ b, (g * h) *ᵥ e b = ∑ c, (G * H) c b • e c
  intro b
  rw [← Matrix.mulVec_mulVec, hh' b]
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, hg', Finset.smul_sum, smul_smul,
    Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  rw [mul_comm]

/- English proof (translation)
Establish `hg' : ∀ b, g *ᵥ e b = ∑ c, G c b • e c` using `hg`. Use `show ∀ b, g⁻¹ *ᵥ e b = ∑ c, G⁻¹ c b • e c`. Introduce `b`. Establish `hinj : ∀ x y : Fin n → ℂ, g *ᵥ x = g *ᵥ y → x = y`. Introduce `x y hxy`.

Establish `h2` using `congrArg (fun z => g⁻¹ *ᵥ z) hxy`. Simplify `h2` using `only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul g hgu, Matrix.one_mulVec]`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv g hgu, Matrix.one_mulVec]`. Simplify using `only [Matrix.mulVec_sum, Matrix.mulVec_smul, hg', Finset.smul_sum, smul_smul]`.

Rewrite using `[Finset.sum_comm]`. Establish `hGG : G * G⁻¹ = 1` using `Matrix.mul_nonsing_inv G hG`. Establish `hc : ∀ d, ∑ c, G⁻¹ c b * G d c = (G * G⁻¹) d b` using `fun d => by`. Rewrite using `[Matrix.mul_apply]`. Conclude with `Finset.sum_congr rfl fun c _ => mul_comm _ _`.

Simplify using `only [← Finset.sum_smul, hc, hGG, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.
-/
theorem FMm_inv {e : Fin m → Fin n → ℂ} {g : Matrix (Fin n) (Fin n) ℂ} {G : Matrix (Fin m) (Fin m) ℂ}
    (hgu : IsUnit g.det) (hg : FM e (fun x => g *ᵥ x) G) (hG : IsUnit G.det) :
    FM e (fun x => g⁻¹ *ᵥ x) G⁻¹ := by
  have hg' : ∀ b, g *ᵥ e b = ∑ c, G c b • e c := hg
  show ∀ b, g⁻¹ *ᵥ e b = ∑ c, G⁻¹ c b • e c
  intro b
  have hinj : ∀ x y : Fin n → ℂ, g *ᵥ x = g *ᵥ y → x = y := by
    intro x y hxy
    have h2 := congrArg (fun z => g⁻¹ *ᵥ z) hxy
    simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul g hgu, Matrix.one_mulVec] using h2
  apply hinj
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv g hgu, Matrix.one_mulVec]
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, hg', Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have hGG : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G hG
  have hc : ∀ d, ∑ c, G⁻¹ c b * G d c = (G * G⁻¹) d b := fun d => by
    rw [Matrix.mul_apply]; exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  simp only [← Finset.sum_smul, hc, hGG, Matrix.one_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/- English proof (translation)
Take `⟨hNi, -⟩` from `isUpUni_inv_and_isUnit_det_of_isUpUni hN`. Establish `key : ∀ Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, (∀ c d, a ≤ c → d ≤ b → (c, d) ≠ (a, b) → Z c d = 0) → (N⁻¹ * Z * N) a b = Z a b`. Introduce `Z hZ`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single b]`. Rewrite using `[(hN b b).2 rfl, mul_one, Matrix.mul_apply, Finset.sum_eq_single a]`.

Rewrite using `[(hNi a a).2 rfl, one_mul]`. Introduce `c _ hc`. Distinguish the cases in `hac : a ≤ c`. Rewrite using `[hZ c b hac le_rfl (by simp [hc]), mul_zero]`. Rewrite using `[(hNi a c).1 (not_le.mp hac), zero_mul]`.

Simplify using the standard rewrite rules. Introduce `d _ hd`. Distinguish the cases in `hdb : d ≤ b`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]`. Introduce `c _`.

Distinguish the cases in `hac : a ≤ c`. Rewrite using `[hZ c d hac hdb (by simp [hd]), mul_zero]`. Rewrite using `[(hNi a c).1 (not_le.mp hac), zero_mul]`. Rewrite using `[(hN d b).1 (not_le.mp hdb), mul_zero]`. Simplify using the standard rewrite rules.

Establish `hZ` using `key (Y - Y') (fun c d h1 h2 h3 => by rw [Matrix.sub_apply, h c d h1 h2 h3, sub_self])`. Simplify using `only [mul_sub, sub_mul, Matrix.sub_apply] at hZ`. Take the linear combination `hZ`.
-/
theorem conj_shear {r : ℕ} {N : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hN : IsUpUni N)
    {Y Y' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (a b : Fin (r + 1))
    (h : ∀ c d, a ≤ c → d ≤ b → (c, d) ≠ (a, b) → Y c d = Y' c d) :
    (N⁻¹ * Y * N) a b - Y a b = (N⁻¹ * Y' * N) a b - Y' a b := by
  obtain ⟨hNi, -⟩ := isUpUni_inv_and_isUnit_det_of_isUpUni hN
  have key : ∀ Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ,
      (∀ c d, a ≤ c → d ≤ b → (c, d) ≠ (a, b) → Z c d = 0) → (N⁻¹ * Z * N) a b = Z a b := by
    intro Z hZ
    rw [Matrix.mul_apply, Finset.sum_eq_single b]
    · rw [(hN b b).2 rfl, mul_one, Matrix.mul_apply, Finset.sum_eq_single a]
      · rw [(hNi a a).2 rfl, one_mul]
      · intro c _ hc
        by_cases hac : a ≤ c
        · rw [hZ c b hac le_rfl (by simp [hc]), mul_zero]
        · rw [(hNi a c).1 (not_le.mp hac), zero_mul]
      · simp
    · intro d _ hd
      by_cases hdb : d ≤ b
      · rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
        intro c _
        by_cases hac : a ≤ c
        · rw [hZ c d hac hdb (by simp [hd]), mul_zero]
        · rw [(hNi a c).1 (not_le.mp hac), zero_mul]
      · rw [(hN d b).1 (not_le.mp hdb), mul_zero]
    · simp
  have hZ := key (Y - Y') (fun c d h1 h2 h3 => by rw [Matrix.sub_apply, h c d h1 h2 h3, sub_self])
  simp only [mul_sub, sub_mul, Matrix.sub_apply] at hZ
  linear_combination hZ

end MatC

section RealFrame

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

abbrev efr (u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) : Fin (D.R.rS + 1) → Fin X.B.I.n → ℂ :=
  Formalism.L2.SG.RealObj.fam (fun a => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR a)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u'))

/- English proof (translation)
Use `Fin.lastCases ?_ (fun i => ?_) c` and prove the remaining obligations. Simplify using `only [efr, Formalism.L2.SG.RealObj.fam, Fin.snoc_last, FlagG.fvec, X.flagZVector u']`. Both sides reduce to the same expression. Simplify using `only [efr, Formalism.L2.SG.RealObj.fam, Fin.snoc_castSucc, FlagG.fvec, X.Fu_e u']`. Both sides reduce to the same expression.
-/
theorem efr_eq (u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) (c : Fin (D.R.rS + 1)) :
    efr X u' v c = Formalism.L2.SG.HidaSetting.rv X.B.I v (X.crd ((X.Fu u').fvec c)) := by
  refine Fin.lastCases ?_ (fun i => ?_) c
  · simp only [efr, Formalism.L2.SG.RealObj.fam, Fin.snoc_last, FlagG.fvec, X.flagZVector u']; rfl
  · simp only [efr, Formalism.L2.SG.RealObj.fam, Fin.snoc_castSucc, FlagG.fvec, X.Fu_e u']; rfl

/- English proof (translation)
Take `⟨M, -, h1, -, h3⟩` from `hx`. Introduce `b`. Use `show Formalism.MainNotions.S.uMat (x.1 v) *ᵥ efr X u' v b = _`. Rewrite using `[efr_eq, h1 v, Formalism.L2.SG.Pf.Level.rv_mulVec, ← h3, hK b, Formalism.L2.SG.NormCut.crd_sum' X]`. Rewrite using `[← Formalism.L2.SG.Pf.Level.rvHom_apply, map_sum]`.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Formalism.L2.SG.NormCut.crd_smul' X, Formalism.L2.SG.Pf.Level.rv_smul, Formalism.L2.SG.Pf.Level.rvHom_apply, ← efr_eq]`. Both sides reduce to the same expression.
-/
theorem realFM {u' : D.what₂.Word} {x : X.B.I.GA} {ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hx : RatLink X x ρ)
    {K : MatR D} (hK : FM (X.Fu u').fvec ρ K) (v : InfinitePlace X.B.I.F) :
    FM (efr X u' v) (fun y => Formalism.MainNotions.S.uMat (x.1 v) *ᵥ y) (K.map (phiV X v)) := by
  obtain ⟨M, -, h1, -, h3⟩ := hx
  intro b
  show Formalism.MainNotions.S.uMat (x.1 v) *ᵥ efr X u' v b = _
  rw [efr_eq, h1 v, Formalism.L2.SG.Pf.Level.rv_mulVec, ← h3, hK b, Formalism.L2.SG.NormCut.crd_sum' X]
  rw [← Formalism.L2.SG.Pf.Level.rvHom_apply, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Formalism.L2.SG.NormCut.crd_smul' X, Formalism.L2.SG.Pf.Level.rv_smul, Formalism.L2.SG.Pf.Level.rvHom_apply, ← efr_eq]
  rfl

/- English proof (translation)
Establish `hE' : ∀ x y : (VS D).V, Formalism.L2.SG.Pf.Level.hE X (X.crd x) (X.crd y) = X.ιE.symm ((VS D).hT x y)` using `fun x y => by rw [← Formalism.L2.SG.PoincareInHH.Cut.hform_crd X x y, RingEquiv.symm_apply_apply]`. Rewrite using `[efr_eq, Formalism.L2.SG.Pf.Level.hJ_rv, show X.fR a = X.crd (X.fY a) from rfl, hE']`. Use `Fin.lastCases ?_ (fun i => ?_) d` and prove the remaining obligations. Rewrite using `[if_neg (Fin.castSucc_lt_last a).ne']`. Simplify using `only [FlagG.fvec, Fin.snoc_last, X.flagZVector u', (X.zu_orth u' a).2, map_zero]`.

Simplify using `only [FlagG.fvec, Fin.snoc_castSucc, X.Fu_e u']`. Establish `h` using `(VS D).herm.eq (X.eX i) (X.fY a)`. Establish `h2 : (VS D).hT (X.fY a) (X.eX i) = if i = a then 1 else 0`. Apply the tactic sequence `rw [← h, X.ef i a]; split_ifs <;> simp`. Rewrite using `[h2]`.

Distinguish the cases in `hia : i = a`. Substitute `hia` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg hia, if_neg (fun h => hia (Fin.castSucc_inj.1 h))]`. Simplify using the standard rewrite rules.
-/
theorem hJ_efr (u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) (a : Fin D.R.rS) (d : Fin (D.R.rS + 1)) :
    Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.fR a)) (efr X u' v d) =
      if d = Fin.castSucc a then 1 else 0 := by
  have hE' : ∀ x y : (VS D).V, Formalism.L2.SG.Pf.Level.hE X (X.crd x) (X.crd y) = X.ιE.symm ((VS D).hT x y) :=
    fun x y => by rw [← Formalism.L2.SG.PoincareInHH.Cut.hform_crd X x y, RingEquiv.symm_apply_apply]
  rw [efr_eq, Formalism.L2.SG.Pf.Level.hJ_rv, show X.fR a = X.crd (X.fY a) from rfl, hE']
  refine Fin.lastCases ?_ (fun i => ?_) d
  · rw [if_neg (Fin.castSucc_lt_last a).ne']
    simp only [FlagG.fvec, Fin.snoc_last, X.flagZVector u', (X.zu_orth u' a).2, map_zero]
  · simp only [FlagG.fvec, Fin.snoc_castSucc, X.Fu_e u']
    have h := (VS D).herm.eq (X.eX i) (X.fY a)
    have h2 : (VS D).hT (X.fY a) (X.eX i) = if i = a then 1 else 0 := by
      rw [← h, X.ef i a]; split_ifs <;> simp
    rw [h2]
    by_cases hia : i = a
    · subst hia; simp
    · rw [if_neg hia, if_neg (fun h => hia (Fin.castSucc_inj.1 h))]; simp

/- English proof (translation)
Establish `h` using `map_sum (Formalism.L2.SG.Pf.Vanish2.hJL ε y) (fun i => c i • e i) Finset.univ`. Simplify using `only [map_smul, smul_eq_mul] at h`. Conclude with `h`.
-/
theorem hJ_sum_right (ε : Fin X.B.I.n → Bool) (y : Fin X.B.I.n → ℂ) {m : ℕ} (c : Fin m → ℂ)
    (e : Fin m → Fin X.B.I.n → ℂ) : Formalism.L2.SG.HidaSetting.hJ ε y (∑ i, c i • e i) = ∑ i, c i * Formalism.L2.SG.HidaSetting.hJ ε y (e i) := by
  have h := map_sum (Formalism.L2.SG.Pf.Vanish2.hJL ε y) (fun i => c i • e i) Finset.univ
  simp only [map_smul, smul_eq_mul] at h
  exact h

/- English proof (translation)
Establish `hg' : ∀ d, g *ᵥ efr X u' v d = ∑ c, G c d • efr X u' v c` using `hg`. Rewrite using `[Matrix.mulVec_smul, hg' b, Finset.smul_sum]`. Simplify using `only [smul_smul, hJ_sum_right X]`. Simplify using `only [hJ_efr, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.
-/
theorem coef_efr (u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) {g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ}
    {G : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ} (hg : FM (efr X u' v) (fun y => g *ᵥ y) G)
    (a : Fin D.R.rS) (b : Fin (D.R.rS + 1)) (κ : ℂ) :
    Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.fR a)) (g *ᵥ (κ • efr X u' v b)) =
      κ * G (Fin.castSucc a) b := by
  have hg' : ∀ d, g *ᵥ efr X u' v d = ∑ c, G c d • efr X u' v c := hg
  rw [Matrix.mulVec_smul, hg' b, Finset.smul_sum]
  simp only [smul_smul, hJ_sum_right X]
  simp only [hJ_efr, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end RealFrame

section KFM

variable {D : D7} {T' : D.host.E}

/- English proof (translation)
Establish `hA : FM F0'.fvec ⇑(g⁻¹ * τ * g) P`. Introduce `b`. Use `show g⁻¹ (τ (g (F0'.fvec b))) = _`. Rewrite using `[hg b, hτ b, map_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, ← hg c]`. Use `show P c b • g.symm (g (F0'.fvec c)) = _`. Rewrite using `[LinearEquiv.symm_apply_apply]`. Establish `hinv : FM F0'.fvec ⇑(m'⁻¹) Mm⁻¹` using `FM_inv hm hMm`. Establish `h1` using `FM_comp (g := m'.toLinearMap) (h := (g⁻¹ * τ * g).toLinearMap) hm hA`.

Establish `h2` using `FM_comp (g := m'.toLinearMap ∘ₗ (g⁻¹ * τ * g).toLinearMap) (h := (m'⁻¹).toLinearMap) h1 hinv`. Conclude with `h2`.
-/
theorem K_FM {F0' F'' : FlagG (VS D) D.R.rS T'} (τ g m' : (VS D).V ≃ₗ[D.host.E] (VS D).V) {P Mm : MatR D}
    (hg : ∀ b, g (F0'.fvec b) = F''.fvec b) (hτ : FM F''.fvec τ P) (hm : FM F0'.fvec m' Mm)
    (hMm : IsUnit Mm.det) : FM F0'.fvec (m' * (g⁻¹ * τ * g) * m'⁻¹) (Mm * P * Mm⁻¹) := by
  have hA : FM F0'.fvec ⇑(g⁻¹ * τ * g) P := by
    intro b
    show g⁻¹ (τ (g (F0'.fvec b))) = _
    rw [hg b, hτ b, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul, ← hg c]
    show P c b • g.symm (g (F0'.fvec c)) = _
    rw [LinearEquiv.symm_apply_apply]
  have hinv : FM F0'.fvec ⇑(m'⁻¹) Mm⁻¹ := FM_inv hm hMm
  have h1 := FM_comp (g := m'.toLinearMap) (h := (g⁻¹ * τ * g).toLinearMap) hm hA
  have h2 := FM_comp (g := m'.toLinearMap ∘ₗ (g⁻¹ * τ * g).toLinearMap) (h := (m'⁻¹).toLinearMap) h1 hinv
  exact h2

end KFM

section Alin

variable {D : D7} (w : Point D.host.E (D.R.rS + 1)) (rdc : ℂ)

def Yhat (x : Formalism.L2.SG.RealObj.FreeE w → ℂ) : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ :=
  fun c d => if h : c < d ∧ Formalism.L2.SG.RealObj.blkOf w.1 c.1 = Formalism.L2.SG.RealObj.blkOf w.1 d.1 then
    x ⟨(c, d), h⟩ / rdc ^ (d.1 - c.1) else 0

/- English proof (translation)
Use extensionality with `c d`. Simplify using `only [Yhat, Matrix.add_apply]`. Use `split_ifs with h`. Conclude with `add_div _ _ _`. Simplify using the standard rewrite rules.
-/
theorem Yhat_add (x y : Formalism.L2.SG.RealObj.FreeE w → ℂ) : Yhat w rdc (x + y) = Yhat w rdc x + Yhat w rdc y := by
  ext c d
  simp only [Yhat, Matrix.add_apply]
  split_ifs with h
  · exact add_div _ _ _
  · simp

/- English proof (translation)
Use extensionality with `c d`. Simplify using `only [Yhat, Matrix.smul_apply]`. Use `split_ifs with h`. Conclude with `mul_div_assoc _ _ _`. Simplify using the standard rewrite rules.
-/
theorem Yhat_smul (k : ℂ) (x : Formalism.L2.SG.RealObj.FreeE w → ℂ) : Yhat w rdc (k • x) = k • Yhat w rdc x := by
  ext c d
  simp only [Yhat, Matrix.smul_apply]
  split_ifs with h
  · exact mul_div_assoc _ _ _
  · simp

def Alin (N : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ) :
    (Formalism.L2.SG.RealObj.FreeE w → ℂ) →ₗ[ℂ] (Formalism.L2.SG.RealObj.FreeE w → ℂ) where
  toFun x p := rdc ^ (p.1.2.1 - p.1.1.1) * (N⁻¹ * Yhat w rdc x * N) p.1.1 p.1.2
  map_add' x y := by
    funext p
    simp only [Yhat_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, Pi.add_apply]; ring
  map_smul' k x := by
    funext p
    simp only [Yhat_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply,
      Pi.smul_apply]; ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Alin_apply (N : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ) (x : Formalism.L2.SG.RealObj.FreeE w → ℂ)
    (p : Formalism.L2.SG.RealObj.FreeE w) :
    Alin w rdc N x p = rdc ^ (p.1.2.1 - p.1.1.1) * (N⁻¹ * Yhat w rdc x * N) p.1.1 p.1.2 := rfl

/- English proof (translation)
Establish `hcond : p.1.1 < p.1.2 ∧ Formalism.L2.SG.RealObj.blkOf w.1 p.1.1.1 = Formalism.L2.SG.RealObj.blkOf w.1 p.1.2.1` using `p.2`. Establish `hx : ∀ z : Formalism.L2.SG.RealObj.FreeE w → ℂ, z p = rdc ^ (p.1.2.1 - p.1.1.1) * Yhat w rdc z p.1.1 p.1.2`. Introduce `z`. Establish `e1 : Yhat w rdc z p.1.1 p.1.2 = z p / rdc ^ (p.1.2.1 - p.1.1.1)`. Simplify using `only [Yhat, dif_pos hcond]`.

Both sides reduce to the same expression. Rewrite using `[e1, mul_div_cancel₀ _ (pow_ne_zero _ hrd)]`. Establish `hcs` using `conj_shear hN (Y := Yhat w rdc x) (Y' := Yhat w rdc x') p.1.1 p.1.2 ?_`. Rewrite using `[Alin_apply, Alin_apply, hx x, hx x', ← mul_sub, ← mul_sub, hcs]`. Introduce `c d hac hdb hne`.

Distinguish the cases in `hcd : c < d ∧ Formalism.L2.SG.RealObj.blkOf w.1 c.1 = Formalism.L2.SG.RealObj.blkOf w.1 d.1`. Simplify using `only [Yhat, dif_pos hcd]`. Use `congr 1`. Apply `h` to reduce the goal to its premises. Establish `h1 : p.1.1.val ≤ c.val` using `hac`.

Establish `h2 : d.val ≤ p.1.2.val` using `hdb`. Establish `h3 : c.val < d.val` using `hcd.1`. Establish `h4 : c.val ≠ p.1.1.val ∨ d.val ≠ p.1.2.val`. Assume the negation of the conclusion as `hh`. Use `push_neg at hh`.

Conclude with `hne (Prod.ext (Fin.ext hh.1) (Fin.ext hh.2))`. Use `show d.val - c.val < p.1.2.val - p.1.1.val`. Use linear arithmetic over natural numbers and integers. Simplify using `only [Yhat, dif_neg hcd]`.
-/
theorem Alin_shear {N : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ} (hN : IsUpUni N) (hrd : rdc ≠ 0)
    (x x' : Formalism.L2.SG.RealObj.FreeE w → ℂ) (p : Formalism.L2.SG.RealObj.FreeE w)
    (h : ∀ q : Formalism.L2.SG.RealObj.FreeE w, q.1.2.val - q.1.1.val < p.1.2.val - p.1.1.val → x q = x' q) :
    Alin w rdc N x p - x p = Alin w rdc N x' p - x' p := by
  have hcond : p.1.1 < p.1.2 ∧
      Formalism.L2.SG.RealObj.blkOf w.1 p.1.1.1 = Formalism.L2.SG.RealObj.blkOf w.1 p.1.2.1 := p.2
  have hx : ∀ z : Formalism.L2.SG.RealObj.FreeE w → ℂ,
      z p = rdc ^ (p.1.2.1 - p.1.1.1) * Yhat w rdc z p.1.1 p.1.2 := by
    intro z
    have e1 : Yhat w rdc z p.1.1 p.1.2 = z p / rdc ^ (p.1.2.1 - p.1.1.1) := by
      simp only [Yhat, dif_pos hcond]
      rfl
    rw [e1, mul_div_cancel₀ _ (pow_ne_zero _ hrd)]
  have hcs := conj_shear hN (Y := Yhat w rdc x) (Y' := Yhat w rdc x') p.1.1 p.1.2 ?_
  · rw [Alin_apply, Alin_apply, hx x, hx x', ← mul_sub, ← mul_sub, hcs]
  · intro c d hac hdb hne
    by_cases hcd : c < d ∧ Formalism.L2.SG.RealObj.blkOf w.1 c.1 = Formalism.L2.SG.RealObj.blkOf w.1 d.1
    · simp only [Yhat, dif_pos hcd]
      congr 1
      apply h
      have h1 : p.1.1.val ≤ c.val := hac
      have h2 : d.val ≤ p.1.2.val := hdb
      have h3 : c.val < d.val := hcd.1
      have h4 : c.val ≠ p.1.1.val ∨ d.val ≠ p.1.2.val := by
        by_contra hh
        push_neg at hh
        exact hne (Prod.ext (Fin.ext hh.1) (Fin.ext hh.2))
      show d.val - c.val < p.1.2.val - p.1.1.val
      omega
    · simp only [Yhat, dif_neg hcd]

end Alin

section Helpers

variable {D : D7}

/- English proof (translation)
Introduce `i j`. Use `⟨fun hji => ?_, fun hij => ?_⟩` and prove the remaining obligations. Simplify using `[Matrix.map_apply, (h i j).1 hji]`. Simplify using `[Matrix.map_apply, (h i j).2 hij]`.
-/
theorem upUni_map {n : ℕ} {K L : Type*} [Field K] [Field L] (f : K →+* L) {A : Matrix (Fin n) (Fin n) K}
    (h : IsUpUni A) : IsUpUni (A.map f) := by
  intro i j
  refine ⟨fun hji => ?_, fun hij => ?_⟩
  · simp [Matrix.map_apply, (h i j).1 hji]
  · simp [Matrix.map_apply, (h i j).2 hij]

/- English proof (translation)
Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[sgnM]`. Simplify using `[sgnM, h]`.
-/
theorem sgnM_map {r : ℕ} {K L : Type*} [Field K] [Field L] (f : K →+* L) :
    (sgnM r : Matrix (Fin (r + 1)) (Fin (r + 1)) K).map f = sgnM r := by
  ext i j
  by_cases h : i = j
  · subst h; simp [sgnM]
  · simp [sgnM, h]

/- English proof (translation)
Simplify using `only [sgnM, Matrix.mul_diagonal, Matrix.diagonal_mul]`.
-/
theorem sgn_conj_apply {r : ℕ} {K : Type*} [Field K] (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (i j : Fin (r + 1)) :
    (sgnM r * A * sgnM r : Matrix (Fin (r + 1)) (Fin (r + 1)) K) i j =
      (-1) ^ (r - i.val) * A i j * (-1) ^ (r - j.val) := by
  simp only [sgnM, Matrix.mul_diagonal, Matrix.diagonal_mul]

/- English proof (translation)
Rewrite using `[← Matrix.map_mul, Matrix.nonsing_inv_mul A hA]`. Simplify using the standard rewrite rules.
-/
theorem map_inv_mul {n : ℕ} {K L : Type*} [Field K] [Field L] (φ : K →+* L) {A : Matrix (Fin n) (Fin n) K}
    (hA : IsUnit A.det) : (A⁻¹).map φ * A.map φ = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul A hA]
  simp

/- English proof (translation)
Rewrite using `[← Matrix.map_mul, Matrix.mul_nonsing_inv A hA]`. Simplify using the standard rewrite rules.
-/
theorem map_mul_inv {n : ℕ} {K L : Type*} [Field K] [Field L] (φ : K →+* L) {A : Matrix (Fin n) (Fin n) K}
    (hA : IsUnit A.det) : A.map φ * (A⁻¹).map φ = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv A hA]
  simp

/- English proof (translation)
Establish `hs : ∀ Z : Matrix (Fin (n + 1)) (Fin (n + 1)) L, sgnM n * (sgnM n * Z) = Z`. Introduce `Z`. Rewrite using `[← mul_assoc, sgnM_mul_self', one_mul]`. Establish `hm : ∀ Z : Matrix (Fin (n + 1)) (Fin (n + 1)) L, (Mm⁻¹).map φ * (Mm.map φ * Z) = Z`. Introduce `Z`.

Rewrite using `[← mul_assoc, map_inv_mul φ hMm, one_mul]`. Establish `hu : ∀ Z : Matrix (Fin (n + 1)) (Fin (n + 1)) L, U.map φ * ((U⁻¹).map φ * Z) = Z`. Introduce `Z`. Rewrite using `[← mul_assoc, map_mul_inv φ hU, one_mul]`. Establish `hS' : ∀ Z : Matrix (Fin (n + 1)) (Fin (n + 1)) L, S * (S⁻¹ * Z) = Z`.

Introduce `Z`. Rewrite using `[← mul_assoc, Matrix.mul_nonsing_inv S hS, one_mul]`. Simplify using `only [mul_assoc, hs, hm, hu, hS']`.
-/
theorem conj_key {n : ℕ} {K : Type*} [Field K] {L : Type*} [Field L] (φ : K →+* L)
    {S : Matrix (Fin (n + 1)) (Fin (n + 1)) L} {Mm U X : Matrix (Fin (n + 1)) (Fin (n + 1)) K}
    (hS : IsUnit S.det) (hMm : IsUnit Mm.det) (hU : IsUnit U.det) :
    (sgnM n * U.map φ * sgnM n * (Mm⁻¹).map φ * S) *
        (S⁻¹ * (Mm.map φ * (sgnM n * ((U⁻¹).map φ * X.map φ * U.map φ) * sgnM n) * (Mm⁻¹).map φ) * S) =
      (sgnM n * X.map φ * sgnM n) * (sgnM n * U.map φ * sgnM n * (Mm⁻¹).map φ * S) := by
  have hs : ∀ Z : Matrix (Fin (n + 1)) (Fin (n + 1)) L, sgnM n * (sgnM n * Z) = Z := by
    intro Z; rw [← mul_assoc, sgnM_mul_self', one_mul]
  have hm : ∀ Z : Matrix (Fin (n + 1)) (Fin (n + 1)) L, (Mm⁻¹).map φ * (Mm.map φ * Z) = Z := by
    intro Z; rw [← mul_assoc, map_inv_mul φ hMm, one_mul]
  have hu : ∀ Z : Matrix (Fin (n + 1)) (Fin (n + 1)) L, U.map φ * ((U⁻¹).map φ * Z) = Z := by
    intro Z; rw [← mul_assoc, map_mul_inv φ hU, one_mul]
  have hS' : ∀ Z : Matrix (Fin (n + 1)) (Fin (n + 1)) L, S * (S⁻¹ * Z) = Z := by
    intro Z; rw [← mul_assoc, Matrix.mul_nonsing_inv S hS, one_mul]
  simp only [mul_assoc, hs, hm, hu, hS']

/- English proof (translation)
Rewrite using `[mul_sub, sub_mul, mul_one, Matrix.nonsing_inv_mul N hN, Matrix.sub_apply, Matrix.one_apply_ne hab, sub_zero]`.
-/
theorem conj_off {n : ℕ} {K : Type*} [Field K] {N Y : Matrix (Fin n) (Fin n) K} (hN : IsUnit N.det)
    {a b : Fin n} (hab : a ≠ b) : (N⁻¹ * Y * N) a b = (N⁻¹ * (Y - 1) * N) a b := by
  rw [mul_sub, sub_mul, mul_one, Matrix.nonsing_inv_mul N hN, Matrix.sub_apply, Matrix.one_apply_ne hab,
    sub_zero]

end Helpers

section Final

open Formalism.L2.SG.PackageTie2 in

/- English proof (translation)
Introduce `D X Y u u' t _ hGt w _ F' L U hN γw s s' _ _ hs' hdec`. Take `⟨hLu, hZu, hZ1⟩` from `nr_units hN`. Take `⟨hRep, -, hL, hU, -⟩` from `hN`. Establish `hT : ((Tu D u : ℕ) : D.host.E) ≠ 0` using `Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero`. Establish `hGv : Gval (lf D (X.Fu u)) F' ≠ 0`.

Establish `e` using `Formalism.L2.SG.Pf.PairValG.gval_eq_G (Y.rowsOK u) hRep`. Introduce `h0`. Conclude with `hGt (e.symm.trans h0)`. Establish `hGr : IsUnit (gramOf (gg (X.Fu u) F'.fl)).det` using `gram_gg_unit (X.Fu u) F'.fl (star_natCast _) (star_natCast _) hZu hGv`. Take `⟨h, hmk⟩` from `hRep`.

Take `⟨n0, hn0, m0, hm0, hfr, -⟩` from `(Formalism.L2.SG.Pf.double_coset_equivalence _ _ _ _ _).1 hmk.symm`. Take `⟨-, h2, h3, h4⟩` from `volume_dictionary_lu_decomposition Y t hL hU hZu hZ1 hGr hT hn0 hm0 hfr`. Use `⟨(rpt X n0 hn0.1.1).1, Phi X (X.Fu u) F'.fl hL hU hZu hZ1 hGr, h2, h3, h4, ?_⟩` and prove the remaining obligations. Establish `hγi : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT` using `t.rep.2.2.1`. Establish `hγΛ : Formalism.HermitianLatticesTheory.gmap t.lin t.lam' = t.lam` using `t.rep.2.2.2.1`.

Establish `hγx : RatLink X t.pt t.lin` using `t.rep.2.1`. Establish `hfe : t.frame = Formalism.L2.SG.Saturated.mapL t.lin hγi (lf D (X.Fu u'))` using `Formalism.L2.SG.Pf.FibreCounting.frame_eq t`. Use `set m0' := t.lin⁻¹ * m0 * t.lin with hm0'def`. Establish `hm0' : m0' ∈ NLam t.lam' (lf D (X.Fu u'))` using `(Formalism.L2.SG.Pf.mem_NLam_map t.lin hγi t.lam' (lf D (X.Fu u')) m0).1 (by rw [hγΛ, ← hfe]; exact hm0)`. Take `⟨Mm, hMmU, hMm⟩` from `tri_exists (X.Fu u') m0' hm0'.2.1 hm0'.2.2`.

Establish `hMmu : IsUnit Mm.det` using `by rw [up_det hMmU]; exact isUnit_one`. Use `set g := n0 * m0 * t.lin with hgdef`. Establish `hg : ∀ b, g ((X.Fu u').fvec b) = F'.fl.fvec b`. Introduce `b`. Establish `e1 : frame F' b = n0 (m0 (frame t.frame b))` using `hfr b`.

Establish `e2 : frame t.frame b = t.lin ((X.Fu u').fvec b)` using `Formalism.L2.SG.Pf.FibreCounting.frame_apply t b`. Use `show n0 (m0 (t.lin ((X.Fu u').fvec b))) = F'.fl.fvec b`. Rewrite using `[← e2]`. Conclude with `e1.symm`. Establish `hrd : (0 : ℝ) < D.host.rdE` using `(Formalism.BasicNotions.rdE_pos_le D).1`.

Establish `hrdc : (D.host.rdE : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 hrd.ne'`. Establish `hUu : IsUnit U.det` using `by rw [up_det hU]; exact isUnit_one`. Use `choose S hSU hS using fun v => inS_frame (hs' v)`. Establish `hSu : ∀ v, IsUnit (S v).det` using `fun v => by rw [up_det (hSU v)]; exact isUnit_one`. Use `set N : InfinitePlace X.B.I.F → Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ := fun v => sgnM D.R.rS * U.map (phiV X v) * sgnM D.R.rS * (Mm⁻¹).map (phiV X v) * S v with hN`.

Establish `hNU : ∀ v, IsUpUni (N v)` using `fun v => up_mul (up_mul (up_sgn (upUni_map (phiV X v) hU)) (upUni_map (phiV X v) (up_inv hMmU))) (hSU v)`. Establish `hNu : ∀ v, IsUnit (N v).det` using `fun v => by rw [up_det (hNU v)]; exact isUnit_one`. Use `⟨fun p => (D.host.rdE : ℂ) ^ (p.1.2.1 - p.1.1.1) * ((-1) ^ (D.R.rS - p.1.1.1) * (-1) ^ (D.R.rS - p.1.2.1)), fun p => ?_, fun v => Alin w (D.host.rdE : ℂ) (N v), fun v x x' p hxx => Alin_shear w _ (hNU v) hrdc x x' p hxx, fun β v => ?_⟩` and prove the remaining obligations. Rewrite using `[norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_pow, mul_one, mul_one, Complex.norm_real, Real.norm_of_nonneg hrd.le]`. Use function extensionality and compare the values at `p`.

Use `set τ := tw (X.Fu u) F'.fl L (hLu_of hL) hZu hGr ((β⁻¹ : StG w) : GLR D) with hτdef`. Use `set xβ := rpt X τ (tw_isom_st (X.Fu u) F'.fl hL hU hZu hZ1 hGr β⁻¹) with hxβ`. Use `set xn := rpt X n0 hn0.1.1 with hxn`. Use `set ρ := t.lin⁻¹ * (n0⁻¹ * τ * n0) * t.lin with hρ`. Use `set zz := t.pt⁻¹ * (xn⁻¹ * xβ * xn) * t.pt with hzz`.

Establish `hzzL : RatLink X zz ρ` using `Formalism.L2.SG.TermOp.Vanish.ratLink_mul X (Formalism.L2.SG.TermOp.Vanish.ratLink_mul X (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X hγx) (Formalism.L2.SG.TermOp.Vanish.ratLink_mul X (Formalism.L2.SG.TermOp.Vanish.ratLink_mul X (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X (rpt_s …`. Use `set P := P'm (X.Fu u) F'.fl L (((β⁻¹ : StG w) : GLR D) : MatR D) with hPdef`. Establish `hτF : FM F'.fl.fvec τ P` using `fun b => tw_frame' (hLu_of hL) hZu hGr _ b`. Establish `hK : FM (X.Fu u').fvec ρ (Mm * P * Mm⁻¹)`. Establish `e : ρ = m0' * (g⁻¹ * τ * g) * m0'⁻¹` using `by rw [hρ, hm0'def, hgdef]; group`.

Rewrite using `[e]`. Conclude with `K_FM τ g m0' hg hτF hMm hMmu`. Use `set Xβ : MatR D := (ptMat w)⁻¹ * ((β : GLR D) : MatR D) * ptMat w with hXβ`. Establish `hβS : (β : GLR D) ∈ StSet (ptMat w)` using `β.2`. Take `⟨hXup, hXrel⟩` from `conjW_up hβS`.

Establish `hPeq : P = sgnM D.R.rS * (U⁻¹ * Xβ * U) * sgnM D.R.rS`. Establish `hBu : IsUnit ((((β⁻¹ : StG w) : GLR D) : MatR D)).det` using `Matrix.isUnits_det_units _`. Use `P'm_eq hL hU hZu hZ1 hBu ?_` and prove the remaining obligations. Establish `e : (((β⁻¹ : StG w) : GLR D) : MatR D) = ((β : GLR D) : MatR D)⁻¹`. Rewrite using `[Subgroup.coe_inv, Matrix.coe_units_inv]`.

Rewrite using `[e]`. Conclude with `hXrel`. Establish `hgrp : γw⁻¹ * (s⁻¹ * ((rpt X n0 hn0.1.1).1⁻¹ * Phi X (X.Fu u) F'.fl hL hU hZu hZ1 hGr β * (rpt X n0 hn0.1.1).1) * s) * γw = s'⁻¹ * zz.1 * s'`. Establish `e1 : zz.1 = t.pt.1⁻¹ * (xn.1⁻¹ * xβ.1 * xn.1) * t.pt.1`. Simplify using `only [hzz, Prod.fst_mul, Prod.fst_inv]`.

Establish `e2 : γw = s⁻¹ * t.pt.1 * s'` using `by rw [hdec]; group`. Rewrite using `[e1, e2]`. Use `show (s⁻¹ * t.pt.1 * s')⁻¹ * (s⁻¹ * (xn.1⁻¹ * xβ.1 * xn.1) * s) * (s⁻¹ * t.pt.1 * s') = _`. Use `group`. Establish `hmi : ∀ a : Formalism.REAL.UJ (X.B.I.ε v), Formalism.MainNotions.S.uMat a * Formalism.MainNotions.S.uMat a⁻¹ = 1`.

Introduce `a`. Use `show _ * (((a⁻¹ : Formalism.REAL.UJ (X.B.I.ε v)) : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) = 1`. Rewrite using `[Subgroup.coe_inv, Units.mul_inv]`. Establish `hu : Formalism.MainNotions.S.uMat ((s'⁻¹ * zz.1 * s') v) = (Formalism.MainNotions.S.uMat (s' v))⁻¹ * Formalism.MainNotions.S.uMat (zz.1 v) * Formalism.MainNotions.S.uMat (s' v)`. Establish `hi : Formalism.MainNotions.S.uMat ((s' v)⁻¹) = (Formalism.MainNotions.S.uMat (s' v))⁻¹` using `(Matrix.inv_eq_right_inv (hmi (s' v))).symm`.

Use `show Formalism.MainNotions.S.uMat ((s' v)⁻¹ * zz.1 v * s' v) = _`. Use `show Formalism.MainNotions.S.uMat ((s' v)⁻¹) * Formalism.MainNotions.S.uMat (zz.1 v) * Formalism.MainNotions.S.uMat (s' v) = _`. Rewrite using `[hi]`. Establish `hs'u : IsUnit (Formalism.MainNotions.S.uMat (s' v)).det`. Use `congrArg Matrix.det (hmi (s' v))` as an intermediate fact.

Rewrite `this` using `[Matrix.det_mul, Matrix.det_one]`. Conclude with `isUnit_iff_ne_zero.2 (left_ne_zero_of_mul_eq_one this)`. Establish `hFM : FM (efr X u' v) (fun y => ((Formalism.MainNotions.S.uMat (s' v))⁻¹ * Formalism.MainNotions.S.uMat (zz.1 v) * Formalism.MainNotions.S.uMat (s' v)) *ᵥ y) ((S v)⁻¹ * (Mm * P * Mm⁻¹).map (phiV X v) * S v)` using `FMm_mul (FMm_mul (FMm_inv hs'u (hS v) (hSu v)) (realFM X hzzL hK v)) (hS v)`. Establish `hG : (S v)⁻¹ * (Mm * P * Mm⁻¹).map (phiV X v) * S v = (N v)⁻¹ * (sgnM D.R.rS * Xβ.map (phiV X v) * sgnM D.R.rS) * N v`. Establish `hk` using `conj_key (phiV X v) (hSu v) hMmu hUu (X := Xβ)`.

Establish `e : (Mm * P * Mm⁻¹).map (phiV X v) = Mm.map (phiV X v) * (sgnM D.R.rS * ((U⁻¹).map (phiV X v) * Xβ.map (phiV X v) * U.map (phiV X v)) * sgnM D.R.rS) * (Mm⁻¹).map (phiV X v)`. Rewrite using `[hPeq]`. Simplify using `only [Matrix.map_mul, sgnM_map]`. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hY : Yhat w (D.host.rdE : ℂ) (fun q => (D.host.rdE : ℂ) ^ (q.1.2.1 - q.1.1.1) * ((-1) ^ (D.R.rS - q.1.1.1) * (-1) ^ (D.R.rS - q.1.2.1)) * phiV X v (Xβ q.1.1 q.1.2)) = sgnM D.R.rS * Xβ.map (phiV X v) * sgnM D.R.rS - 1`. Simplify using `only [hXβ]`. Use extensionality with `c d`. Rewrite using `[Matrix.sub_apply, sgn_conj_apply, Matrix.map_apply]`. Simplify using `only [Yhat]`.

Use `split_ifs with hcd`. Rewrite using `[Matrix.one_apply_ne (ne_of_lt hcd.1), sub_zero]`. Clear the denominators using the available nonvanishing facts. Distinguish the cases in `hlt : c < d`. Establish `hb : Formalism.L2.SG.RealObj.blkOf w.1 c.1 ≠ Formalism.L2.SG.RealObj.blkOf w.1 d.1` using `fun he => hcd ⟨hlt, he⟩`.

Rewrite using `[conjW_blk hβS c d hlt hb, map_zero, mul_zero, zero_mul, Matrix.one_apply_ne (ne_of_lt hlt), sub_zero]`. Break down `lt_or_eq_of_le (not_lt.1 hlt) with hgt | heq` into its components or cases. Rewrite using `[(hXup c d).1 hgt, map_zero, mul_zero, zero_mul, Matrix.one_apply_ne (ne_of_gt hgt), sub_zero]`. Rewrite using `[heq, (hXup c c).2 rfl, map_one, mul_one, Matrix.one_apply_eq, ← pow_add, ← two_mul, pow_mul]`. Simplify using the standard rewrite rules.

Establish `hab : p.1.1 < p.1.2` using `p.2.1`. Establish `har : p.1.1.1 < D.R.rS` using `lt_of_lt_of_le hab (Nat.lt_succ_iff.1 p.1.2.2)`. Use `show Formalism.L2.SG.RealObj.stCoord X u' w γw _ v p = Alin w (D.host.rdE : ℂ) (N v) _ p`. Unfold `Formalism.L2.SG.RealObj.stCoord`. Rewrite using `[hgrp, hu, Alin_apply, hY]`.

Establish `hfrm : Formalism.L2.SG.RealObj.frm X u' D.host.rdE v p.1.2 = (((D.host.rdE : ℂ)) ^ (D.R.rS - p.1.2.1))⁻¹ • efr X u' v p.1.2` using `rfl`. Rewrite using `[hfrm, coef_efr X u' v hFM ⟨p.1.1.1, har⟩ p.1.2, hG]`. Establish `hcs : (Fin.castSucc (⟨p.1.1.1, har⟩ : Fin D.R.rS)) = p.1.1` using `Fin.ext rfl`. Rewrite using `[hcs, conj_off (hNu v) (ne_of_lt hab)]`. Establish `hpow : (D.host.rdE : ℂ) ^ (D.R.rS - p.1.1.1) = (D.host.rdE : ℂ) ^ (D.R.rS - p.1.2.1) * (D.host.rdE : ℂ) ^ (p.1.2.1 - p.1.1.1)`.

Rewrite using `[← pow_add]`. Use `congr 1`. Establish `: (p.1.2 : ℕ) ≤ D.R.rS` using `Nat.lt_succ_iff.1 p.1.2.2`. Establish `: (p.1.1 : ℕ) < p.1.2` using `hab`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hpow]`. Clear the denominators using the available nonvanishing facts.
-/
theorem dictC_holds : DictC := by
  intro D X Y u u' t _ hGt w _ F' L U hN γw s s' _ _ hs' hdec
  obtain ⟨hLu, hZu, hZ1⟩ := nr_units hN
  obtain ⟨hRep, -, hL, hU, -⟩ := hN
  have hT : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero
  have hGv : Gval (lf D (X.Fu u)) F' ≠ 0 := by
    have e := Formalism.L2.SG.Pf.PairValG.gval_eq_G (Y.rowsOK u) hRep
    intro h0; exact hGt (e.symm.trans h0)
  have hGr : IsUnit (gramOf (gg (X.Fu u) F'.fl)).det :=
    gram_gg_unit (X.Fu u) F'.fl (star_natCast _) (star_natCast _) hZu hGv
  obtain ⟨h, hmk⟩ := hRep
  obtain ⟨n0, hn0, m0, hm0, hfr, -⟩ := (Formalism.L2.SG.Pf.double_coset_equivalence _ _ _ _ _).1 hmk.symm
  obtain ⟨-, h2, h3, h4⟩ := volume_dictionary_lu_decomposition Y t hL hU hZu hZ1 hGr hT hn0 hm0 hfr
  refine ⟨(rpt X n0 hn0.1.1).1, Phi X (X.Fu u) F'.fl hL hU hZu hZ1 hGr, h2, h3, h4, ?_⟩

  have hγi : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hγΛ : Formalism.HermitianLatticesTheory.gmap t.lin t.lam' = t.lam := t.rep.2.2.2.1
  have hγx : RatLink X t.pt t.lin := t.rep.2.1
  have hfe : t.frame = Formalism.L2.SG.Saturated.mapL t.lin hγi (lf D (X.Fu u')) := Formalism.L2.SG.Pf.FibreCounting.frame_eq t
  set m0' := t.lin⁻¹ * m0 * t.lin with hm0'def
  have hm0' : m0' ∈ NLam t.lam' (lf D (X.Fu u')) :=
    (Formalism.L2.SG.Pf.mem_NLam_map t.lin hγi t.lam' (lf D (X.Fu u')) m0).1 (by rw [hγΛ, ← hfe]; exact hm0)
  obtain ⟨Mm, hMmU, hMm⟩ := tri_exists (X.Fu u') m0' hm0'.2.1 hm0'.2.2
  have hMmu : IsUnit Mm.det := by rw [up_det hMmU]; exact isUnit_one
  set g := n0 * m0 * t.lin with hgdef
  have hg : ∀ b, g ((X.Fu u').fvec b) = F'.fl.fvec b := by
    intro b
    have e1 : frame F' b = n0 (m0 (frame t.frame b)) := hfr b
    have e2 : frame t.frame b = t.lin ((X.Fu u').fvec b) := Formalism.L2.SG.Pf.FibreCounting.frame_apply t b
    show n0 (m0 (t.lin ((X.Fu u').fvec b))) = F'.fl.fvec b
    rw [← e2]; exact e1.symm
  have hrd : (0 : ℝ) < D.host.rdE := (Formalism.BasicNotions.rdE_pos_le D).1
  have hrdc : (D.host.rdE : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hrd.ne'
  have hUu : IsUnit U.det := by rw [up_det hU]; exact isUnit_one

  choose S hSU hS using fun v => inS_frame (hs' v)
  have hSu : ∀ v, IsUnit (S v).det := fun v => by rw [up_det (hSU v)]; exact isUnit_one
  set N : InfinitePlace X.B.I.F → Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ := fun v =>
    sgnM D.R.rS * U.map (phiV X v) * sgnM D.R.rS * (Mm⁻¹).map (phiV X v) * S v with hN
  have hNU : ∀ v, IsUpUni (N v) := fun v =>
    up_mul (up_mul (up_sgn (upUni_map (phiV X v) hU)) (upUni_map (phiV X v) (up_inv hMmU))) (hSU v)
  have hNu : ∀ v, IsUnit (N v).det := fun v => by rw [up_det (hNU v)]; exact isUnit_one
  refine ⟨fun p => (D.host.rdE : ℂ) ^ (p.1.2.1 - p.1.1.1) *
      ((-1) ^ (D.R.rS - p.1.1.1) * (-1) ^ (D.R.rS - p.1.2.1)), fun p => ?_,
    fun v => Alin w (D.host.rdE : ℂ) (N v), fun v x x' p hxx => Alin_shear w _ (hNU v) hrdc x x' p hxx,
    fun β v => ?_⟩
  · rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_pow, mul_one,
      mul_one, Complex.norm_real, Real.norm_of_nonneg hrd.le]
  funext p

  set τ := tw (X.Fu u) F'.fl L (hLu_of hL) hZu hGr ((β⁻¹ : StG w) : GLR D) with hτdef
  set xβ := rpt X τ (tw_isom_st (X.Fu u) F'.fl hL hU hZu hZ1 hGr β⁻¹) with hxβ
  set xn := rpt X n0 hn0.1.1 with hxn
  set ρ := t.lin⁻¹ * (n0⁻¹ * τ * n0) * t.lin with hρ
  set zz := t.pt⁻¹ * (xn⁻¹ * xβ * xn) * t.pt with hzz
  have hzzL : RatLink X zz ρ :=
    Formalism.L2.SG.TermOp.Vanish.ratLink_mul X (Formalism.L2.SG.TermOp.Vanish.ratLink_mul X
      (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X hγx) (Formalism.L2.SG.TermOp.Vanish.ratLink_mul X
        (Formalism.L2.SG.TermOp.Vanish.ratLink_mul X (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X (rpt_spec X _ _))
          (rpt_spec X _ _)) (rpt_spec X _ _))) hγx
  set P := P'm (X.Fu u) F'.fl L (((β⁻¹ : StG w) : GLR D) : MatR D) with hPdef
  have hτF : FM F'.fl.fvec τ P := fun b => tw_frame' (hLu_of hL) hZu hGr _ b
  have hK : FM (X.Fu u').fvec ρ (Mm * P * Mm⁻¹) := by
    have e : ρ = m0' * (g⁻¹ * τ * g) * m0'⁻¹ := by rw [hρ, hm0'def, hgdef]; group
    rw [e]; exact K_FM τ g m0' hg hτF hMm hMmu
  set Xβ : MatR D := (ptMat w)⁻¹ * ((β : GLR D) : MatR D) * ptMat w with hXβ
  have hβS : (β : GLR D) ∈ StSet (ptMat w) := β.2
  obtain ⟨hXup, hXrel⟩ := conjW_up hβS
  have hPeq : P = sgnM D.R.rS * (U⁻¹ * Xβ * U) * sgnM D.R.rS := by
    have hBu : IsUnit ((((β⁻¹ : StG w) : GLR D) : MatR D)).det := Matrix.isUnits_det_units _
    refine P'm_eq hL hU hZu hZ1 hBu ?_
    have e : (((β⁻¹ : StG w) : GLR D) : MatR D) = ((β : GLR D) : MatR D)⁻¹ := by
      rw [Subgroup.coe_inv, Matrix.coe_units_inv]
    rw [e]; exact hXrel

  have hgrp : γw⁻¹ * (s⁻¹ * ((rpt X n0 hn0.1.1).1⁻¹ * Phi X (X.Fu u) F'.fl hL hU hZu hZ1 hGr β *
      (rpt X n0 hn0.1.1).1) * s) * γw = s'⁻¹ * zz.1 * s' := by
    have e1 : zz.1 = t.pt.1⁻¹ * (xn.1⁻¹ * xβ.1 * xn.1) * t.pt.1 := by
      simp only [hzz, Prod.fst_mul, Prod.fst_inv]
    have e2 : γw = s⁻¹ * t.pt.1 * s' := by rw [hdec]; group
    rw [e1, e2]
    show (s⁻¹ * t.pt.1 * s')⁻¹ * (s⁻¹ * (xn.1⁻¹ * xβ.1 * xn.1) * s) * (s⁻¹ * t.pt.1 * s') = _
    group
  have hmi : ∀ a : Formalism.REAL.UJ (X.B.I.ε v), Formalism.MainNotions.S.uMat a * Formalism.MainNotions.S.uMat a⁻¹ = 1 := by
    intro a
    show _ * (((a⁻¹ : Formalism.REAL.UJ (X.B.I.ε v)) : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) = 1
    rw [Subgroup.coe_inv, Units.mul_inv]
  have hu : Formalism.MainNotions.S.uMat ((s'⁻¹ * zz.1 * s') v) =
      (Formalism.MainNotions.S.uMat (s' v))⁻¹ * Formalism.MainNotions.S.uMat (zz.1 v) * Formalism.MainNotions.S.uMat (s' v) := by
    have hi : Formalism.MainNotions.S.uMat ((s' v)⁻¹) = (Formalism.MainNotions.S.uMat (s' v))⁻¹ :=
      (Matrix.inv_eq_right_inv (hmi (s' v))).symm
    show Formalism.MainNotions.S.uMat ((s' v)⁻¹ * zz.1 v * s' v) = _
    show Formalism.MainNotions.S.uMat ((s' v)⁻¹) * Formalism.MainNotions.S.uMat (zz.1 v) * Formalism.MainNotions.S.uMat (s' v) = _
    rw [hi]
  have hs'u : IsUnit (Formalism.MainNotions.S.uMat (s' v)).det := by
    have := congrArg Matrix.det (hmi (s' v))
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact isUnit_iff_ne_zero.2 (left_ne_zero_of_mul_eq_one this)
  have hFM : FM (efr X u' v) (fun y => ((Formalism.MainNotions.S.uMat (s' v))⁻¹ * Formalism.MainNotions.S.uMat (zz.1 v) *
      Formalism.MainNotions.S.uMat (s' v)) *ᵥ y) ((S v)⁻¹ * (Mm * P * Mm⁻¹).map (phiV X v) * S v) :=
    FMm_mul (FMm_mul (FMm_inv hs'u (hS v) (hSu v)) (realFM X hzzL hK v)) (hS v)

  have hG : (S v)⁻¹ * (Mm * P * Mm⁻¹).map (phiV X v) * S v =
      (N v)⁻¹ * (sgnM D.R.rS * Xβ.map (phiV X v) * sgnM D.R.rS) * N v := by
    have hk := conj_key (phiV X v) (hSu v) hMmu hUu (X := Xβ)
    have e : (Mm * P * Mm⁻¹).map (phiV X v) = Mm.map (phiV X v) * (sgnM D.R.rS * ((U⁻¹).map (phiV X v) *
        Xβ.map (phiV X v) * U.map (phiV X v)) * sgnM D.R.rS) * (Mm⁻¹).map (phiV X v) := by
      rw [hPeq]; simp only [Matrix.map_mul, sgnM_map]
    rw [e]
    calc (S v)⁻¹ * (Mm.map (phiV X v) * (sgnM D.R.rS * ((U⁻¹).map (phiV X v) * Xβ.map (phiV X v) *
          U.map (phiV X v)) * sgnM D.R.rS) * (Mm⁻¹).map (phiV X v)) * S v
        = (N v)⁻¹ * ((N v) * ((S v)⁻¹ * (Mm.map (phiV X v) * (sgnM D.R.rS * ((U⁻¹).map (phiV X v) *
          Xβ.map (phiV X v) * U.map (phiV X v)) * sgnM D.R.rS) * (Mm⁻¹).map (phiV X v)) * S v)) :=
          (Matrix.nonsing_inv_mul_cancel_left _ _ (hNu v)).symm
      _ = _ := by rw [show N v = _ from rfl, hk]; simp only [hN, Matrix.mul_assoc]

  have hY : Yhat w (D.host.rdE : ℂ) (fun q => (D.host.rdE : ℂ) ^ (q.1.2.1 - q.1.1.1) *
      ((-1) ^ (D.R.rS - q.1.1.1) * (-1) ^ (D.R.rS - q.1.2.1)) * phiV X v (Xβ q.1.1 q.1.2)) =
      sgnM D.R.rS * Xβ.map (phiV X v) * sgnM D.R.rS - 1 := by
    simp only [hXβ]
    ext c d
    rw [Matrix.sub_apply, sgn_conj_apply, Matrix.map_apply]
    simp only [Yhat]
    split_ifs with hcd
    · rw [Matrix.one_apply_ne (ne_of_lt hcd.1), sub_zero]
      field_simp
    · by_cases hlt : c < d
      · have hb : Formalism.L2.SG.RealObj.blkOf w.1 c.1 ≠ Formalism.L2.SG.RealObj.blkOf w.1 d.1 := fun he => hcd ⟨hlt, he⟩
        rw [conjW_blk hβS c d hlt hb, map_zero, mul_zero, zero_mul, Matrix.one_apply_ne (ne_of_lt hlt), sub_zero]
      · rcases lt_or_eq_of_le (not_lt.1 hlt) with hgt | heq
        · rw [(hXup c d).1 hgt, map_zero, mul_zero, zero_mul, Matrix.one_apply_ne (ne_of_gt hgt), sub_zero]
        · rw [heq, (hXup c c).2 rfl, map_one, mul_one, Matrix.one_apply_eq, ← pow_add, ← two_mul, pow_mul]
          simp

  have hab : p.1.1 < p.1.2 := p.2.1
  have har : p.1.1.1 < D.R.rS := lt_of_lt_of_le hab (Nat.lt_succ_iff.1 p.1.2.2)
  show Formalism.L2.SG.RealObj.stCoord X u' w γw _ v p = Alin w (D.host.rdE : ℂ) (N v) _ p
  unfold Formalism.L2.SG.RealObj.stCoord
  rw [hgrp, hu, Alin_apply, hY]
  have hfrm : Formalism.L2.SG.RealObj.frm X u' D.host.rdE v p.1.2 =
      (((D.host.rdE : ℂ)) ^ (D.R.rS - p.1.2.1))⁻¹ • efr X u' v p.1.2 := rfl
  rw [hfrm, coef_efr X u' v hFM ⟨p.1.1.1, har⟩ p.1.2, hG]
  have hcs : (Fin.castSucc (⟨p.1.1.1, har⟩ : Fin D.R.rS)) = p.1.1 := Fin.ext rfl
  rw [hcs, conj_off (hNu v) (ne_of_lt hab)]
  have hpow : (D.host.rdE : ℂ) ^ (D.R.rS - p.1.1.1) =
      (D.host.rdE : ℂ) ^ (D.R.rS - p.1.2.1) * (D.host.rdE : ℂ) ^ (p.1.2.1 - p.1.1.1) := by
    rw [← pow_add]; congr 1
    have : (p.1.2 : ℕ) ≤ D.R.rS := Nat.lt_succ_iff.1 p.1.2.2
    have : (p.1.1 : ℕ) < p.1.2 := hab
    omega
  rw [hpow]
  field_simp

end Final

end Formalism.L2.SG.Pf.VolPinAsm
