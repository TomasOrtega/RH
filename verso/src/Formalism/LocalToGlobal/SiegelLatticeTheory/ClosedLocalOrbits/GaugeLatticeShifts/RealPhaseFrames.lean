import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PointMatrixPhases
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.FormRegularity

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open scoped ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.RealPhaseFrames

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.HermitianBlockSpans Formalism.L2.SG.RealObj.RootCoordinateFrames Formalism.L2.SG.Pf.PointMatrixPhases

section Frame

variable {n r : ℕ} (ε : Fin n → Bool)

/- English proof (translation)
Unfold `hJ`. Rewrite using `[Matrix.mulVec_add, dotProduct_add]`.
-/
theorem hJ_add_r (x y y' : Fin n → ℂ) : hJ ε x (y + y') = hJ ε x y + hJ ε x y' := by
  unfold hJ; rw [Matrix.mulVec_add, dotProduct_add]

/- English proof (translation)
Unfold `hJ`. Rewrite using `[Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]`.
-/
theorem hJ_smul_r (c : ℂ) (x y : Fin n → ℂ) : hJ ε x (c • y) = c * hJ ε x y := by
  unfold hJ; rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

/- English proof (translation)
Unfold `spanLt at hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨b0, hb0, rfl⟩` from `hx`. Use `⟨fun b hb => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hfe, if_neg]`. Introduce `h; subst h; exact absurd hb0 (by simp only [Set.mem_setOf_eq]; omega)`. Simplify using `only [hfe, ite_smul, one_smul, zero_smul]`. Simplify using the standard rewrite rules. Consider the case `zero => refine ⟨fun b _ => ?_, ?_⟩ <;> simp [hJ]`.

Consider the case `add a c _ _ ha hc`. Use `⟨fun b hb => by rw [hJ_add_r, ha.1 b hb, hc.1 b hb, add_zero], ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [ha.2, hc.2]`. Simplify using `only [hJ_add_r, add_smul, Finset.sum_add_distrib]`. Consider the case `smul t a _ ha`.

Use `⟨fun b hb => by rw [hJ_smul_r, ha.1 b hb, mul_zero], ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [ha.2]`. Simplify using `only [hJ_smul_r, Finset.smul_sum, smul_smul]`.
-/
theorem expand_e (e fd : Fin r → Fin n → ℂ) (hfe : ∀ a b, hJ ε (fd a) (e b) = if a = b then 1 else 0) {k : ℕ}
    {y : Fin n → ℂ} (hy : y ∈ spanLt e k) :
    (∀ b : Fin r, k ≤ b.1 → hJ ε (fd b) y = 0) ∧ y = ∑ b, hJ ε (fd b) y • e b := by
  unfold spanLt at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b0, hb0, rfl⟩ := hx
    refine ⟨fun b hb => ?_, ?_⟩
    · rw [hfe, if_neg]
      intro h; subst h; exact absurd hb0 (by simp only [Set.mem_setOf_eq]; omega)
    · simp only [hfe, ite_smul, one_smul, zero_smul]
      simp
  | zero => refine ⟨fun b _ => ?_, ?_⟩ <;> simp [hJ]
  | add a c _ _ ha hc =>
    refine ⟨fun b hb => by rw [hJ_add_r, ha.1 b hb, hc.1 b hb, add_zero], ?_⟩
    conv_lhs => rw [ha.2, hc.2]
    simp only [hJ_add_r, add_smul, Finset.sum_add_distrib]
  | smul t a _ ha =>
    refine ⟨fun b hb => by rw [hJ_smul_r, ha.1 b hb, mul_zero], ?_⟩
    conv_lhs => rw [ha.2]
    simp only [hJ_smul_r, Finset.smul_sum, smul_smul]

def frameMat (e fd : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  fun a c => Fin.lastCases (if a = Fin.last r then 1 else 0)
    (fun b => (if a = b.castSucc then 1 else 0) + hJ ε (fd b) ((g - 1) *ᵥ fam e z a)) c

/- English proof (translation)
Establish `hsp_cs : ∀ b : Fin r, (g - 1) *ᵥ fam e z b.castSucc ∈ spanLt e b.1` using `fun b => by`. Simplify using `only [fam, Fin.snoc_castSucc]`. Conclude with `hg.1 b`. Establish `hsp_l : (g - 1) *ᵥ fam e z (Fin.last r) ∈ spanLt e r`. Simplify using `only [fam, Fin.snoc_last]`.

Conclude with `hg.2`. Use `⟨?_, fun a => ?_⟩` and prove the remaining obligations. Introduce `i j`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last`.

Use `⟨fun hij => ?_, fun hij => ?_⟩` and prove the remaining obligations. Simplify using `only [frameMat, Fin.lastCases_last]`. Rewrite using `[if_neg (ne_of_lt hij)]`. Substitute `hij` using the available equality. Simplify using `[frameMat]`.

Consider the case `cast b`. Use `⟨fun hij => ?_, fun hij => ?_⟩` and prove the remaining obligations. Simplify using `only [frameMat, Fin.lastCases_castSucc]`. Rewrite using `[if_neg (ne_of_lt hij)]`. Establish `hi : i ≠ Fin.last r` using `fun h => by`.

Rewrite `hij` using `[h]`. Conclude with `absurd hij (not_lt.2 (Fin.le_last _))`. Take `⟨a', rfl⟩` from `Fin.exists_castSucc_eq.2 hi`. Establish `hlt : a'.1 < b.1` using `Fin.castSucc_lt_castSucc_iff.1 hij`. Rewrite using `[(expand_e ε e fd hfe (hsp_cs a')).1 b (le_of_lt hlt), add_zero]`.

Substitute `hij` using the available equality. Simplify using `only [frameMat, Fin.lastCases_castSucc]`. Rewrite using `[(expand_e ε e fd hfe (hsp_cs b)).1 b le_rfl, add_zero]`. Simplify using the standard rewrite rules. Establish `e0 : g *ᵥ fam e z a = fam e z a + (g - 1) *ᵥ fam e z a`.

Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec]`. Normalize the expressions using the abelian group laws. Rewrite using `[e0, Fin.sum_univ_castSucc]`. Simplify using `only [frameMat, Fin.lastCases_castSucc, Fin.lastCases_last, add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul]`. Proceed by induction on `a using Fin.lastCases with`.

Consider the case `last`. Establish `hx` using `(expand_e ε e fd hfe hsp_l).2`. Simplify using `only [fam, Fin.snoc_castSucc, Fin.snoc_last, if_pos rfl] at hx ⊢`. Establish `h0 : ∀ b : Fin r, (if Fin.last r = b.castSucc then e b else 0) = 0` using `fun b => by`. Rewrite using `[if_neg (Fin.castSucc_lt_last b).ne']`.

Simplify using `only [h0, Finset.sum_const_zero, zero_add]`. Rewrite using `[← hx]`. Simplify using `[add_comm]`. Consider the case `cast b0`. Establish `hx` using `(expand_e ε e fd hfe (hsp_cs b0)).2`.

Simplify using `only [fam, Fin.snoc_castSucc, Fin.snoc_last] at hx ⊢`. Rewrite using `[if_neg (Fin.castSucc_lt_last b0).ne, add_zero]`. Establish `h0 : ∑ b : Fin r, (if b0.castSucc = b.castSucc then e b else 0) = e b0`. Simplify using `[Fin.castSucc_inj]`. Rewrite using `[h0, ← hx]`.
-/
theorem frameMat_spec (e fd : Fin r → Fin n → ℂ) (z : Fin n → ℂ)
    (hfe : ∀ a b, hJ ε (fd a) (e b) = if a = b then 1 else 0) (g : Matrix (Fin n) (Fin n) ℂ) (hg : InS e z g) :
    IsLoUni (frameMat ε e fd z g) ∧ ∀ a, g *ᵥ fam e z a = ∑ c, frameMat ε e fd z g a c • fam e z c := by
  have hsp_cs : ∀ b : Fin r, (g - 1) *ᵥ fam e z b.castSucc ∈ spanLt e b.1 := fun b => by
    simp only [fam, Fin.snoc_castSucc]; exact hg.1 b
  have hsp_l : (g - 1) *ᵥ fam e z (Fin.last r) ∈ spanLt e r := by
    simp only [fam, Fin.snoc_last]; exact hg.2
  refine ⟨?_, fun a => ?_⟩
  · intro i j
    induction j using Fin.lastCases with
    | last =>
      refine ⟨fun hij => ?_, fun hij => ?_⟩
      · simp only [frameMat, Fin.lastCases_last]
        rw [if_neg (ne_of_lt hij)]
      · subst hij
        simp [frameMat]
    | cast b =>
      refine ⟨fun hij => ?_, fun hij => ?_⟩
      · simp only [frameMat, Fin.lastCases_castSucc]
        rw [if_neg (ne_of_lt hij)]
        have hi : i ≠ Fin.last r := fun h => by
          rw [h] at hij; exact absurd hij (not_lt.2 (Fin.le_last _))
        obtain ⟨a', rfl⟩ := Fin.exists_castSucc_eq.2 hi
        have hlt : a'.1 < b.1 := Fin.castSucc_lt_castSucc_iff.1 hij
        rw [(expand_e ε e fd hfe (hsp_cs a')).1 b (le_of_lt hlt), add_zero]
      · subst hij
        simp only [frameMat, Fin.lastCases_castSucc]
        rw [(expand_e ε e fd hfe (hsp_cs b)).1 b le_rfl, add_zero]
        simp
  · have e0 : g *ᵥ fam e z a = fam e z a + (g - 1) *ᵥ fam e z a := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [e0, Fin.sum_univ_castSucc]
    simp only [frameMat, Fin.lastCases_castSucc, Fin.lastCases_last, add_smul, Finset.sum_add_distrib, ite_smul,
      one_smul, zero_smul]
    induction a using Fin.lastCases with
    | last =>
      have hx := (expand_e ε e fd hfe hsp_l).2
      simp only [fam, Fin.snoc_castSucc, Fin.snoc_last, if_pos rfl] at hx ⊢
      have h0 : ∀ b : Fin r, (if Fin.last r = b.castSucc then e b else 0) = 0 := fun b => by
        rw [if_neg (Fin.castSucc_lt_last b).ne']
      simp only [h0, Finset.sum_const_zero, zero_add]
      rw [← hx]
      simp [add_comm]
    | cast b0 =>
      have hx := (expand_e ε e fd hfe (hsp_cs b0)).2
      simp only [fam, Fin.snoc_castSucc, Fin.snoc_last] at hx ⊢
      rw [if_neg (Fin.castSucc_lt_last b0).ne, add_zero]
      have h0 : ∑ b : Fin r, (if b0.castSucc = b.castSucc then e b else 0) = e b0 := by
        simp [Fin.castSucc_inj]
      rw [h0, ← hx]

end Frame

section Sums

variable {r : ℕ}

/- English proof (translation)
Unfold `sgLoF`. Rewrite using `[Fin.sum_univ_castSucc, dif_neg (by simp), add_zero]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[dif_pos (by simp)]`. Both sides reduce to the same expression.
-/
theorem sgLoF_eq {K : Type} [Field K] (M : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    sgLoF M = ∑ a : Fin r, M a.succ a.castSucc := by
  unfold sgLoF
  rw [Fin.sum_univ_castSucc, dif_neg (by simp), add_zero]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [dif_pos (by simp)]
  rfl

/- English proof (translation)
Unfold `sgUpF`. Rewrite using `[Fin.sum_univ_castSucc, dif_neg (by simp), add_zero]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[dif_pos (by simp)]`. Both sides reduce to the same expression.
-/
theorem sgUpF_eq {K : Type} [Field K] (M : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    sgUpF M = ∑ a : Fin r, M a.castSucc a.succ := by
  unfold sgUpF
  rw [Fin.sum_univ_castSucc, dif_neg (by simp), add_zero]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [dif_pos (by simp)]
  rfl

/- English proof (translation)
Unfold `sgLoF`. Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Conclude with `Matrix.one_apply_ne (fun e => by have := congrArg Fin.val e; simp at this)`. Both sides reduce to the same expression.
-/
theorem sgLoF_one {K : Type} [Field K] {N : ℕ} : sgLoF (1 : Matrix (Fin N) (Fin N) K) = 0 := by
  unfold sgLoF
  refine Finset.sum_eq_zero fun a _ => ?_
  split_ifs with h
  · exact Matrix.one_apply_ne (fun e => by have := congrArg Fin.val e; simp at this)
  · rfl

/- English proof (translation)
Unfold `sgUpF`. Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Conclude with `Matrix.one_apply_ne (fun e => by have := congrArg Fin.val e; simp at this)`. Both sides reduce to the same expression.
-/
theorem sgUpF_one {K : Type} [Field K] {N : ℕ} : sgUpF (1 : Matrix (Fin N) (Fin N) K) = 0 := by
  unfold sgUpF
  refine Finset.sum_eq_zero fun a _ => ?_
  split_ifs with h
  · exact Matrix.one_apply_ne (fun e => by have := congrArg Fin.val e; simp at this)
  · rfl

/- English proof (translation)
Introduce `i j` and use `⟨fun h => Matrix.one_apply_ne (ne_of_lt h), fun h => by subst h; exact Matrix.one_apply_eq i⟩`.
-/
theorem isLoUni_one {K : Type} [Field K] {N : ℕ} : IsLoUni (1 : Matrix (Fin N) (Fin N) K) := fun i j =>
  ⟨fun h => Matrix.one_apply_ne (ne_of_lt h), fun h => by subst h; exact Matrix.one_apply_eq i⟩

/- English proof (translation)
Introduce `i j` and use `⟨fun h => Matrix.one_apply_ne (ne_of_lt h).symm, fun h => by subst h; exact Matrix.one_apply_eq i⟩`.
-/
theorem isUpUni_one {K : Type} [Field K] {N : ℕ} : IsUpUni (1 : Matrix (Fin N) (Fin N) K) := fun i j =>
  ⟨fun h => Matrix.one_apply_ne (ne_of_lt h).symm, fun h => by subst h; exact Matrix.one_apply_eq i⟩

/- English proof (translation)
Introduce `i j`. Simplify using `only [FormRegularity.sgn, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply]`. Use `⟨fun hij => ?_, fun hij => ?_⟩` and prove the remaining obligations. Rewrite using `[(h j i).1 hij]`. Expand and normalize the polynomial expressions, which then agree.

Substitute `hij` using the available equality. Rewrite using `[(h i i).2 rfl, mul_one, ← pow_add, ← two_mul, pow_mul]`. Simplify using the standard rewrite rules.
-/
theorem isUpUni_sgnT {P : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (h : IsLoUni P) :
    IsUpUni (FormRegularity.sgn r * Pᵀ * FormRegularity.sgn r) := by
  intro i j
  simp only [FormRegularity.sgn, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply]
  refine ⟨fun hij => ?_, fun hij => ?_⟩
  · rw [(h j i).1 hij]; ring
  · subst hij
    rw [(h i i).2 rfl, mul_one, ← pow_add, ← two_mul, pow_mul]
    simp

end Sums

section Main

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

/- English proof (translation)
Rewrite using `[sgLoF_eq, FormRegularity.sgLo_eq, map_sum]`. Both sides reduce to the same expression.
-/
theorem sgLoF_map (L : Formalism.L2.SG.PairVal.MatR D) (ψ : D.host.E →+* ℂ) :
    sgLoF (L.map ψ) = ψ (Formalism.L2.SG.PairVal.sgLo L) := by
  rw [sgLoF_eq, FormRegularity.sgLo_eq, map_sum]
  rfl

/- English proof (translation)
Rewrite using `[sgUpF_eq, FormRegularity.sgUp_eq, map_sum]`. Both sides reduce to the same expression.
-/
theorem sgUpF_map (U : Formalism.L2.SG.PairVal.MatR D) (ψ : D.host.E →+* ℂ) :
    sgUpF (U.map ψ) = ψ (Formalism.L2.SG.PairVal.sgUp U) := by
  rw [sgUpF_eq, FormRegularity.sgUp_eq, map_sum]
  rfl

/- English proof (translation)
Use `set ε := X.B.I.ε v`. Use `set e : Fin D.R.rS → Fin X.B.I.n → ℂ := fun a => rv X.B.I v (X.eR a)`. Use `set f : Fin D.R.rS → Fin X.B.I.n → ℂ := fun a => rv X.B.I v (X.fR a)`. Use `set z := rv X.B.I v (X.zR u)`. Use `set z' := rv X.B.I v (X.zR u')`.

Establish `hfr` using `HermitianSumRootCoordinateFrames.FrameAtV_holds D X u v`. Establish `hfr'` using `HermitianSumRootCoordinateFrames.FrameAtV_holds D X u' v`. Establish `hfe : ∀ a b, hJ ε (f a) (e b) = if a = b then 1 else 0` using `hfr.2.2.2.1`. Take `⟨hPg, sPg⟩` from `frameMat_spec ε e f z hfe (uMat (g v)) (hg v)`. Take `⟨hPg', sPg'⟩` from `frameMat_spec ε e f z' hfe (uMat (g' v)) (hg' v)`.

Use `set Pg := frameMat ε e f z (uMat (g v)) with hPgdef`. Use `set Pg' := frameMat ε e f z' (uMat (g' v)) with hPg'def`. Establish `hrc : ∀ a, rootCoord ε e f z (uMat (g v)) a = Pg a.succ a.castSucc` using `fun a => HermitianSumRootCoordinateFrames.RootCoordFrame_holds _ _ ε e f z hfe (fun a => (hfr.2.2.2.2.1 a).2) _ _ sPg a`. Establish `hrc' : ∀ a, rootCoord ε e f z' (uMat (g' v)) a = Pg' a.succ a.castSucc` using `fun a => HermitianSumRootCoordinateFrames.RootCoordFrame_holds _ _ ε e f z' hfe (fun a => (hfr'.2.2.2.2.1 a).2) _ _ sPg' a`. Establish `h4` using `HermitianSumRootCoordinateFrames.ZhatNAct_holds _ _ ε (fam e z) (fam e z') (uMat (g v)) (uMat (g⁻¹ v)) (uMat (g' v)) (uMat (γ v)) Pg Pg' (Formalism.L2.SG.RealObj.InfCut.uMat_inv_mul' (g v)) (hJ_map _ (g v).2) sPg sPg'`.

Establish `hγw : γw = g⁻¹ * γ * g'` using `by rw [hdec]; group`. Establish `hu : uMat (g⁻¹ v) * uMat (γ v) * uMat (g' v) = uMat (γw v)`. Rewrite using `[hγw]`. Simplify using `only [uMat, Pi.mul_apply, Subgroup.coe_mul, Units.val_mul]`. Rewrite `h4` using `[hu]`.

Establish `hw` using `hPt v`. Establish `hz` using `hZ v`. Rewrite `hw`, `hz` using `[FormRegularity.zx_eq, FormRegularity.zhatO_eq]`. Rewrite `hw` using `[h4]`. Use `set ψ : D.host.E →+* ℂ := (X.B.I.φ v).comp X.ιE.symm.toRingHom with hψ`.

Use `set Zγ := Zhat ε (fam e z) (fam e z') (uMat (γ v))`. Establish `hz' : Zγ * FormRegularity.sgn D.R.rS = L.map ψ * ptMat (mapPt ψ w) * U.map ψ`. Rewrite using `[ptMat_mapPt, ← Matrix.map_mul, ← Matrix.map_mul]`. Conclude with `hz`. Establish `hw' : (Pg.map star * L.map ψ) * ptMat (mapPt ψ w) * (U.map ψ * (FormRegularity.sgn D.R.rS * Pg'ᵀ * FormRegularity.sgn D.R.rS)) = 1 * ptMat (mapPt ψ w) * 1`.

Rewrite using `[Matrix.one_mul, Matrix.mul_one]`. Establish `hC : ptMat (mapPt ψ w) = ptC X v w` using `ptMat_mapPt ψ w`. Use `conv_rhs => rw [hC, ← hw]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = Pg.map star * (Zγ * FormRegularity.sgn D.R.rS) * (FormRegularity.sgn D.R.rS * Pg'ᵀ * FormRegularity.sgn D.R.rS) := by rw [hz']`. Use `_ = Pg.map star * Zγ * Pg'ᵀ * FormRegularity.sgn D.R.rS := by`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [FormRegularity.sgn_sq, Matrix.mul_one]`.

Establish `hLo` using `Formalism.MainNotions.BridgeLemma.bru_lo_mul (FormRegularity.isLoUni_star hPg) (FormRegularity.isLoUni_map ψ hL)`. Establish `hUp` using `Formalism.MainNotions.BridgeLemma.bru_up_mul (FormRegularity.isUpUni_map ψ hU) (isUpUni_sgnT hPg')`. Establish `hds` using `decompSimpleF (mapPt ψ w) hLo hUp isLoUni_one isUpUni_one hw'`. Rewrite `hds` using `[sgLoF_mul (FormRegularity.isLoUni_star hPg) (FormRegularity.isLoUni_map ψ hL), sgUpF_mul (FormRegularity.isUpUni_map ψ hU) (isUpUni_sgnT hPg'), sgLoF_one, sgUpF_one, sgLoF_map, sgUpF_map]`. Establish `e1 : sgLoF (Pg.map star) = ∑ a, star (rootCoord ε e f z (uMat (g v)) a)`.

Rewrite using `[sgLoF_eq]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.map_apply, hrc]`. Establish `e2 : sgUpF (FormRegularity.sgn D.R.rS * Pg'ᵀ * FormRegularity.sgn D.R.rS) = -∑ a, rootCoord ε e f z' (uMat (g' v)) a`. Rewrite using `[sgUpF_eq, ← Finset.sum_neg_distrib]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `only [FormRegularity.sgn, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply]`. Rewrite using `[hrc']`. Take the linear combination `(Pg' a.succ a.castSucc) * FormRegularity.sgn_adj a`. Rewrite `hds` using `[e1, e2]`.

Establish `hψy : ψ (Formalism.L2.SG.PairVal.sgLo L) + ψ (Formalism.L2.SG.PairVal.sgUp U) = X.B.I.φ v (X.ιE.symm (Formalism.L2.SG.PairVal.sgLo L + Formalism.L2.SG.PairVal.sgUp U))`. Rewrite using `[← map_add]`. Both sides reduce to the same expression. Take the linear combination `hds - hψy`.
-/
theorem place_id (u u' : D.what₂.Word) {γ γw g g' : X.B.I.Ginf} (hg : g ∈ X.SinfU u) (hg' : g' ∈ X.SinfU u')
    (hdec : γ = g * γw * g'⁻¹) (w : Point D.host.E (D.R.rS + 1)) (hPt : IsPtRep X u u' w γw)
    (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U)
    (hZ : ∀ v, ZhatO (ZX X u u' 1 γ v) = (L * ptMat w * U).map (fun x => X.B.I.φ v (X.ιE.symm x)))
    (v : InfinitePlace X.B.I.F) :
    ∑ a, star (rootCoord (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a))
        (rv X.B.I v (X.zR u)) (uMat (g v)) a) -
      ∑ a, rootCoord (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a))
        (rv X.B.I v (X.zR u')) (uMat (g' v)) a =
      -(X.B.I.φ v (X.ιE.symm (Formalism.L2.SG.PairVal.sgLo L + Formalism.L2.SG.PairVal.sgUp U))) := by
  set ε := X.B.I.ε v
  set e : Fin D.R.rS → Fin X.B.I.n → ℂ := fun a => rv X.B.I v (X.eR a)
  set f : Fin D.R.rS → Fin X.B.I.n → ℂ := fun a => rv X.B.I v (X.fR a)
  set z := rv X.B.I v (X.zR u)
  set z' := rv X.B.I v (X.zR u')
  have hfr := HermitianSumRootCoordinateFrames.FrameAtV_holds D X u v
  have hfr' := HermitianSumRootCoordinateFrames.FrameAtV_holds D X u' v
  have hfe : ∀ a b, hJ ε (f a) (e b) = if a = b then 1 else 0 := hfr.2.2.2.1
  obtain ⟨hPg, sPg⟩ := frameMat_spec ε e f z hfe (uMat (g v)) (hg v)
  obtain ⟨hPg', sPg'⟩ := frameMat_spec ε e f z' hfe (uMat (g' v)) (hg' v)
  set Pg := frameMat ε e f z (uMat (g v)) with hPgdef
  set Pg' := frameMat ε e f z' (uMat (g' v)) with hPg'def
  have hrc : ∀ a, rootCoord ε e f z (uMat (g v)) a = Pg a.succ a.castSucc := fun a =>
    HermitianSumRootCoordinateFrames.RootCoordFrame_holds _ _ ε e f z hfe (fun a => (hfr.2.2.2.2.1 a).2) _ _ sPg a
  have hrc' : ∀ a, rootCoord ε e f z' (uMat (g' v)) a = Pg' a.succ a.castSucc := fun a =>
    HermitianSumRootCoordinateFrames.RootCoordFrame_holds _ _ ε e f z' hfe (fun a => (hfr'.2.2.2.2.1 a).2) _ _ sPg' a
  have h4 := HermitianSumRootCoordinateFrames.ZhatNAct_holds _ _ ε (fam e z) (fam e z') (uMat (g v)) (uMat (g⁻¹ v)) (uMat (g' v))
    (uMat (γ v)) Pg Pg' (Formalism.L2.SG.RealObj.InfCut.uMat_inv_mul' (g v)) (hJ_map _ (g v).2) sPg sPg'
  have hγw : γw = g⁻¹ * γ * g' := by rw [hdec]; group
  have hu : uMat (g⁻¹ v) * uMat (γ v) * uMat (g' v) = uMat (γw v) := by
    rw [hγw]; simp only [uMat, Pi.mul_apply, Subgroup.coe_mul, Units.val_mul]
  rw [hu] at h4
  have hw := hPt v
  have hz := hZ v
  rw [FormRegularity.zx_eq, FormRegularity.zhatO_eq] at hw hz
  rw [h4] at hw
  set ψ : D.host.E →+* ℂ := (X.B.I.φ v).comp X.ιE.symm.toRingHom with hψ
  set Zγ := Zhat ε (fam e z) (fam e z') (uMat (γ v))
  have hz' : Zγ * FormRegularity.sgn D.R.rS = L.map ψ * ptMat (mapPt ψ w) * U.map ψ := by
    rw [ptMat_mapPt, ← Matrix.map_mul, ← Matrix.map_mul]
    exact hz
  have hw' : (Pg.map star * L.map ψ) * ptMat (mapPt ψ w) * (U.map ψ * (FormRegularity.sgn D.R.rS * Pg'ᵀ * FormRegularity.sgn D.R.rS)) =
      1 * ptMat (mapPt ψ w) * 1 := by
    rw [Matrix.one_mul, Matrix.mul_one]
    have hC : ptMat (mapPt ψ w) = ptC X v w := ptMat_mapPt ψ w
    conv_rhs => rw [hC, ← hw]
    calc (Pg.map star * L.map ψ) * ptMat (mapPt ψ w) * (U.map ψ * (FormRegularity.sgn D.R.rS * Pg'ᵀ * FormRegularity.sgn D.R.rS))
        = Pg.map star * (L.map ψ * ptMat (mapPt ψ w) * U.map ψ) * (FormRegularity.sgn D.R.rS * Pg'ᵀ * FormRegularity.sgn D.R.rS) := by
          simp only [Matrix.mul_assoc]
      _ = Pg.map star * (Zγ * FormRegularity.sgn D.R.rS) * (FormRegularity.sgn D.R.rS * Pg'ᵀ * FormRegularity.sgn D.R.rS) := by rw [hz']
      _ = Pg.map star * Zγ * Pg'ᵀ * FormRegularity.sgn D.R.rS := by
          calc _ = Pg.map star * Zγ * (FormRegularity.sgn D.R.rS * FormRegularity.sgn D.R.rS) * Pg'ᵀ * FormRegularity.sgn D.R.rS := by
                simp only [Matrix.mul_assoc]
            _ = _ := by rw [FormRegularity.sgn_sq, Matrix.mul_one]
  have hLo := Formalism.MainNotions.BridgeLemma.bru_lo_mul (FormRegularity.isLoUni_star hPg) (FormRegularity.isLoUni_map ψ hL)
  have hUp := Formalism.MainNotions.BridgeLemma.bru_up_mul (FormRegularity.isUpUni_map ψ hU) (isUpUni_sgnT hPg')
  have hds := decompSimpleF (mapPt ψ w) hLo hUp isLoUni_one isUpUni_one hw'
  rw [sgLoF_mul (FormRegularity.isLoUni_star hPg) (FormRegularity.isLoUni_map ψ hL),
    sgUpF_mul (FormRegularity.isUpUni_map ψ hU) (isUpUni_sgnT hPg'), sgLoF_one, sgUpF_one, sgLoF_map, sgUpF_map] at hds
  have e1 : sgLoF (Pg.map star) = ∑ a, star (rootCoord ε e f z (uMat (g v)) a) := by
    rw [sgLoF_eq]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.map_apply, hrc]
  have e2 : sgUpF (FormRegularity.sgn D.R.rS * Pg'ᵀ * FormRegularity.sgn D.R.rS) = -∑ a, rootCoord ε e f z' (uMat (g' v)) a := by
    rw [sgUpF_eq, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [FormRegularity.sgn, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply]
    rw [hrc']
    linear_combination (Pg' a.succ a.castSucc) * FormRegularity.sgn_adj a
  rw [e1, e2] at hds
  have hψy : ψ (Formalism.L2.SG.PairVal.sgLo L) + ψ (Formalism.L2.SG.PairVal.sgUp U) =
      X.B.I.φ v (X.ιE.symm (Formalism.L2.SG.PairVal.sgLo L + Formalism.L2.SG.PairVal.sgUp U)) := by
    rw [← map_add]; rfl
  linear_combination hds - hψy

end Main

section Main2

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

/- English proof (translation)
Establish `hgS : X.B.g = gS D` using `X.g_eq`. Use `set y := Formalism.L2.SG.PairVal.sgLo L + Formalism.L2.SG.PairVal.sgUp U with hy`. Rewrite using `[Formalism.L2.SG.Pf.phasePair_eq, ← FormRegularity.psiInf_neg, ← RingEquiv.apply_symm_apply X.ιE (-y), ← PlaceEmbeddingTraceSums.TraceSum_holds D X (gS D) (X.ιE.symm (-y))]`. Unfold `HidaSetting.psiInfU psiInf psiR`. Rewrite using `[hgS, map_prod (starRingEnd ℂ), ← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[← Complex.exp_conj, ← Complex.exp_add]`. Use `congr 1`. Establish `hp` using `place_id X u u' hg hg' hdec w hPt L U hL hU hZ v`. Use `set A := ∑ a, rootCoord (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) (uMat (g v)) a with hA`.

Use `set A' := ∑ a, rootCoord (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u')) (uMat (g' v)) a with hA'`. Use `set Y := X.B.I.φ v (X.ιE.symm y) with hY`. Establish `hsA : (∑ a, star (rootCoord (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) (uMat (g v)) a)) = star A` using `by rw [hA, star_sum]`. Rewrite `hp` using `[hsA]`. Establish `hp'` using `congrArg (starRingEnd ℂ) hp`.

Simplify using `only [map_sub, map_neg, Complex.star_def, Complex.conj_conj] at hp'`. Establish `e1 : ∑ a, (rootCoord (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) (uMat (g v)) a + star (rootCoord (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) (uMat (g v)) a)) = A + star A`. Rewrite using `[Finset.sum_add_distrib, hA, star_sum]`. Establish `e2 : ∑ a, (rootCoord (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u')) (uMat (g' v)) a + star (rootCoord (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u')) (uMat (g' v)) a)) = A' + star A …`. Rewrite using `[Finset.sum_add_distrib, hA', star_sum]`.

Rewrite using `[e1, e2]`. Simplify using `only [map_neg]`. Rewrite using `[← hY]`. Simplify using `only [map_mul, map_div₀, map_add, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_natCast, Complex.star_def, Complex.conj_conj, map_neg]`. Rewrite `hp` using `[Complex.star_def]`.

Simplify using `only [div_eq_mul_inv]`. Take the linear combination `(2 * (Real.pi : ℂ) * Complex.I * ((gS D : ℕ) : ℂ)⁻¹) * (hp + hp')`.
-/
theorem realPhase (u u' : D.what₂.Word) {γ γw g g' : X.B.I.Ginf} (hg : g ∈ X.SinfU u) (hg' : g' ∈ X.SinfU u')
    (hdec : γ = g * γw * g'⁻¹) (w : Point D.host.E (D.R.rS + 1)) (hPt : IsPtRep X u u' w γw)
    (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U)
    (hZ : ∀ v, ZhatO (ZX X u u' 1 γ v) = (L * ptMat w * U).map (fun x => X.B.I.φ v (X.ιE.symm x))) :
    X.psiInfU u g * conj (X.psiInfU u' g') = Formalism.L2.SG.PairVal.phasePair (gS D) L U := by
  have hgS : X.B.g = gS D := X.g_eq
  set y := Formalism.L2.SG.PairVal.sgLo L + Formalism.L2.SG.PairVal.sgUp U with hy
  rw [Formalism.L2.SG.Pf.phasePair_eq, ← FormRegularity.psiInf_neg, ← RingEquiv.apply_symm_apply X.ιE (-y),
    ← PlaceEmbeddingTraceSums.TraceSum_holds D X (gS D) (X.ιE.symm (-y))]
  unfold HidaSetting.psiInfU psiInf psiR
  rw [hgS, map_prod (starRingEnd ℂ), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  have hp := place_id X u u' hg hg' hdec w hPt L U hL hU hZ v
  set A := ∑ a, rootCoord (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a))
    (rv X.B.I v (X.zR u)) (uMat (g v)) a with hA
  set A' := ∑ a, rootCoord (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a))
    (rv X.B.I v (X.zR u')) (uMat (g' v)) a with hA'
  set Y := X.B.I.φ v (X.ιE.symm y) with hY
  have hsA : (∑ a, star (rootCoord (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a))
      (rv X.B.I v (X.zR u)) (uMat (g v)) a)) = star A := by rw [hA, star_sum]
  rw [hsA] at hp
  have hp' := congrArg (starRingEnd ℂ) hp
  simp only [map_sub, map_neg, Complex.star_def, Complex.conj_conj] at hp'
  have e1 : ∑ a, (rootCoord (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a))
      (rv X.B.I v (X.zR u)) (uMat (g v)) a + star (rootCoord (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a))
      (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) (uMat (g v)) a)) = A + star A := by
    rw [Finset.sum_add_distrib, hA, star_sum]
  have e2 : ∑ a, (rootCoord (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a))
      (rv X.B.I v (X.zR u')) (uMat (g' v)) a + star (rootCoord (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a))
      (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u')) (uMat (g' v)) a)) = A' + star A' := by
    rw [Finset.sum_add_distrib, hA', star_sum]
  rw [e1, e2]
  simp only [map_neg]
  rw [← hY]
  simp only [map_mul, map_div₀, map_add, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_natCast,
    Complex.star_def, Complex.conj_conj, map_neg]
  rw [Complex.star_def] at hp
  simp only [div_eq_mul_inv]
  linear_combination (2 * (Real.pi : ℂ) * Complex.I * ((gS D : ℕ) : ℂ)⁻¹) * (hp + hp')

end Main2

end Formalism.L2.SG.RealObj.RealPhaseFrames
