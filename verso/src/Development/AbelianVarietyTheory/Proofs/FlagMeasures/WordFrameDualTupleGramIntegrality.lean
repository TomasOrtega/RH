import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Direct
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeUnimodular
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovDom.FrameCrd

variable {D : D7} (X : HidaSetting D)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sig_apply (x : D.host.E) : (D.sp.cm.sig : D.host.E →+* D.host.E) x = starRingEnd D.host.E x := rfl

/- English proof (translation)
Simplify using `only [vecOf, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Module.Basis.equivFun_symm_apply, LinearEquiv.funCongrLeft_apply]`. Rewrite using `[← Equiv.sum_comp (ci X).symm]`. Simplify using the standard rewrite rules.
-/
theorem vecOf_sum (x : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) :
    vecOf X x = ∑ i, x i • X.bas (ci X i) := by
  simp only [vecOf, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    Module.Basis.equivFun_symm_apply, LinearEquiv.funCongrLeft_apply]
  rw [← Equiv.sum_comp (ci X).symm]
  simp

/- English proof (translation)
Rewrite using `[vecOf_sum]`. Simplify using `only [crdH]`. Rewrite using `[Equiv.sum_comp (ci X) (fun j => X.bas.repr y j • X.bas j)]`. Conclude with `X.bas.sum_repr y`.
-/
theorem vecOf_crdH (y : (VS D).V) : vecOf X (crdH X y) = y := by
  rw [vecOf_sum]
  simp only [crdH]
  rw [Equiv.sum_comp (ci X) (fun j => X.bas.repr y j • X.bas j)]
  exact X.bas.sum_repr y

/- English proof (translation)
Rewrite using `[vecOf_sum, vecOf_sum]`. Simplify using `only [GlobalTheory.SgAlg.pairM, GlobalTheory.SgAlg.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Jc, map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum, sig_apply]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [RingHom.id_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pairM_apply {α β : Type} [Fintype α] [Fintype β]
    (P : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) α D.host.E) (Q : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) β D.host.E)
    (a : α) (b : β) :
    GlobalTheory.SgAlg.pairM (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) Q P a b =
      (VS D).hT (vecOf X fun i => P i a) (vecOf X fun i => Q i b) := by
  rw [vecOf_sum, vecOf_sum]
  simp only [GlobalTheory.SgAlg.pairM, GlobalTheory.SgAlg.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Jc,
    map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum, sig_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [RingHom.id_apply]
  ring

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[Pc]`.
-/
theorem col_last (u : D.what₂.Word) : (fun i => Pc X u i (Fin.last D.R.rS)) = crdH X (X.zu u) := by
  funext i; simp [Pc]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[Pc]`.
-/
theorem col_cs (u : D.what₂.Word) (a : Fin D.R.rS) : (fun i => Pc X u i a.castSucc) = crdH X (X.eX a) := by
  funext i; simp [Pc]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[fc]`.
-/
theorem col_f (a : Fin D.R.rS) : (fun i => fc X i a) = crdH X (X.fY a) := by
  funext i; simp [fc]

/- English proof (translation)
Rewrite using `[← (VS D).herm.eq x y, h, map_zero]`.
-/
theorem hT_swap_zero {x y : (VS D).V} (h : (VS D).hT x y = 0) : (VS D).hT y x = 0 := by
  rw [← (VS D).herm.eq x y, h, map_zero]

/- English proof (translation)
The claim follows from `Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero`.
-/
theorem T_ne_zero (u : D.what₂.Word) : ((((D.mem u).A.T : ℕ) : D.host.E)) ≠ 0 :=
  Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[pairM_apply]`. Proceed by induction on `a using Fin.lastCases with`. Consider the case `last`. Proceed by induction on `b using Fin.lastCases with`.

Consider the case `last => rw [col_last, vecOf_crdH, X.zu_norm]`. Simplify using `[GlobalTheory.SgAlg.TF, Tc]`. Consider the case `cast b`. Rewrite using `[col_last, col_cs, vecOf_crdH, vecOf_crdH, hT_swap_zero (X.zu_orth u b).1]`. Simplify using `[GlobalTheory.SgAlg.TF, (Fin.castSucc_ne_last b).symm]`.

Consider the case `cast a`. Proceed by induction on `b using Fin.lastCases with`. Consider the case `last`. Rewrite using `[col_last, col_cs, vecOf_crdH, vecOf_crdH, (X.zu_orth u a).1]`. Simplify using `[GlobalTheory.SgAlg.TF, Fin.castSucc_ne_last a]`.

Consider the case `cast b`. Rewrite using `[col_cs, col_cs, vecOf_crdH, vecOf_crdH, X.ee]`. Simplify using `[GlobalTheory.SgAlg.TF, Matrix.diagonal_apply, Fin.castSucc_ne_last a]`.
-/
theorem gram_frame (u : D.what₂.Word) :
    GlobalTheory.SgAlg.pairM (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) (Pc X u) =
      GlobalTheory.SgAlg.TF D.R.rS (algebraMap D.host.F D.host.E (Tc u)) := by
  ext a b
  rw [pairM_apply]
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => rw [col_last, vecOf_crdH, X.zu_norm]; simp [GlobalTheory.SgAlg.TF, Tc]
    | cast b =>
      rw [col_last, col_cs, vecOf_crdH, vecOf_crdH, hT_swap_zero (X.zu_orth u b).1]
      simp [GlobalTheory.SgAlg.TF, (Fin.castSucc_ne_last b).symm]
  | cast a =>
    induction b using Fin.lastCases with
    | last =>
      rw [col_last, col_cs, vecOf_crdH, vecOf_crdH, (X.zu_orth u a).1]
      simp [GlobalTheory.SgAlg.TF, Fin.castSucc_ne_last a]
    | cast b =>
      rw [col_cs, col_cs, vecOf_crdH, vecOf_crdH, X.ee]
      simp [GlobalTheory.SgAlg.TF, Matrix.diagonal_apply, Fin.castSucc_ne_last a]

/- English proof (translation)
Establish `hT0` using `T_ne_zero u`. Set `Y : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (D.R.rS + 1)) D.host.E` to `Matrix.of fun i c => Fin.lastCases (crdH X (X.zu u) i) (fun a => crdH X (X.fY a) i) c`. Set `Dg : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E` to `Matrix.diagonal fun c => Fin.lastCases (-(((D.mem u).A.T : ℕ) : D.host.E))⁻¹ (fun _ => 1) c`. Use `⟨Dg * (GlobalTheory.SgAlg.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * Jc X), ?_⟩` and prove the remaining obligations. Establish `h : Dg * (GlobalTheory.SgAlg.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * Jc X) * Pc X u = Dg * GlobalTheory.SgAlg.pairM (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) Y`.

Simplify using `only [GlobalTheory.SgAlg.pairM, Matrix.mul_assoc]`. Rewrite using `[h]`. Use extensionality with `c d`. Rewrite using `[Matrix.diagonal_mul, pairM_apply]`. Proceed by induction on `c using Fin.lastCases with`.

Consider the case `last`. Establish `hy : (fun i => Y i (Fin.last D.R.rS)) = crdH X (X.zu u)` using `by funext i; simp [Y]`. Proceed by induction on `d using Fin.lastCases with`. Consider the case `last => rw [hy, col_last, vecOf_crdH, X.zu_norm]`. Simplify using `[hT0]`.

Consider the case `cast b`. Rewrite using `[hy, col_cs, vecOf_crdH, vecOf_crdH, hT_swap_zero (X.zu_orth u b).1]`. Simplify using `[(Fin.castSucc_ne_last b).symm]`. Consider the case `cast a`. Establish `hy : (fun i => Y i a.castSucc) = crdH X (X.fY a)` using `by funext i; simp [Y]`.

Proceed by induction on `d using Fin.lastCases with`. Consider the case `last`. Rewrite using `[hy, col_last, vecOf_crdH, vecOf_crdH, (X.zu_orth u a).2]`. Simplify using `[Fin.castSucc_ne_last a]`. Consider the case `cast b`.

Rewrite using `[hy, col_cs, vecOf_crdH, vecOf_crdH, ← (VS D).herm.eq (X.eX b) (X.fY a), X.ef]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hab, Ne.symm hab]`.
-/
theorem free_frame (u : D.what₂.Word) : GlobalTheory.SgAlg.Free (Pc X u) := by
  have hT0 := T_ne_zero u
  let Y : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (D.R.rS + 1)) D.host.E :=
    Matrix.of fun i c => Fin.lastCases (crdH X (X.zu u) i) (fun a => crdH X (X.fY a) i) c
  let Dg : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E :=
    Matrix.diagonal fun c => Fin.lastCases (-(((D.mem u).A.T : ℕ) : D.host.E))⁻¹ (fun _ => 1) c
  refine ⟨Dg * (GlobalTheory.SgAlg.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * Jc X), ?_⟩
  have h : Dg * (GlobalTheory.SgAlg.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * Jc X) * Pc X u =
      Dg * GlobalTheory.SgAlg.pairM (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) Y := by
    simp only [GlobalTheory.SgAlg.pairM, Matrix.mul_assoc]
  rw [h]
  ext c d
  rw [Matrix.diagonal_mul, pairM_apply]
  induction c using Fin.lastCases with
  | last =>
    have hy : (fun i => Y i (Fin.last D.R.rS)) = crdH X (X.zu u) := by funext i; simp [Y]
    induction d using Fin.lastCases with
    | last => rw [hy, col_last, vecOf_crdH, X.zu_norm]; simp [hT0]
    | cast b =>
      rw [hy, col_cs, vecOf_crdH, vecOf_crdH, hT_swap_zero (X.zu_orth u b).1]
      simp [(Fin.castSucc_ne_last b).symm]
  | cast a =>
    have hy : (fun i => Y i a.castSucc) = crdH X (X.fY a) := by funext i; simp [Y]
    induction d using Fin.lastCases with
    | last =>
      rw [hy, col_last, vecOf_crdH, vecOf_crdH, (X.zu_orth u a).2]
      simp [Fin.castSucc_ne_last a]
    | cast b =>
      rw [hy, col_cs, vecOf_crdH, vecOf_crdH, ← (VS D).herm.eq (X.eX b) (X.fY a), X.ef]
      by_cases hab : a = b
      · subst hab; simp
      · simp [hab, Ne.symm hab]

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Use extensionality with `a b`. Rewrite using `[pairM_apply, col_f, vecOf_crdH]`. Proceed by induction on `a using Fin.lastCases with`. Consider the case `last`.

Rewrite using `[col_last, vecOf_crdH, hT_swap_zero (X.zu_orth u b).2]`. Simplify using `[(Fin.castSucc_ne_last b).symm]`. Consider the case `cast a`. Rewrite using `[col_cs, vecOf_crdH, X.ef]`. Simplify using the standard rewrite rules.

Use extensionality with `a b`. Rewrite using `[pairM_apply, col_f, col_f, vecOf_crdH, vecOf_crdH, X.ff]`. Simplify using the standard rewrite rules.
-/
theorem dual_frame (u : D.what₂.Word) :
    GlobalTheory.SgAlg.IsDual (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) (fc X) := by
  refine ⟨?_, ?_⟩
  · ext a b
    rw [pairM_apply, col_f, vecOf_crdH]
    induction a using Fin.lastCases with
    | last =>
      rw [col_last, vecOf_crdH, hT_swap_zero (X.zu_orth u b).2]
      simp [(Fin.castSucc_ne_last b).symm]
    | cast a =>
      rw [col_cs, vecOf_crdH, X.ef]
      simp
  · ext a b
    rw [pairM_apply, col_f, col_f, vecOf_crdH, vecOf_crdH, X.ff]
    simp

/- English proof (translation)
Rewrite using `[aaD, GlobalTheory.IntTerm.Conv.ddS_eq, GlobalTheory.SgGlob.dInv, ← Nat.cast_sub a.2.le, _root_.zpow_neg, _root_.zpow_natCast, inv_pow]`.
-/
theorem aaD_eq (a : Fin D.R.rS) : aaD D a = GlobalTheory.SgGlob.dInv D.host.E (D.R.rS - a) := by
  rw [aaD, GlobalTheory.IntTerm.Conv.ddS_eq, GlobalTheory.SgGlob.dInv, ← Nat.cast_sub a.2.le, _root_.zpow_neg, _root_.zpow_natCast,
    inv_pow]

/- English proof (translation)
Rewrite using `[GlobalTheory.SnMass.tupLat, Submodule.span_le]`. Introduce and unpack `_ ⟨b, x, hx, rfl⟩`. Use `show vecOf X (x • fun i => GlobalTheory.SnMass.sideM (Pc X u) (fc X) i b) ∈ (VS D).L0`. Rewrite using `[LinearMap.map_smul, X.Lam_split]`. Proceed by induction on `b using Fin.addCases with`.

Consider the case `left c`. Simplify using `only [GlobalTheory.SnMass.sideM, Fin.append_left]`. Simplify using `only [GlobalTheory.SnMass.id1, Fin.append_left] at hx`. Proceed by induction on `c using Fin.lastCases with`. Consider the case `last`.

Simplify using `only [Fin.val_last, Nat.sub_self, GlobalTheory.SgGlob.dInv, pow_zero] at hx`. Take `⟨o, rfl⟩` from `(FractionalIdeal.mem_one_iff _).1 hx`. Rewrite using `[col_last, vecOf_crdH, algebraMap_smul]`. Conclude with `Submodule.mem_sup_left (Submodule.mem_sup_right (X.Lb.smul_mem o (X.zu_Lb u)))`. Consider the case `cast a`.

Simplify using `only [Fin.val_castSucc] at hx`. Rewrite `hx` using `[← aaD_eq]`. Rewrite using `[col_cs, vecOf_crdH]`. Conclude with `Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨a, x, hx, rfl⟩))`. Consider the case `right a`.

Simplify using `only [GlobalTheory.SnMass.sideM, Fin.append_right]`. Simplify using `only [GlobalTheory.SnMass.id1, Fin.append_right] at hx`. Rewrite `hx` using `[← aaD_eq]`. Rewrite using `[col_f, vecOf_crdH]`. Conclude with `Submodule.mem_sup_right (Submodule.subset_span ⟨a, x, hx, rfl⟩)`.
-/
theorem tupLat_le (u : D.what₂.Word) :
    GlobalTheory.SnMass.tupLat (GlobalTheory.SnMass.id1 D.host.E D.R.rS) (GlobalTheory.SnMass.sideM (Pc X u) (fc X)) ≤ Lc X := by
  rw [GlobalTheory.SnMass.tupLat, Submodule.span_le]
  rintro _ ⟨b, x, hx, rfl⟩
  show vecOf X (x • fun i => GlobalTheory.SnMass.sideM (Pc X u) (fc X) i b) ∈ (VS D).L0
  rw [LinearMap.map_smul, X.Lam_split]
  induction b using Fin.addCases with
  | left c =>
    simp only [GlobalTheory.SnMass.sideM, Fin.append_left]
    simp only [GlobalTheory.SnMass.id1, Fin.append_left] at hx
    induction c using Fin.lastCases with
    | last =>
      simp only [Fin.val_last, Nat.sub_self, GlobalTheory.SgGlob.dInv, pow_zero] at hx
      obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
      rw [col_last, vecOf_crdH, algebraMap_smul]
      exact Submodule.mem_sup_left (Submodule.mem_sup_right (X.Lb.smul_mem o (X.zu_Lb u)))
    | cast a =>
      simp only [Fin.val_castSucc] at hx
      rw [← aaD_eq] at hx
      rw [col_cs, vecOf_crdH]
      exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨a, x, hx, rfl⟩))
  | right a =>
    simp only [GlobalTheory.SnMass.sideM, Fin.append_right]
    simp only [GlobalTheory.SnMass.id1, Fin.append_right] at hx
    rw [← aaD_eq] at hx
    rw [col_f, vecOf_crdH]
    exact Submodule.mem_sup_right (Submodule.subset_span ⟨a, x, hx, rfl⟩)

end GlobalTheory.CovDom.FrameCrd

namespace GlobalTheory.CovDom

open GlobalTheory.CovDom.FrameCrd in

/- English proof (translation)
Introduce `_ X u` and use `⟨⟨free_frame X u, gram_frame X u⟩, dual_frame X u, tupLat_le X u⟩`.
-/
theorem frame_dual_lat : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word),
    GlobalTheory.SgAlg.IsFrame (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (algebraMap D.host.F D.host.E (Tc u)) (Pc X u) ∧
    GlobalTheory.SgAlg.IsDual (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) (fc X) ∧
    GlobalTheory.SnMass.tupLat (GlobalTheory.SnMass.id1 D.host.E D.R.rS) (GlobalTheory.SnMass.sideM (Pc X u) (fc X)) ≤ Lc X :=
  fun _ X u => ⟨⟨free_frame X u, gram_frame X u⟩, dual_frame X u, tupLat_le X u⟩

end GlobalTheory.CovDom
