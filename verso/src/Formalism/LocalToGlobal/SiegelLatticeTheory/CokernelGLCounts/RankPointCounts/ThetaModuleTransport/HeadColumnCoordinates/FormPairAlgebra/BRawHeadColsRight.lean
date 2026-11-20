import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.AlgInj

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

namespace Formalism.L2.SG.LocalCountModules.UnramifiedPairingLinear

section Gen

variable {R : Type} [CommRing R] {r : ℕ}

/- English proof (translation)
Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun R).mp hy`. Use `⟨Fin.snoc c 0, by simp, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, mul_zero, add_zero]`. Conclude with `Finset.sum_congr rfl fun a _ => mul_comm _ _`.
-/
theorem mem_headCols {Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R} {y : Fin (r + 1) → R}
    (hy : y ∈ headCols Z) : ∃ w : Fin (r + 1) → R, w (Fin.last r) = 0 ∧ y = Z.mulVec w := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hy
  refine ⟨Fin.snoc c 0, by simp, ?_⟩
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc,
    Fin.snoc_castSucc, Fin.snoc_last, mul_zero, add_zero]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

/- English proof (translation)
Establish `h1 : v - c • (fun i => Z i (Fin.last r)) ∈ headCols Z`. Rewrite using `[← Submodule.Quotient.eq]`. Rewrite using `[hv, bCls, Submodule.Quotient.mk_smul]`. Take `⟨w, -, hw⟩` from `mem_headCols h1`. Use `⟨w + Pi.single (Fin.last r) c, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.mulVec_add, ← hw]`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec_single]`.
-/
theorem exists_of_mk {Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R} {v : Fin (r + 1) → R} {c : R}
    (hv : (Submodule.Quotient.mk v : MbMod Z) = c • bCls Z) : ∃ w, v = Z.mulVec w := by
  have h1 : v - c • (fun i => Z i (Fin.last r)) ∈ headCols Z := by
    rw [← Submodule.Quotient.eq]
    rw [hv, bCls, Submodule.Quotient.mk_smul]
  obtain ⟨w, -, hw⟩ := mem_headCols h1
  refine ⟨w + Pi.single (Fin.last r) c, ?_⟩
  rw [Matrix.mulVec_add, ← hw]
  funext i
  simp [Matrix.mulVec_single]

/- English proof (translation)
Use extensionality with `i`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.
-/
theorem sum_smul_single (c : Fin (r + 1) → R) : ∑ a, c a • (Pi.single a 1 : Fin (r + 1) → R) = c := by
  ext i
  simp [Finset.sum_apply, Pi.single_apply]

end Gen

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

/- English proof (translation)
Simplify using `[Matrix.mulVec, dotProduct, Matrix.map_apply]`.
-/
theorem coe_mulVec (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (v : Fin (r + 1) → O) (i : Fin (r + 1)) :
    ((Z.mulVec v i : O) : E) = (Z.map O.subtype).mulVec (fun j => (v j : E)) i := by
  simp [Matrix.mulVec, dotProduct, Matrix.map_apply]

/- English proof (translation)
Simplify using `[Matrix.mulVec, dotProduct, cjT, Matrix.map_apply]`.
-/
theorem cjT_mulVec_coe (hO : ∀ x ∈ O, cj x ∈ O) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O)
    (w : Fin (r + 1) → O) (b : Fin (r + 1)) :
    (((cjT O cj hO Z).mulVec w b : O) : E) = ∑ a, cj ((Z.map O.subtype) a b) * (w a : E) := by
  simp [Matrix.mulVec, dotProduct, cjT, Matrix.map_apply]

/- English proof (translation)
Unfold `bRaw`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `h1 : (fun i => (((y + z) i : O) : E)) = (fun i => (y i : E)) + fun i => (z i : E)`. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules. Rewrite using `[h1, Matrix.mulVec_add, Pi.add_apply, mul_add]`.
-/
theorem bRaw_add_left (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (y z y' : Fin (r + 1) → O) :
    bRaw O cj Z (y + z) y' = bRaw O cj Z y y' + bRaw O cj Z z y' := by
  unfold bRaw
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : (fun i => (((y + z) i : O) : E)) = (fun i => (y i : E)) + fun i => (z i : E) := by
    funext i
    simp
  rw [h1, Matrix.mulVec_add, Pi.add_apply, mul_add]

/- English proof (translation)
Unfold `bRaw`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `h1 : (fun i => (((c • y) i : O) : E)) = (c : E) • fun i => (y i : E)`. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules. Rewrite using `[h1, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem bRaw_smul_left (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (c : O) (y y' : Fin (r + 1) → O) :
    bRaw O cj Z (c • y) y' = (c : E) * bRaw O cj Z y y' := by
  unfold bRaw
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : (fun i => (((c • y) i : O) : E)) = (c : E) • fun i => (y i : E) := by
    funext i
    simp
  rw [h1, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Unfold `bRaw`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `[map_add, add_mul]`.
-/
theorem bRaw_add_right (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (y y' z' : Fin (r + 1) → O) :
    bRaw O cj Z y (y' + z') = bRaw O cj Z y y' + bRaw O cj Z y z' := by
  unfold bRaw
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [map_add, add_mul]

/- English proof (translation)
Unfold `bRaw`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem bRaw_smul_right (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (c : O) (y y' : Fin (r + 1) → O) :
    bRaw O cj Z y (c • y') = cj (c : E) * bRaw O cj Z y y' := by
  unfold bRaw
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [map_mul]
  ring

def bLin (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (y' : Fin (r + 1) → O) :
    (Fin (r + 1) → O) →ₗ[O] E where
  toFun y := bRaw O cj Z y y'
  map_add' y z := bRaw_add_left O cj Z y z y'
  map_smul' c y := by rw [bRaw_smul_left]; rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem bLin_apply (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (y y' : Fin (r + 1) → O) :
    bLin O cj Z y' y = bRaw O cj Z y y' := rfl

/- English proof (translation)
Unfold `bRaw`. Establish `h1 : (fun i => ((Z.mulVec v i : O) : E)) = (Z.map O.subtype).mulVec (fun j => (v j : E))`. Use function extensionality and compare the values at `(coe_mulVec O Z v)`. Rewrite using `[h1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]`.
-/
theorem bRaw_mulVec (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (hu : IsUnit (Z.map O.subtype).det)
    (v y' : Fin (r + 1) → O) :
    bRaw O cj Z (Z.mulVec v) y' = ∑ j, cj (y' j : E) * (v j : E) := by
  unfold bRaw
  have h1 : (fun i => ((Z.mulVec v i : O) : E)) = (Z.map O.subtype).mulVec (fun j => (v j : E)) :=
    funext (coe_mulVec O Z v)
  rw [h1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

/- English proof (translation)
Take `⟨w, rfl⟩` from `exists_of_mk hv`. Rewrite using `[bRaw_mulVec O cj Z hu]`. Conclude with `Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hO _ (y' j).2) (w j).2`.
-/
theorem bRaw_mem_of_mk (hO : ∀ x ∈ O, cj x ∈ O) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O)
    (hu : IsUnit (Z.map O.subtype).det) {v : Fin (r + 1) → O} {c : O}
    (hv : (Submodule.Quotient.mk v : MbMod Z) = c • bCls Z) (y' : Fin (r + 1) → O) :
    bRaw O cj Z v y' ∈ O := by
  obtain ⟨w, rfl⟩ := exists_of_mk hv
  rw [bRaw_mulVec O cj Z hu]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hO _ (y' j).2) (w j).2

/- English proof (translation)
Unfold `bRaw`. Simplify using `only [hy', map_sum, map_mul, hcj, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Establish `e : ∑ j, (Z.map O.subtype) a j * cj (w a) * ((Z.map O.subtype)⁻¹.mulVec (fun i => (y i : E))) j = cj (w a) * ((Z.map O.subtype).mulVec ((Z.map O.subtype)⁻¹.mulVec (fun i => (y i : E)))) a`.

Simplify using `only [Matrix.mulVec, dotProduct, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]`.
-/
theorem bRaw_cjT (hcj : ∀ x, cj (cj x) = x) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O)
    (hu : IsUnit (Z.map O.subtype).det) (y y' : Fin (r + 1) → O) (w : Fin (r + 1) → E)
    (hy' : ∀ b, (y' b : E) = ∑ a, cj ((Z.map O.subtype) a b) * w a) :
    bRaw O cj Z y y' = ∑ a, cj (w a) * (y a : E) := by
  unfold bRaw
  simp only [hy', map_sum, map_mul, hcj, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  have e : ∑ j, (Z.map O.subtype) a j * cj (w a) * ((Z.map O.subtype)⁻¹.mulVec (fun i => (y i : E))) j =
      cj (w a) * ((Z.map O.subtype).mulVec ((Z.map O.subtype)⁻¹.mulVec (fun i => (y i : E)))) a := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]

/- English proof (translation)
Unfold `lamS`. Establish `h1 : (fun b => (y' b : E)) = fun b => ∑ a, cj ((Z.map O.subtype) a b) * w a` using `funext hy'`. Rewrite using `[h1]`. Conclude with `lamStarC_mulVec (cj := cj) _ hu w`.
-/
theorem lamS_cjT (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (hu : IsUnit (Z.map O.subtype).det)
    (y' : Fin (r + 1) → O) (w : Fin (r + 1) → E)
    (hy' : ∀ b, (y' b : E) = ∑ a, cj ((Z.map O.subtype) a b) * w a) :
    lamS O cj Z y' = w (Fin.last r) := by
  unfold lamS
  have h1 : (fun b => (y' b : E)) = fun b => ∑ a, cj ((Z.map O.subtype) a b) * w a := funext hy'
  rw [h1]
  exact lamStarC_mulVec (cj := cj) _ hu w

/- English proof (translation)
Take `⟨w, hw0, rfl⟩` from `mem_headCols hy`. Rewrite using `[lamS_cjT O cj Z hu _ (fun a => (w a : E)) (fun b => cjT_mulVec_coe O cj hO Z w b)]`. Simplify using `[hw0]`.
-/
theorem lamS_headCols (hO : ∀ x ∈ O, cj x ∈ O) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O)
    (hu : IsUnit (Z.map O.subtype).det) {y' : Fin (r + 1) → O} (hy : y' ∈ headCols (cjT O cj hO Z)) :
    lamS O cj Z y' = 0 := by
  obtain ⟨w, hw0, rfl⟩ := mem_headCols hy
  rw [lamS_cjT O cj Z hu _ (fun a => (w a : E)) (fun b => cjT_mulVec_coe O cj hO Z w b)]
  simp [hw0]

/- English proof (translation)
Take `⟨w, -, rfl⟩` from `mem_headCols hy`. Rewrite using `[bRaw_cjT O cj hcj Z hu y _ (fun a => (w a : E)) (fun b => cjT_mulVec_coe O cj hO Z w b)]`. Conclude with `Subring.sum_mem _ fun a _ => Subring.mul_mem _ (hO _ (w a).2) (y a).2`.
-/
theorem bRaw_headCols_right (hcj : ∀ x, cj (cj x) = x) (hO : ∀ x ∈ O, cj x ∈ O)
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (hu : IsUnit (Z.map O.subtype).det)
    (y : Fin (r + 1) → O) {y' : Fin (r + 1) → O} (hy : y' ∈ headCols (cjT O cj hO Z)) :
    bRaw O cj Z y y' ∈ O := by
  obtain ⟨w, -, rfl⟩ := mem_headCols hy
  rw [bRaw_cjT O cj hcj Z hu y _ (fun a => (w a : E)) (fun b => cjT_mulVec_coe O cj hO Z w b)]
  exact Subring.sum_mem _ fun a _ => Subring.mul_mem _ (hO _ (w a).2) (y a).2

/- English proof (translation)
Simplify using `only [bRaw, lamS, lamStarC, coe_single, Matrix.mulVec_single_one, map_sum, map_mul, hcj, Matrix.transpose_apply]`. Conclude with `Finset.sum_congr rfl fun j _ => mul_comm _ _`.
-/
theorem cj_bRaw_single (hcj : ∀ x, cj (cj x) = x) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O)
    (y' : Fin (r + 1) → O) :
    cj (bRaw O cj Z (Pi.single (Fin.last r) 1) y') = lamS O cj Z y' := by
  simp only [bRaw, lamS, lamStarC, coe_single, Matrix.mulVec_single_one, map_sum, map_mul, hcj,
    Matrix.transpose_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end Formalism.L2.SG.LocalCountModules.UnramifiedPairingLinear
