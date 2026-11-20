import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.BRawHeadColsRight

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

namespace Formalism.L2.SG.LocalCountModules.UnramifiedPairingLinear

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

def cG (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (T T' : E) (Y : Ix r → O) : Ix r → E :=
  Matrix.vecMul (fun j => (Y j : E)) (gramC cj (Z.map O.subtype) T T')⁻¹

section Vec

variable {Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (T T' : E)

/- English proof (translation)
Simplify using `only [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, gramC, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.of_apply, Matrix.transpose_apply]`. Distinguish the cases in `hb : b = Fin.last r`. Substitute `hb` using the available equality. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Simplify using `[hb]`.
-/
theorem vecMul_gramC_inl (x : Ix r → E) (b : Fin (r + 1)) :
    Matrix.vecMul x (gramC cj Z T T') (Sum.inl b) =
      ∑ a, x (Sum.inr a) * Z b a - if b = Fin.last r then T * x (Sum.inl (Fin.last r)) else 0 := by
  simp only [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, gramC, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₂₁, Matrix.of_apply, Matrix.transpose_apply]
  by_cases hb : b = Fin.last r
  · subst hb; simp; ring
  · simp [hb]

/- English proof (translation)
Simplify using `only [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, gramC, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.of_apply]`. Distinguish the cases in `hb : b = Fin.last r`. Substitute `hb` using the available equality. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Simplify using `[hb]`.
-/
theorem vecMul_gramC_inr (x : Ix r → E) (b : Fin (r + 1)) :
    Matrix.vecMul x (gramC cj Z T T') (Sum.inr b) =
      ∑ a, x (Sum.inl a) * cj (Z a b) - if b = Fin.last r then T' * x (Sum.inr (Fin.last r)) else 0 := by
  simp only [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, gramC, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
  by_cases hb : b = Fin.last r
  · subst hb; simp; ring
  · simp [hb]

end Vec

/- English proof (translation)
Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`.
-/
theorem mulVec_single_apply' {Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (j i : Fin (r + 1)) (v : E) :
    Z.mulVec (Pi.single j v) i = Z i j * v := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

section Coord

variable (hcj : ∀ x, cj (cj x) = x) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O)
  (hu : IsUnit (Z.map O.subtype).det) (T T' : E)
  (hG : IsUnit (gramC cj (Z.map O.subtype) T T').det)

include hG in
/- English proof (translation)
Unfold `cG`. Rewrite using `[Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hG, Matrix.vecMul_one]`.
-/
theorem vecMul_cG (Y : Ix r → O) :
    Matrix.vecMul (cG O cj Z T T' Y) (gramC cj (Z.map O.subtype) T T') = fun j => (Y j : E) := by
  unfold cG
  rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hG, Matrix.vecMul_one]

include hG in

/- English proof (translation)
Use function extensionality and compare the values at `b`. Establish `h` using `congrFun (vecMul_cG O cj Z T T' hG Y) (Sum.inl b)`. Rewrite `h` using `[vecMul_gramC_inl]`. Rewrite using `[← h]`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]`.
-/
theorem inl_eq (Y : Ix r → O) :
    (fun j => (Y (Sum.inl j) : E)) = (Z.map O.subtype).mulVec (fun a => cG O cj Z T T' Y (Sum.inr a)) -
      Pi.single (Fin.last r) (T * cG O cj Z T T' Y (Sum.inl (Fin.last r))) := by
  funext b
  have h := congrFun (vecMul_cG O cj Z T T' hG Y) (Sum.inl b)
  rw [vecMul_gramC_inl] at h
  rw [← h]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]

include hG in

/- English proof (translation)
Use function extensionality and compare the values at `b`. Establish `h` using `congrFun (vecMul_cG O cj Z T T' hG Y) (Sum.inr b)`. Rewrite `h` using `[vecMul_gramC_inr]`. Rewrite using `[← h]`. Simplify using `[Pi.single_apply, mul_comm]`.
-/
theorem inr_eq (Y : Ix r → O) :
    (fun j => (Y (Sum.inr j) : E)) =
      (fun b => ∑ a, cj ((Z.map O.subtype) a b) * cG O cj Z T T' Y (Sum.inl a)) -
      Pi.single (Fin.last r) (T' * cG O cj Z T T' Y (Sum.inr (Fin.last r))) := by
  funext b
  have h := congrFun (vecMul_cG O cj Z T T' hG Y) (Sum.inr b)
  rw [vecMul_gramC_inr] at h
  rw [← h]
  simp [Pi.single_apply, mul_comm]

include hu hG in

/- English proof (translation)
Rewrite using `[lamC, inl_eq O cj Z T T' hG Y, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec, Pi.sub_apply, mulVec_single_apply']`.
-/
theorem lam_cG (Y : Ix r → O) :
    lamC (Z.map O.subtype) (fun j => (Y (Sum.inl j) : E)) =
      cG O cj Z T T' Y (Sum.inr (Fin.last r)) -
        (Z.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) * (T * cG O cj Z T T' Y (Sum.inl (Fin.last r))) := by
  rw [lamC, inl_eq O cj Z T T' hG Y, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu,
    Matrix.one_mulVec, Pi.sub_apply, mulVec_single_apply']

include hu hG in

/- English proof (translation)
Rewrite using `[inr_eq O cj Z T T' hG Y]`. Establish `h1` using `lamStarC_mulVec cj (Z.map O.subtype) hu (fun a => cG O cj Z T T' Y (Sum.inl a))`. Simplify using `only [lamStarC, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib] at h1 ⊢`. Rewrite using `[h1]`. Use `congr 1`.

Simplify using `[Pi.single_apply]`.
-/
theorem lamS_cG (Y : Ix r → O) :
    lamStarC cj (Z.map O.subtype) (fun j => (Y (Sum.inr j) : E)) =
      cG O cj Z T T' Y (Sum.inl (Fin.last r)) -
        cj ((Z.map O.subtype)⁻¹ (Fin.last r) (Fin.last r)) * (T' * cG O cj Z T T' Y (Sum.inr (Fin.last r))) := by
  rw [inr_eq O cj Z T T' hG Y]
  have h1 := lamStarC_mulVec cj (Z.map O.subtype) hu (fun a => cG O cj Z T T' Y (Sum.inl a))
  simp only [lamStarC, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib] at h1 ⊢
  rw [h1]
  congr 1
  simp [Pi.single_apply]

include hcj hu hG in

/- English proof (translation)
Use `set Ze := Z.map O.subtype with hZe`. Use `set c := cG O cj Z T T' Y with hc`. Establish `hf : formC O cj Ze T T' Y W = ∑ j, c j * cj (W j : E)`. Simplify using `only [formC, hc, cG, Matrix.vecMul, dotProduct, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.

Establish `hA : ∑ b, c (Sum.inr b) * cj (W (Sum.inr b) : E) = bRaw O cj Z (fun j => Y (Sum.inl j)) (fun j => W (Sum.inr j)) + T * c (Sum.inl (Fin.last r)) * cj (lamStarC cj Ze (fun j => (W (Sum.inr j) : E)))`. Establish `hPy : Ze⁻¹.mulVec (fun j => (Y (Sum.inl j) : E)) = (fun a => c (Sum.inr a)) - Ze⁻¹.mulVec (Pi.single (Fin.last r) (T * c (Sum.inl (Fin.last r))))`. Rewrite using `[inl_eq O cj Z T T' hG Y, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]`. Establish `hB : bRaw O cj Z (fun j => Y (Sum.inl j)) (fun j => W (Sum.inr j)) = ∑ j, cj (W (Sum.inr j) : E) * (c (Sum.inr j) - Ze⁻¹ j (Fin.last r) * (T * c (Sum.inl (Fin.last r))))`. Unfold `bRaw`.

Rewrite using `[← hZe, hPy]`. Simplify using `only [Pi.sub_apply, mulVec_single_apply']`. Establish `hL : cj (lamStarC cj Ze (fun j => (W (Sum.inr j) : E))) = ∑ j, Ze⁻¹ j (Fin.last r) * cj (W (Sum.inr j) : E)`. Simplify using `only [lamStarC, map_sum, map_mul, hcj]`. Rewrite using `[hB, hL, Finset.mul_sum, ← Finset.sum_add_distrib]`.

Conclude with `Finset.sum_congr rfl fun j _ => by ring`. Establish `hB' : ∑ a, c (Sum.inl a) * cj (W (Sum.inl a) : E) = cj (bRaw O cj Z (fun j => W (Sum.inl j)) (fun j => Y (Sum.inr j))) + T' * c (Sum.inr (Fin.last r)) * cj (lamC Ze (fun j => (W (Sum.inl j) : E)))` using `by set pw := Ze⁻¹.mulVec (fun j => (W (Sum.inl j) : E)) with hpw`. Establish `h2 : Ze.mulVec pw = fun j => (W (Sum.inl j) : E)`. Rewrite using `[hpw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]`. Establish `hw : ∀ a, cj (W (Sum.inl a) : E) = ∑ k, cj (Ze a k) * cj (pw k)`.

Introduce `a`. Use `congrFun h2 a` as an intermediate fact. Rewrite using `[← this]`. Simplify using `only [Matrix.mulVec, dotProduct, map_sum, map_mul]`. Establish `hy' : ∀ k, ∑ a, c (Sum.inl a) * cj (Ze a k) = (Y (Sum.inr k) : E) + if k = Fin.last r then T' * c (Sum.inr (Fin.last r)) else 0`.

Introduce `k`. Use `congrFun (inr_eq O cj Z T T' hG Y) k` as an intermediate fact. Simplify using `only [Pi.sub_apply, Pi.single_apply] at this`. Rewrite using `[this, sub_add_cancel]`. Conclude with `Finset.sum_congr rfl fun a _ => mul_comm _ _`.

Establish `hl : lamC Ze (fun j => (W (Sum.inl j) : E)) = pw (Fin.last r)` using `rfl`. Establish `hb : cj (bRaw O cj Z (fun j => W (Sum.inl j)) (fun j => Y (Sum.inr j))) = ∑ k, (Y (Sum.inr k) : E) * cj (pw k)`. Unfold `bRaw`. Rewrite using `[← hZe, ← hpw]`. Simplify using `only [map_sum, map_mul, hcj]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [hw, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => by ring`. Use `_ = ∑ k, cj (pw k) * ((Y (Sum.inr k) : E) + if k = Fin.last r then T' * c (Sum.inr (Fin.last r)) else 0) := by`.

Simplify using `only [hy']`. Use `_ = _ := by`. Rewrite using `[hb, hl]`. Simplify using `only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Use `congr 1`.

Conclude with `Finset.sum_congr rfl fun k _ => mul_comm _ _`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hf, Fintype.sum_sum_type, hA, hB']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem formC_eqG (Y W : Ix r → O) :
    formC O cj (Z.map O.subtype) T T' Y W =
      bRaw O cj Z (fun j => Y (Sum.inl j)) (fun j => W (Sum.inr j)) +
        cj (bRaw O cj Z (fun j => W (Sum.inl j)) (fun j => Y (Sum.inr j))) +
        T' * cG O cj Z T T' Y (Sum.inr (Fin.last r)) *
          cj (lamC (Z.map O.subtype) (fun j => (W (Sum.inl j) : E))) +
        T * cG O cj Z T T' Y (Sum.inl (Fin.last r)) *
          cj (lamStarC cj (Z.map O.subtype) (fun j => (W (Sum.inr j) : E))) := by
  set Ze := Z.map O.subtype with hZe
  set c := cG O cj Z T T' Y with hc
  have hf : formC O cj Ze T T' Y W = ∑ j, c j * cj (W j : E) := by
    simp only [formC, hc, cG, Matrix.vecMul, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]

  have hA : ∑ b, c (Sum.inr b) * cj (W (Sum.inr b) : E) =
      bRaw O cj Z (fun j => Y (Sum.inl j)) (fun j => W (Sum.inr j)) +
        T * c (Sum.inl (Fin.last r)) * cj (lamStarC cj Ze (fun j => (W (Sum.inr j) : E))) := by
    have hPy : Ze⁻¹.mulVec (fun j => (Y (Sum.inl j) : E)) =
        (fun a => c (Sum.inr a)) - Ze⁻¹.mulVec (Pi.single (Fin.last r) (T * c (Sum.inl (Fin.last r)))) := by
      rw [inl_eq O cj Z T T' hG Y, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu,
        Matrix.one_mulVec]
    have hB : bRaw O cj Z (fun j => Y (Sum.inl j)) (fun j => W (Sum.inr j)) =
        ∑ j, cj (W (Sum.inr j) : E) * (c (Sum.inr j) - Ze⁻¹ j (Fin.last r) * (T * c (Sum.inl (Fin.last r)))) := by
      unfold bRaw
      rw [← hZe, hPy]
      simp only [Pi.sub_apply, mulVec_single_apply']
    have hL : cj (lamStarC cj Ze (fun j => (W (Sum.inr j) : E))) =
        ∑ j, Ze⁻¹ j (Fin.last r) * cj (W (Sum.inr j) : E) := by
      simp only [lamStarC, map_sum, map_mul, hcj]
    rw [hB, hL, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring

  have hB' : ∑ a, c (Sum.inl a) * cj (W (Sum.inl a) : E) =
      cj (bRaw O cj Z (fun j => W (Sum.inl j)) (fun j => Y (Sum.inr j))) +
        T' * c (Sum.inr (Fin.last r)) * cj (lamC Ze (fun j => (W (Sum.inl j) : E))) := by
    set pw := Ze⁻¹.mulVec (fun j => (W (Sum.inl j) : E)) with hpw
    have h2 : Ze.mulVec pw = fun j => (W (Sum.inl j) : E) := by
      rw [hpw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
    have hw : ∀ a, cj (W (Sum.inl a) : E) = ∑ k, cj (Ze a k) * cj (pw k) := by
      intro a
      have := congrFun h2 a
      rw [← this]
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
    have hy' : ∀ k, ∑ a, c (Sum.inl a) * cj (Ze a k) =
        (Y (Sum.inr k) : E) + if k = Fin.last r then T' * c (Sum.inr (Fin.last r)) else 0 := by
      intro k
      have := congrFun (inr_eq O cj Z T T' hG Y) k
      simp only [Pi.sub_apply, Pi.single_apply] at this
      rw [this, sub_add_cancel]
      exact Finset.sum_congr rfl fun a _ => mul_comm _ _
    have hl : lamC Ze (fun j => (W (Sum.inl j) : E)) = pw (Fin.last r) := rfl
    have hb : cj (bRaw O cj Z (fun j => W (Sum.inl j)) (fun j => Y (Sum.inr j))) =
        ∑ k, (Y (Sum.inr k) : E) * cj (pw k) := by
      unfold bRaw
      rw [← hZe, ← hpw]
      simp only [map_sum, map_mul, hcj]
    calc ∑ a, c (Sum.inl a) * cj (W (Sum.inl a) : E)
        = ∑ k, cj (pw k) * ∑ a, c (Sum.inl a) * cj (Ze a k) := by
          simp only [hw, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => by ring
      _ = ∑ k, cj (pw k) * ((Y (Sum.inr k) : E) +
            if k = Fin.last r then T' * c (Sum.inr (Fin.last r)) else 0) := by
          simp only [hy']
      _ = _ := by
          rw [hb, hl]
          simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
            Finset.mem_univ, if_true]
          congr 1
          · exact Finset.sum_congr rfl fun k _ => mul_comm _ _
          · ring
  rw [hf, Fintype.sum_sum_type, hA, hB']
  ring

end Coord

section Uniq

variable (hcj : ∀ x, cj (cj x) = x) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O)
  (hu : IsUnit (Z.map O.subtype).det) (T T' : E)
  (hG : IsUnit (gramC cj (Z.map O.subtype) T T').det)

include hcj hu hG in

/- English proof (translation)
Use `set Ze := Z.map O.subtype with hZe`. Use `set P := Ze⁻¹ with hP`. Set `c : Ix r → E` to `Sum.elim (fun a => cj (P (Fin.last r) a) * (T' * d)) (fun a => P a (Fin.last r) * (T * d'))`. Establish `hZP : Ze * P = 1` using `Matrix.mul_nonsing_inv _ hu`. Establish `hPZ : P * Ze = 1` using `Matrix.nonsing_inv_mul _ hu`.

Establish `hc0 : Matrix.vecMul c (gramC cj Ze T T') = 0`. Use function extensionality and compare the values at `i`. Break down `i with b | b` into its components or cases. Rewrite using `[vecMul_gramC_inl]`. Establish `e1` using `congrFun (congrFun hZP b) (Fin.last r)`.

Rewrite `e1` using `[Matrix.mul_apply, Matrix.one_apply]`. Establish `: ∑ a, c (Sum.inr a) * Ze b a = (∑ a, Ze b a * P a (Fin.last r)) * (T * d')`. Rewrite using `[Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun a _ => by simp only [c, Sum.elim_inr]; ring`. Rewrite using `[this, e1]`.

Simplify using `only [c, Sum.elim_inl, Pi.zero_apply]`. Distinguish the cases in `hb : b = Fin.last r`. Simplify using `only [hb, if_true]`. Rewrite using `[h2]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `[hb]`. Rewrite using `[vecMul_gramC_inr]`. Establish `e1` using `congrFun (congrFun hPZ (Fin.last r)) b`. Rewrite `e1` using `[Matrix.mul_apply, Matrix.one_apply]`. Establish `: ∑ a, c (Sum.inl a) * cj (Ze a b) = cj (∑ a, P (Fin.last r) a * Ze a b) * (T' * d)`.

Rewrite using `[map_sum, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun a _ => by simp only [c, Sum.elim_inl, map_mul]; ring`. Rewrite using `[this, e1]`. Simplify using `only [c, Sum.elim_inr, Pi.zero_apply]`. Distinguish the cases in `hb : b = Fin.last r`.

Simplify using `only [hb, if_true, map_one]`. Rewrite using `[h1]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[hb, Ne.symm hb]`. Establish `hc : c = 0`.

Establish `: c = Matrix.vecMul (Matrix.vecMul c (gramC cj Ze T T')) (gramC cj Ze T T')⁻¹`. Rewrite using `[Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hG, Matrix.vecMul_one]`. Rewrite using `[this, hc0, Matrix.zero_vecMul]`. Establish `ed : d = c (Sum.inr (Fin.last r))` using `by simp only [c, Sum.elim_inr]; rw [h1]`. Establish `ed' : d' = c (Sum.inl (Fin.last r))` using `by simp only [c, Sum.elim_inl]; rw [h2]`.

Rewrite `ed`, `ed'` using `[hc]`. Conclude with `⟨ed, ed'⟩`.
-/
theorem uniq_core (d d' : E)
    (h1 : d = (Z.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) * (T * d'))
    (h2 : d' = cj ((Z.map O.subtype)⁻¹ (Fin.last r) (Fin.last r)) * (T' * d)) :
    d = 0 ∧ d' = 0 := by
  set Ze := Z.map O.subtype with hZe
  set P := Ze⁻¹ with hP
  let c : Ix r → E := Sum.elim (fun a => cj (P (Fin.last r) a) * (T' * d)) (fun a => P a (Fin.last r) * (T * d'))
  have hZP : Ze * P = 1 := Matrix.mul_nonsing_inv _ hu
  have hPZ : P * Ze = 1 := Matrix.nonsing_inv_mul _ hu
  have hc0 : Matrix.vecMul c (gramC cj Ze T T') = 0 := by
    funext i
    rcases i with b | b
    · rw [vecMul_gramC_inl]
      have e1 := congrFun (congrFun hZP b) (Fin.last r)
      rw [Matrix.mul_apply, Matrix.one_apply] at e1
      have : ∑ a, c (Sum.inr a) * Ze b a = (∑ a, Ze b a * P a (Fin.last r)) * (T * d') := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _ => by simp only [c, Sum.elim_inr]; ring
      rw [this, e1]
      simp only [c, Sum.elim_inl, Pi.zero_apply]
      by_cases hb : b = Fin.last r
      · simp only [hb, if_true]
        rw [h2]; ring
      · simp [hb]
    · rw [vecMul_gramC_inr]
      have e1 := congrFun (congrFun hPZ (Fin.last r)) b
      rw [Matrix.mul_apply, Matrix.one_apply] at e1
      have : ∑ a, c (Sum.inl a) * cj (Ze a b) = cj (∑ a, P (Fin.last r) a * Ze a b) * (T' * d) := by
        rw [map_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _ => by simp only [c, Sum.elim_inl, map_mul]; ring
      rw [this, e1]
      simp only [c, Sum.elim_inr, Pi.zero_apply]
      by_cases hb : b = Fin.last r
      · simp only [hb, if_true, map_one]
        rw [h1]; ring
      · simp [hb, Ne.symm hb]
  have hc : c = 0 := by
    have : c = Matrix.vecMul (Matrix.vecMul c (gramC cj Ze T T')) (gramC cj Ze T T')⁻¹ := by
      rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hG, Matrix.vecMul_one]
    rw [this, hc0, Matrix.zero_vecMul]
  have ed : d = c (Sum.inr (Fin.last r)) := by simp only [c, Sum.elim_inr]; rw [h1]
  have ed' : d' = c (Sum.inl (Fin.last r)) := by simp only [c, Sum.elim_inl]; rw [h2]
  rw [hc] at ed ed'
  exact ⟨ed, ed'⟩

include hcj hu hG in
/- English proof (translation)
Use `set κ := (Z.map O.subtype)⁻¹ (Fin.last r) (Fin.last r)`. Use `(uniq_core O cj hcj Z hu T T' hG (κ * (T * u)) u rfl ?_).2` and prove the remaining obligations. Take the linear combination `h`.
-/
theorem eta_nzd (u : E)
    (h : (1 - T * T' * ((Z.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) *
      cj ((Z.map O.subtype)⁻¹ (Fin.last r) (Fin.last r)))) * u = 0) : u = 0 := by
  set κ := (Z.map O.subtype)⁻¹ (Fin.last r) (Fin.last r)
  refine (uniq_core O cj hcj Z hu T T' hG (κ * (T * u)) u rfl ?_).2
  linear_combination h

end Uniq

/- English proof (translation)
Rewrite `hl` using `[lam_cG O cj Z₂ hu₂ T T' hG₂, lam_cG O cj Z₁ hu₁ T T' hG₁, ← hκ]`. Rewrite `hl'` using `[lamS_cG O cj Z₂ hu₂ T T' hG₂, lamS_cG O cj Z₁ hu₁ T T' hG₁, ← hκ]`. Take `⟨h1, h2⟩` from `uniq_core O cj hcj Z₂ hu₂ T T' hG₂ (cG O cj Z₂ T T' Y₂ (Sum.inr (Fin.last r)) - cG O cj Z₁ T T' Y₁ (Sum.inr (Fin.last r))) (cG O cj Z₂ T T' Y₂ (Sum.inl (Fin.last r)) - cG O cj Z₁ T T' Y₁ (Sum.inl (Fin.last r))) (by linear_combination hl) (by linear_combination hl')`. Conclude with `⟨sub_eq_zero.1 h2, sub_eq_zero.1 h1⟩`.
-/
theorem cG_transfer (hcj : ∀ x, cj (cj x) = x) (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O)
    (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det) (T T' : E)
    (hG₁ : IsUnit (gramC cj (Z₁.map O.subtype) T T').det)
    (hG₂ : IsUnit (gramC cj (Z₂.map O.subtype) T T').det)
    (hκ : (Z₂.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = (Z₁.map O.subtype)⁻¹ (Fin.last r) (Fin.last r))
    (Y₁ Y₂ : Ix r → O)
    (hl : lamC (Z₂.map O.subtype) (fun j => (Y₂ (Sum.inl j) : E)) =
      lamC (Z₁.map O.subtype) (fun j => (Y₁ (Sum.inl j) : E)))
    (hl' : lamStarC cj (Z₂.map O.subtype) (fun j => (Y₂ (Sum.inr j) : E)) =
      lamStarC cj (Z₁.map O.subtype) (fun j => (Y₁ (Sum.inr j) : E))) :
    cG O cj Z₂ T T' Y₂ (Sum.inl (Fin.last r)) = cG O cj Z₁ T T' Y₁ (Sum.inl (Fin.last r)) ∧
      cG O cj Z₂ T T' Y₂ (Sum.inr (Fin.last r)) = cG O cj Z₁ T T' Y₁ (Sum.inr (Fin.last r)) := by
  rw [lam_cG O cj Z₂ hu₂ T T' hG₂, lam_cG O cj Z₁ hu₁ T T' hG₁, ← hκ] at hl
  rw [lamS_cG O cj Z₂ hu₂ T T' hG₂, lamS_cG O cj Z₁ hu₁ T T' hG₁, ← hκ] at hl'
  obtain ⟨h1, h2⟩ := uniq_core O cj hcj Z₂ hu₂ T T' hG₂
    (cG O cj Z₂ T T' Y₂ (Sum.inr (Fin.last r)) - cG O cj Z₁ T T' Y₁ (Sum.inr (Fin.last r)))
    (cG O cj Z₂ T T' Y₂ (Sum.inl (Fin.last r)) - cG O cj Z₁ T T' Y₁ (Sum.inl (Fin.last r)))
    (by linear_combination hl) (by linear_combination hl')
  exact ⟨sub_eq_zero.1 h2, sub_eq_zero.1 h1⟩

end Formalism.L2.SG.LocalCountModules.UnramifiedPairingLinear
