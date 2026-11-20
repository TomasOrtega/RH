import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjLowUni
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LowerUnipotentConjBlockFormulas

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

noncomputable section

namespace GlobalTheory.SchurExt.AdBridge

section Maps

variable {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m r : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Aof_map (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Aof (M.map f) = (Aof M).map f := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Bof_map (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Bof (M.map f) = (Bof M).map f := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Cof_map (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Cof (M.map f) = (Cof M).map f := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Dof_map (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Dof (M.map f) = (Dof M).map f := rfl

/- English proof (translation)
Use `symm`. Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Rewrite using `[← Matrix.map_mul, Matrix.nonsing_inv_mul A h, Matrix.map_one f (map_zero f) (map_one f)]`.
-/
theorem inv_map_of_isUnit {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (h : IsUnit A.det) :
    (A⁻¹).map f = (A.map f)⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul A h, Matrix.map_one f (map_zero f) (map_one f)]

/- English proof (translation)
Rewrite using `[Yof, Yof, Matrix.map_mul, Dof_map, Cof_map, inv_map_of_isUnit f _ h]`.
-/
theorem Yof_map (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : IsUnit (Dof M).det) :
    Yof (M.map f) = (Yof M).map f := by
  rw [Yof, Yof, Matrix.map_mul, Dof_map, Cof_map, inv_map_of_isUnit f _ h]

/- English proof (translation)
Rewrite using `[Xof, Xof, Matrix.map_mul, Dof_map, Bof_map, inv_map_of_isUnit f _ h]`.
-/
theorem Xof_map (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : IsUnit (Dof M).det) :
    Xof (M.map f) = (Xof M).map f := by
  rw [Xof, Xof, Matrix.map_mul, Dof_map, Bof_map, inv_map_of_isUnit f _ h]

/- English proof (translation)
Rewrite using `[Scof, Scof, Matrix.map_sub _ (map_sub f), Matrix.map_mul, Matrix.map_mul, Aof_map, Dof_map, Bof_map, Cof_map, inv_map_of_isUnit f _ h]`.
-/
theorem Scof_map (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : IsUnit (Dof M).det) :
    Scof (M.map f) = (Scof M).map f := by
  rw [Scof, Scof, Matrix.map_sub _ (map_sub f), Matrix.map_mul, Matrix.map_mul, Aof_map, Dof_map, Bof_map, Cof_map,
    inv_map_of_isUnit f _ h]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [lowUni, unblk, Matrix.map_apply, Matrix.submatrix_apply]`. Apply the tactic sequence `rcases (eqv m r i) with a | a <;> rcases (eqv m r j) with b | b <;>`. Simplify using `[Matrix.one_apply, apply_ite f]`.
-/
theorem lowUni_map (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) :
    (lowUni Y).map f = lowUni (Y.map f) := by
  ext i j
  simp only [lowUni, unblk, Matrix.map_apply, Matrix.submatrix_apply]
  rcases (eqv m r i) with a | a <;> rcases (eqv m r j) with b | b <;>
    simp [Matrix.one_apply, apply_ite f]

/- English proof (translation)
Rewrite using `[conjLowUni, conjLowUni, Matrix.map_mul, Matrix.map_mul, lowUni_map, lowUni_map, Matrix.map_neg _ (map_neg f)]`.
-/
theorem conjLowUni_map (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) :
    (conjLowUni Y k).map f = conjLowUni (Y.map f) (k.map f) := by
  rw [conjLowUni, conjLowUni, Matrix.map_mul, Matrix.map_mul, lowUni_map, lowUni_map, Matrix.map_neg _ (map_neg f)]

end Maps

section Ones

variable {R : Type} [CommRing R] {m r : ℕ}

/- English proof (translation)
Simplify using `[blk]`.
-/
theorem blk_one : blk (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 1 := by
  simp [blk]

/- English proof (translation)
Rewrite using `[Aof, blk_one, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₁]`.
-/
theorem Aof_one : Aof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 1 := by
  rw [Aof, blk_one, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₁]
/- English proof (translation)
Rewrite using `[Bof, blk_one, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₂]`.
-/
theorem Bof_one : Bof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 0 := by
  rw [Bof, blk_one, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₂]
/- English proof (translation)
Rewrite using `[Cof, blk_one, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₂₁]`.
-/
theorem Cof_one : Cof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 0 := by
  rw [Cof, blk_one, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₂₁]
/- English proof (translation)
Rewrite using `[Dof, blk_one, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₂₂]`.
-/
theorem Dof_one : Dof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 1 := by
  rw [Dof, blk_one, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₂₂]
/- English proof (translation)
Rewrite using `[Yof, Cof_one, Matrix.mul_zero]`.
-/
theorem Yof_one : Yof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 0 := by
  rw [Yof, Cof_one, Matrix.mul_zero]
/- English proof (translation)
Rewrite using `[Xof, Bof_one, Matrix.zero_mul]`.
-/
theorem Xof_one : Xof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 0 := by
  rw [Xof, Bof_one, Matrix.zero_mul]
/- English proof (translation)
Rewrite using `[Scof, Aof_one, Bof_one, Cof_one]`. Simplify using the standard rewrite rules.
-/
theorem Scof_one : Scof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 1 := by
  rw [Scof, Aof_one, Bof_one, Cof_one]; simp

/- English proof (translation)
The claim follows from `Matrix.submatrix_mul_equiv _ _ _ _ _`.
-/
theorem unblk_mul (P Q : Matrix (Fin (m + 1) ⊕ Fin (r + 1)) (Fin (m + 1) ⊕ Fin (r + 1)) R) :
    unblk P * unblk Q = unblk (P * Q) := Matrix.submatrix_mul_equiv _ _ _ _ _

/- English proof (translation)
Simplify using `[unblk]`.
-/
theorem unblk_one : unblk (1 : Matrix (Fin (m + 1) ⊕ Fin (r + 1)) (Fin (m + 1) ⊕ Fin (r + 1)) R) = 1 := by
  simp [unblk]

/- English proof (translation)
Rewrite using `[lowUni, lowUni, unblk_mul, Matrix.fromBlocks_multiply]`. Simplify using `[unblk_one]`.
-/
theorem lowUni_mul_neg (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) : lowUni Y * lowUni (-Y) = 1 := by
  rw [lowUni, lowUni, unblk_mul, Matrix.fromBlocks_multiply]
  simp [unblk_one]

/- English proof (translation)
Rewrite using `[conjLowUni, Matrix.mul_one, lowUni_mul_neg]`.
-/
theorem conjLowUni_one (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) : conjLowUni Y 1 = 1 := by
  rw [conjLowUni, Matrix.mul_one, lowUni_mul_neg]

/- English proof (translation)
Rewrite using `[lowUni, unblk, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₁₂]`. Simplify using the standard rewrite rules.
-/
theorem det_lowUni (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) : (lowUni (m := m) Y).det = 1 := by
  rw [lowUni, unblk, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₁₂]; simp

/- English proof (translation)
Rewrite using `[conjLowUni, Matrix.det_mul, Matrix.det_mul, det_lowUni, det_lowUni]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_conjLowUni (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) :
    (conjLowUni Y k).det = k.det := by
  rw [conjLowUni, Matrix.det_mul, Matrix.det_mul, det_lowUni, det_lowUni]; ring

/- English proof (translation)
Use `letI := Matrix.invertibleOfIsUnitDet _ h`. Establish `e : Matrix.fromBlocks (Aof M) (Bof M) (Cof M) (Dof M) = blk M` using `Matrix.fromBlocks_toBlocks _`. Establish `h1 : M.det = (blk M).det` using `by rw [blk, Matrix.det_submatrix_equiv_self]`. Rewrite using `[h1, ← e, Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]`. Both sides reduce to the same expression.
-/
theorem det_eq_det_Dof_mul (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : IsUnit (Dof M).det) :
    M.det = (Dof M).det * (Scof M).det := by
  letI := Matrix.invertibleOfIsUnitDet _ h
  have e : Matrix.fromBlocks (Aof M) (Bof M) (Cof M) (Dof M) = blk M := Matrix.fromBlocks_toBlocks _
  have h1 : M.det = (blk M).det := by rw [blk, Matrix.det_submatrix_equiv_self]
  rw [h1, ← e, Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]; rfl

/- English proof (translation)
Rewrite `hM` using `[det_eq_det_Dof_mul M h]`. Conclude with `isUnit_of_mul_isUnit_right hM`.
-/
theorem isUnit_det_Scof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (hM : IsUnit M.det)
    (h : IsUnit (Dof M).det) : IsUnit (Scof M).det := by
  rw [det_eq_det_Dof_mul M h] at hM
  exact isUnit_of_mul_isUnit_right hM

end Ones

section Adeles

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

/- English proof (translation)
The claim follows from `map_zero (infEq E).symm`.
-/
theorem pInf_sFin_eq_zero (b : Af E) : pInf E (sFin E b) = 0 := map_zero (infEq E).symm

omit [IsTotallyComplex E] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pFin_sFin_eq (b : Af E) : pFin E (sFin E b) = b := rfl

/- English proof (translation)
Use `Prod.isUnit_iff.2 ⟨?_, h2⟩` and prove the remaining obligations. Establish `e : (infEq E) (pInf E x) = x.1` using `(infEq E).apply_symm_apply x.1`. Rewrite using `[← e]`. Conclude with `h1.map _`.
-/
theorem isUnit_of_parts {x : Ad E} (h1 : IsUnit (pInf E x)) (h2 : IsUnit (pFin E x)) : IsUnit x := by
  refine Prod.isUnit_iff.2 ⟨?_, h2⟩
  have e : (infEq E) (pInf E x) = x.1 := (infEq E).apply_symm_apply x.1
  rw [← e]; exact h1.map _

/- English proof (translation)
The claim follows from `congrArg (fun g : GL (Fin n) (Cinf E) => (g : Matrix (Fin n) (Fin n) (Cinf E))) (pInf_finGL k)`.
-/
theorem map_pInf_finGL {n : ℕ} (k : GL (Fin n) (Af E)) :
    (finGL E n k : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E) = 1 :=
  congrArg (fun g : GL (Fin n) (Cinf E) => (g : Matrix (Fin n) (Fin n) (Cinf E))) (pInf_finGL k)

omit [IsTotallyComplex E] in
/- English proof (translation)
The claim follows from `congrArg (fun g : GL (Fin n) (Af E) => (g : Matrix (Fin n) (Fin n) (Af E))) (pFin_finGL k)`.
-/
theorem map_pFin_finGL {n : ℕ} (k : GL (Fin n) (Af E)) :
    (finGL E n k : Matrix (Fin n) (Fin n) (Ad E)).map (pFin E) = (k : Matrix (Fin n) (Fin n) (Af E)) :=
  congrArg (fun g : GL (Fin n) (Af E) => (g : Matrix (Fin n) (Fin n) (Af E))) (pFin_finGL k)

/- English proof (translation)
Establish `hu' : IsUnit (M.map (pFin E)).det`. Establish `h` using `hu.map (pFin E)`. Rewrite `h` using `[RingHom.map_det]`. Then use the resulting hypothesis. Use extensionality with `i j`. Use `ad_ext ?_ ?_` and prove the remaining obligations.

Conclude with `congrFun (congrFun ((map_pInf_finGL _).trans hi.symm) i) j`. Conclude with `congrFun (congrFun ((map_pFin_finGL _).trans (coe_mkGL hu')) i) j`.
-/
theorem coe_finGL_mkGL {n : ℕ} (M : Matrix (Fin n) (Fin n) (Ad E)) (hi : M.map (pInf E) = 1) (hu : IsUnit M.det) :
    (finGL E n (mkGL (M.map (pFin E))) : Matrix (Fin n) (Fin n) (Ad E)) = M := by
  have hu' : IsUnit (M.map (pFin E)).det := by
    have h := hu.map (pFin E)
    rwa [RingHom.map_det] at h
  ext i j
  refine ad_ext ?_ ?_
  · exact congrFun (congrFun ((map_pInf_finGL _).trans hi.symm) i) j
  · exact congrFun (congrFun ((map_pFin_finGL _).trans (coe_mkGL hu')) i) j

end Adeles

/- English proof (translation)
Introduce `E _ _ _ m r x k hD hD'`. Rewrite using `[Units.val_mul]`. Establish `hx : IsUnit (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).det` using `(Matrix.isUnit_iff_isUnit_det _).1 x.isUnit`. Establish `hK : IsUnit (finGL E (m + r + 1 + 1) k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).det` using `(Matrix.isUnit_iff_isUnit_det _).1 (finGL E (m + r + 1 + 1) k).isUnit`. Establish `hKi` using `map_pInf_finGL (E := E) k`.

Establish `hKf` using `map_pFin_finGL (E := E) k`. Generalize the expression as in `(finGL E (m + r + 1 + 1) k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) = K at *`. Generalize the expression as in `(x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) = g at *`. Establish `hf : conjLowUni ((Yof g).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)) = (conjLowUni (Yof g) K).map (pFin E)` using `by rw [conjLowUni_map, hKf]`. Establish `hi : (conjLowUni (Yof g) K).map (pInf E) = 1` using `by rw [conjLowUni_map, hKi, conjLowUni_one]`.

Establish `hdet : IsUnit (conjLowUni (Yof g) K).det` using `by rwa [det_conjLowUni]`. Rewrite `hD'`, the goal using `[hf]`. Establish `alg` using `GlobalTheory.T.lower_unipotent_conj_block_formulas (Ad E) m r g K hD`. Generalize the expression as in `conjLowUni (Yof g) K = L at *`. Establish `hDi : (Dof L).map (pInf E) = 1` using `by rw [← Dof_map, hi, Dof_one]`.

Establish `hDL : IsUnit (Dof L).det`. Use `isUnit_of_parts ?_ ?_` and prove the remaining obligations. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, hDi, Matrix.det_one]`. Conclude with `isUnit_one`. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, ← Dof_map]`.

Conclude with `hD'`. Take `⟨a1, a2, a3, a4, a5⟩` from `alg hDL`. Establish `hS` using `isUnit_det_Scof g hx hD`. Establish `hSL` using `isUnit_det_Scof L hdet hDL`. Establish `hSi : (Scof L).map (pInf E) = 1` using `by rw [← Scof_map _ _ hDL, hi, Scof_one]`.

Establish `hYi : (Yof L).map (pInf E) = 0` using `by rw [← Yof_map _ _ hDL, hi, Yof_one]`. Establish `hXi : (Xof L).map (pInf E) = 0` using `by rw [← Xof_map _ _ hDL, hi, Xof_one]`. Establish `hXi' : ∀ j l, pInf E (Xof L j l) = 0` using `fun j l => congrFun (congrFun hXi j) l`. Use `⟨hS, a1, Units.ext ?_, Units.ext ?_, fun i j => ?_, fun i j => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[coe_mkGL a1, Units.val_mul, coe_mkGL hD, Dof_map, coe_finGL_mkGL _ hDi hDL, a2]`.

Establish `hSgK : IsUnit (Scof (g * K)).det` using `by rw [a4, Matrix.det_mul]; exact hS.mul hSL`. Rewrite using `[coe_mkGL hSgK, Units.val_mul, coe_mkGL hS, Scof_map _ _ hDL, coe_finGL_mkGL _ hSi hSL, a4]`. Establish `h0 : pInf E (Yof L i j) = 0` using `congrFun (congrFun hYi i) j`. Rewrite using `[a3, Matrix.add_apply, map_add, h0, add_zero]`. Rewrite using `[a3, Matrix.add_apply, map_add, Yof_map _ _ hDL, Matrix.map_apply]`.

Rewrite using `[a5, Matrix.add_apply, Xof_map _ _ hDL]`. Use `congr 1`. Use `ad_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[pInf_sFin_eq_zero]`. Simplify using `only [Matrix.mul_apply, map_sum, map_mul, hXi', mul_zero, Finset.sum_const_zero, zero_mul]`.

Rewrite using `[pFin_sFin_eq, Finset.sum_comm]`. Simplify using `only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul, Matrix.map_apply]`.
-/
theorem schur_data_mul_finGL : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m r : ℕ) (x : GA E (m + r + 1 + 1)) (k : GL (Fin (m + r + 1 + 1)) (Af E)), IsUnit (Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det → IsUnit (Dof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))).det → IsUnit (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det ∧ IsUnit (Dof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det ∧ mkGL (Dof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) = mkGL (Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) * finGL E (r + 1) (mkGL (Dof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))))) ∧ mkGL (Scof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) = mkGL (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) * finGL E (m + 1) (mkGL (Scof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))))) ∧ (∀ i j, pInf E (Yof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) = pInf E (Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j)) ∧ (∀ i j, pFin E (Yof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) = pFin E (Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) + Yof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) i j) ∧ Xof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (Fin.last m) 0 = Xof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (Fin.last m) 0 + sFin E (∑ j, ∑ l, pFin E (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (Fin.last m) j) * Xof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) j l * pFin E ((Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)))⁻¹ l 0)) := by
  intro E _ _ _ m r x k hD hD'
  rw [Units.val_mul]
  have hx : IsUnit (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 x.isUnit
  have hK : IsUnit (finGL E (m + r + 1 + 1) k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (finGL E (m + r + 1 + 1) k).isUnit
  have hKi := map_pInf_finGL (E := E) k
  have hKf := map_pFin_finGL (E := E) k
  generalize (finGL E (m + r + 1 + 1) k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) = K at *
  generalize (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) = g at *
  have hf : conjLowUni ((Yof g).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)) =
      (conjLowUni (Yof g) K).map (pFin E) := by rw [conjLowUni_map, hKf]
  have hi : (conjLowUni (Yof g) K).map (pInf E) = 1 := by rw [conjLowUni_map, hKi, conjLowUni_one]
  have hdet : IsUnit (conjLowUni (Yof g) K).det := by rwa [det_conjLowUni]
  rw [hf] at hD' ⊢
  have alg := GlobalTheory.T.lower_unipotent_conj_block_formulas (Ad E) m r g K hD
  generalize conjLowUni (Yof g) K = L at *
  have hDi : (Dof L).map (pInf E) = 1 := by rw [← Dof_map, hi, Dof_one]
  have hDL : IsUnit (Dof L).det := by
    refine isUnit_of_parts ?_ ?_
    · rw [RingHom.map_det, RingHom.mapMatrix_apply, hDi, Matrix.det_one]; exact isUnit_one
    · rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Dof_map]; exact hD'
  obtain ⟨a1, a2, a3, a4, a5⟩ := alg hDL
  have hS := isUnit_det_Scof g hx hD
  have hSL := isUnit_det_Scof L hdet hDL
  have hSi : (Scof L).map (pInf E) = 1 := by rw [← Scof_map _ _ hDL, hi, Scof_one]
  have hYi : (Yof L).map (pInf E) = 0 := by rw [← Yof_map _ _ hDL, hi, Yof_one]
  have hXi : (Xof L).map (pInf E) = 0 := by rw [← Xof_map _ _ hDL, hi, Xof_one]
  have hXi' : ∀ j l, pInf E (Xof L j l) = 0 := fun j l => congrFun (congrFun hXi j) l
  refine ⟨hS, a1, Units.ext ?_, Units.ext ?_, fun i j => ?_, fun i j => ?_, ?_⟩
  · rw [coe_mkGL a1, Units.val_mul, coe_mkGL hD, Dof_map, coe_finGL_mkGL _ hDi hDL, a2]
  · have hSgK : IsUnit (Scof (g * K)).det := by rw [a4, Matrix.det_mul]; exact hS.mul hSL
    rw [coe_mkGL hSgK, Units.val_mul, coe_mkGL hS, Scof_map _ _ hDL, coe_finGL_mkGL _ hSi hSL, a4]
  · have h0 : pInf E (Yof L i j) = 0 := congrFun (congrFun hYi i) j
    rw [a3, Matrix.add_apply, map_add, h0, add_zero]
  · rw [a3, Matrix.add_apply, map_add, Yof_map _ _ hDL, Matrix.map_apply]
  · rw [a5, Matrix.add_apply, Xof_map _ _ hDL]
    congr 1
    refine ad_ext ?_ ?_
    · rw [pInf_sFin_eq_zero]
      simp only [Matrix.mul_apply, map_sum, map_mul, hXi', mul_zero, Finset.sum_const_zero, zero_mul]
    · rw [pFin_sFin_eq, Finset.sum_comm]
      simp only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul, Matrix.map_apply]

end GlobalTheory.SchurExt.AdBridge
