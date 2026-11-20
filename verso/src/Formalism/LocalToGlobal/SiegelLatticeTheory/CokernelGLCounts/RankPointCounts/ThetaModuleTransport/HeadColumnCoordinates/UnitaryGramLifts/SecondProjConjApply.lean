import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.FirstProjConjApply
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.DetAddCor

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

section DuU3

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

def duU_P (r : ℕ) (x : F) : Matrix (Ix r) (Ix r) F := Matrix.fromBlocks 1 (-x • 1) 0 (x • 1)

def duU_Gh (r : ℕ) (A B : Matrix (Fin (r + 1)) (Fin (r + 1)) F) (T T' : F) : Matrix (Ix r) (Ix r) F :=
  Matrix.fromBlocks (Matrix.of fun a b => cor r a b (-T)) A B.transpose (Matrix.of fun a b => cor r a b (-T'))

/- English proof (translation)
The claim follows from `secondProj_conj_eq_firstProj x`.
-/
theorem secondProj_conj_apply (x : E) : ph2 g (M.L.cj x) = ph1 g x := secondProj_conj_eq_firstProj x

/- English proof (translation)
Apply the tactic sequence `ext (a | a) (b | b) <;>`. Apply the tactic sequence `simp [gramG, duU_Gh, duU_P, cor, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, hφ, hφa, Matrix.mul_apply, Matrix.one_apply, Matrix.smul_apply, Finset.sum_ite_eq, Finset.sum_ite_eq', apply_ite φ] <;>`. Apply the tactic sequence `split_ifs <;> ring`.
-/
theorem duU_map_gramG (φ ψ : E →+* F) (hφ : ∀ x, φ (M.L.cj x) = ψ x) (hφa : ∀ a : F, φ (algebraMap F E a) = a)
    (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' q : F) :
    (gramG (M.L.cj : E →+* E) (algebraMap F E q⁻¹) Zh (algebraMap F E T) (algebraMap F E T')).map φ =
      (duU_P r q⁻¹).transpose * duU_Gh r (Zh.map ψ) (Zh.map φ) T T' * duU_P r q⁻¹ := by
  ext (a | a) (b | b) <;>
    simp [gramG, duU_Gh, duU_P, cor, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, hφ, hφa,
      Matrix.mul_apply, Matrix.one_apply, Matrix.smul_apply, Finset.sum_ite_eq, Finset.sum_ite_eq', apply_ite φ] <;>
    split_ifs <;> ring

/- English proof (translation)
Simplify using `[duU_P, Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul]`.
-/
theorem duU_det_P (x : F) : (duU_P r x).det = x ^ (r + 1) := by
  simp [duU_P, Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul]

/- English proof (translation)
Rewrite using `[Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]`. Simplify using the standard rewrite rules.
-/
theorem duU_inv_last (A : Matrix (Fin (r + 1)) (Fin (r + 1)) F) :
    A⁻¹ (Fin.last r) (Fin.last r) = Ring.inverse A.det * (A.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]
  simp

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Matrix.mul_apply, Matrix.of_apply, cor]`. Apply the tactic sequence `by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r <;>`. Simplify using `[ha, hb, Finset.sum_ite_eq', Finset.sum_ite_eq]`.
-/
theorem duU_cor_mul_cor (N : Matrix (Fin (r + 1)) (Fin (r + 1)) F) (s t : F) :
    (Matrix.of fun a b => cor r a b s) * N * (Matrix.of fun a b => cor r a b t) =
      Matrix.of fun a b => cor r a b (s * N (Fin.last r) (Fin.last r) * t) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.of_apply, cor]
  by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r <;>
    simp [ha, hb, Finset.sum_ite_eq', Finset.sum_ite_eq]

/- English proof (translation)
Use `haveI : Invertible A := Matrix.invertibleOfIsUnitDet A (isUnit_iff_ne_zero.2 hA)`. Establish `hS : duU_Gh r A B T T' * Matrix.fromBlocks 0 1 1 0 = Matrix.fromBlocks A (Matrix.of fun a b => cor r a b (-T)) (Matrix.of fun a b => cor r a b (-T')) B.transpose`. Simplify using `[duU_Gh, Matrix.fromBlocks_multiply]`. Establish `hdet : (duU_Gh r A B T T' * Matrix.fromBlocks 0 1 1 0).det = A.det * B.det - T * T' * ((A.submatrix Fin.castSucc Fin.castSucc).det * (B.submatrix Fin.castSucc Fin.castSucc).det)`. Rewrite using `[hS, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv, duU_cor_mul_cor]`.

Establish `hc : B.transpose - (Matrix.of fun a b => cor r a b (-T' * A⁻¹ (Fin.last r) (Fin.last r) * -T)) = B.transpose + Matrix.of fun a b => cor r a b (-(T' * A⁻¹ (Fin.last r) (Fin.last r) * T))`. Apply the tactic sequence `ext a b; simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.of_apply, cor]; split_ifs <;> ring`. Rewrite using `[hc, det_add_cor, Matrix.det_transpose, duU_inv_last, Ring.inverse_eq_inv']`. Establish `: (B.transpose.submatrix Fin.castSucc Fin.castSucc) = (B.submatrix Fin.castSucc Fin.castSucc).transpose`. Use extensionality with `a b`.

Both sides reduce to the same expression. Rewrite using `[this, Matrix.det_transpose]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Introduce `h0`.

Apply `h` to reduce the goal to its premises. Rewrite using `[← hdet, Matrix.det_mul, h0, zero_mul]`.
-/
theorem duU_det_Gh (A B : Matrix (Fin (r + 1)) (Fin (r + 1)) F) (T T' : F) (hA : A.det ≠ 0)
    (h : A.det * B.det - T * T' * ((A.submatrix Fin.castSucc Fin.castSucc).det *
      (B.submatrix Fin.castSucc Fin.castSucc).det) ≠ 0) :
    (duU_Gh r A B T T').det ≠ 0 := by
  haveI : Invertible A := Matrix.invertibleOfIsUnitDet A (isUnit_iff_ne_zero.2 hA)
  have hS : duU_Gh r A B T T' * Matrix.fromBlocks 0 1 1 0 =
      Matrix.fromBlocks A (Matrix.of fun a b => cor r a b (-T)) (Matrix.of fun a b => cor r a b (-T')) B.transpose := by
    simp [duU_Gh, Matrix.fromBlocks_multiply]
  have hdet : (duU_Gh r A B T T' * Matrix.fromBlocks 0 1 1 0).det =
      A.det * B.det - T * T' * ((A.submatrix Fin.castSucc Fin.castSucc).det *
        (B.submatrix Fin.castSucc Fin.castSucc).det) := by
    rw [hS, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv, duU_cor_mul_cor]
    have hc : B.transpose - (Matrix.of fun a b => cor r a b (-T' * A⁻¹ (Fin.last r) (Fin.last r) * -T)) =
        B.transpose + Matrix.of fun a b => cor r a b (-(T' * A⁻¹ (Fin.last r) (Fin.last r) * T)) := by
      ext a b; simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.of_apply, cor]; split_ifs <;> ring
    rw [hc, det_add_cor, Matrix.det_transpose, duU_inv_last, Ring.inverse_eq_inv']
    have : (B.transpose.submatrix Fin.castSucc Fin.castSucc) = (B.submatrix Fin.castSucc Fin.castSucc).transpose := by
      ext a b; rfl
    rw [this, Matrix.det_transpose]
    field_simp
    ring
  intro h0
  apply h
  rw [← hdet, Matrix.det_mul, h0, zero_mul]

/- English proof (translation)
Introduce `F _ _ _ E _ _ _ _ M g hs r T T' TT Zh Z Zσ hG`. Establish `hZ` using `hG.2.2.2.2.2.1`. Establish `hN` using `hG.2.2.2.2.2.2`. Rewrite `hZ`, `hN`, the goal using `[isUnit_iff_ph (g := g)]`. Establish `hq : (g.q : F)⁻¹ ≠ 0` using `inv_ne_zero (q_ne g)`.

Prove the components needed by the constructor for the conclusion. Rewrite using `[det_ph (ph1 g), duU_map_gramG (ph1 g) (ph2 g) (fun x => firstProj_conj_apply x) firstProj_algebraMap, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, duU_det_P]`. Use `mul_ne_zero (mul_ne_zero (pow_ne_zero _ hq) (duU_det_Gh _ _ _ _ ?_ ?_)) (pow_ne_zero _ hq)` and prove the remaining obligations. Rewrite using `[← det_ph]`. Conclude with `hZ.2`.

Use `hN.1 using 1` and compare the differences between its conclusion and the goal. Simplify using `only [map_sub, map_mul, firstProj_conj_apply, firstProj_algebraMap, det_ph (ph1 g), det_ph (ph2 g), Matrix.submatrix_map]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[det_ph (ph2 g), duU_map_gramG (ph2 g) (ph1 g) (fun x => secondProj_conj_apply x) ph2_algebraMap_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, duU_det_P]`. Use `mul_ne_zero (mul_ne_zero (pow_ne_zero _ hq) (duU_det_Gh _ _ _ _ ?_ ?_)) (pow_ne_zero _ hq)` and prove the remaining obligations.

Rewrite using `[← det_ph]`. Conclude with `hZ.1`. Use `hN.2 using 1` and compare the differences between its conclusion and the goal. Simplify using `only [map_sub, map_mul, secondProj_conj_apply, ph2_algebraMap_eq, det_ph (ph1 g), det_ph (ph2 g), Matrix.submatrix_map]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem unitGramG_holds : UnitGramG := by
  intro F _ _ _ E _ _ _ _ M g hs r T T' TT Zh Z Zσ hG
  have hZ := hG.2.2.2.2.2.1
  have hN := hG.2.2.2.2.2.2
  rw [isUnit_iff_ph (g := g)] at hZ hN ⊢
  have hq : (g.q : F)⁻¹ ≠ 0 := inv_ne_zero (q_ne g)
  constructor
  · rw [det_ph (ph1 g), duU_map_gramG (ph1 g) (ph2 g) (fun x => firstProj_conj_apply x) firstProj_algebraMap, Matrix.det_mul,
      Matrix.det_mul, Matrix.det_transpose, duU_det_P]
    refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ hq) (duU_det_Gh _ _ _ _ ?_ ?_)) (pow_ne_zero _ hq)
    · rw [← det_ph]; exact hZ.2
    · convert hN.1 using 1
      simp only [map_sub, map_mul, firstProj_conj_apply, firstProj_algebraMap, det_ph (ph1 g), det_ph (ph2 g), Matrix.submatrix_map]
      ring
  · rw [det_ph (ph2 g), duU_map_gramG (ph2 g) (ph1 g) (fun x => secondProj_conj_apply x) ph2_algebraMap_eq, Matrix.det_mul,
      Matrix.det_mul, Matrix.det_transpose, duU_det_P]
    refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ hq) (duU_det_Gh _ _ _ _ ?_ ?_)) (pow_ne_zero _ hq)
    · rw [← det_ph]; exact hZ.1
    · convert hN.2 using 1
      simp only [map_sub, map_mul, secondProj_conj_apply, ph2_algebraMap_eq, det_ph (ph1 g), det_ph (ph2 g), Matrix.submatrix_map]
      ring

/- English proof (translation)
The claim follows from `stepDuU_of unitGramG_holds`.
-/
theorem stepDuU : StepDuU := stepDuU_of unitGramG_holds

end DuU3

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
