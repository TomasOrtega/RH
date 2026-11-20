import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
open GlobalTheory GlobalTheory.TopForm
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.TopFormAppend

/- English proof (translation)
Introduce `k K L _ _ _ cK cL j hc n r x w bK hbK f hf t`. Set `a : Matrix (Fin n) (Fin n) K` to `Matrix.of fun i l => bK.repr (dFun cK (x i)) l`. Establish `ha : ∀ i, dFun cK (x i) = ∑ l, a i l • dFun cK (w l)` using `fun i => by conv_lhs => rw [← bK.sum_repr (dFun cK (x i))]`. Conclude with `Finset.sum_congr rfl fun l _ => by rw [hbK]; rfl`. Establish `hdet : a.det = f` using `(isFreeGen_dForm w bK hbK).1 ((dForm_eq_det_smul x w a ha).symm.trans hf)`.

Establish `hL : ∀ i, dFun cL (j (x i)) = ∑ l, j (a i l) • dFun cL (j (w l))` using `fun i => by`. Use `letI := cK.toAlgebra`. Use `letI := cL.toAlgebra`. Use `letI := j.toAlgebra`. Use `haveI : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' hc.symm`.

Use `congrArg (KaehlerDifferential.map k k K L) (ha i)` as an intermediate fact. Rewrite `this` using `[map_sum]`. Simplify using `only [map_smul, KaehlerDifferential.map_D] at this`. Use `this.trans (Finset.sum_congr rfl fun l _ => ?_)` and prove the remaining obligations. Rewrite using `[← algebraMap_smul L]`.

Both sides reduce to the same expression. Set `M : Matrix (Fin (r + n)) (Fin (r + n)) L` to `Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 0 0 (j.mapMatrix a))`. Establish `hM : M.det = j f`. Rewrite using `[Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, ← RingHom.map_det, hdet]`. Rewrite using `[← hM]`.

Use `dForm_eq_det_smul _ _ M fun i => ?_` and prove the remaining obligations. Rewrite using `[Fin.sum_univ_add]`. Use `Fin.addCases (fun i => ?_) (fun i => ?_) i` and prove the remaining obligations. Simplify using `[M, Matrix.one_apply, Fin.append_left]`. Simplify using `[M, Fin.append_right, hL]`.
-/
theorem dForm_append_eq_smul : ∀ {k K L : Type} [CommRing k] [CommRing K] [CommRing L] (cK : k →+* K) (cL : k →+* L)
    (j : K →+* L), j.comp cK = cL → ∀ {n r : ℕ} (x w : Fin n → K) (bK : Module.Basis (Fin n) K (Omega cK)),
    (∀ i, bK i = dFun cK (w i)) → ∀ f : K, dForm cK x = f • dForm cK w → ∀ t : Fin r → L,
    dForm cL (Fin.append t (fun i => j (x i))) = j f • dForm cL (Fin.append t (fun i => j (w i))) := by
  intro k K L _ _ _ cK cL j hc n r x w bK hbK f hf t
  let a : Matrix (Fin n) (Fin n) K := Matrix.of fun i l => bK.repr (dFun cK (x i)) l
  have ha : ∀ i, dFun cK (x i) = ∑ l, a i l • dFun cK (w l) := fun i => by
    conv_lhs => rw [← bK.sum_repr (dFun cK (x i))]
    exact Finset.sum_congr rfl fun l _ => by rw [hbK]; rfl
  have hdet : a.det = f :=
    (isFreeGen_dForm w bK hbK).1 ((dForm_eq_det_smul x w a ha).symm.trans hf)
  have hL : ∀ i, dFun cL (j (x i)) = ∑ l, j (a i l) • dFun cL (j (w l)) := fun i => by
    letI := cK.toAlgebra
    letI := cL.toAlgebra
    letI := j.toAlgebra
    haveI : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' hc.symm
    have := congrArg (KaehlerDifferential.map k k K L) (ha i)
    rw [map_sum] at this
    simp only [map_smul, KaehlerDifferential.map_D] at this
    refine this.trans (Finset.sum_congr rfl fun l _ => ?_)
    rw [← algebraMap_smul L]
    rfl
  let M : Matrix (Fin (r + n)) (Fin (r + n)) L :=
    Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 0 0 (j.mapMatrix a))
  have hM : M.det = j f := by
    rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul,
      ← RingHom.map_det, hdet]
  rw [← hM]
  refine dForm_eq_det_smul _ _ M fun i => ?_
  rw [Fin.sum_univ_add]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [M, Matrix.one_apply, Fin.append_left]
  · simp [M, Fin.append_right, hL]

end GlobalTheory.TopFormAppend
