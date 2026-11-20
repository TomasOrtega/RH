import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.BlockCharpoly

open Polynomial

/- English proof (translation)
Use `set V := LinearMap.range e.mulVecLin with hV`. Establish `hd : Module.finrank K V = t` using `hr`. Set `bs` to `Module.finBasisOfFinrankEq K V hd`. Set `P : (Fin n → K) →ₗ[K] V` to `e.mulVecLin.rangeRestrict`. Set `fa : (Fin t → K) →ₗ[K] (Fin n → K)` to `V.subtype ∘ₗ bs.equivFun.symm.toLinearMap`.

Set `fb : (Fin n → K) →ₗ[K] (Fin t → K)` to `bs.equivFun.toLinearMap ∘ₗ P`. Establish `hP : ∀ v : V, P v = v`. Introduce and unpack `⟨v, w, rfl⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show e.mulVecLin (e.mulVecLin w) = e.mulVecLin w`.

Simplify using `only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, he]`. Use `⟨LinearMap.toMatrix' fa, LinearMap.toMatrix' fb, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]`. Use `congr 1`. Use `LinearMap.ext fun y => ?_` and prove the remaining obligations.

Simplify using `only [fa, fb, LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.coe_subtype, hP, LinearEquiv.apply_symm_apply, LinearMap.id_apply]`. Rewrite using `[← LinearMap.toMatrix'_comp]`. Establish `hc : fa ∘ₗ fb = Matrix.toLin' e`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Simplify using `only [fa, fb, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, Submodule.coe_subtype, P, Matrix.toLin'_apply]`.

Both sides reduce to the same expression. Rewrite using `[hc, LinearMap.toMatrix'_toLin']`.
-/
theorem exists_factor_of_idempotent {K : Type} [Field K] {n t : ℕ} (e : Matrix (Fin n) (Fin n) K)
    (he : e * e = e) (hr : e.rank = t) :
    ∃ (a : Matrix (Fin n) (Fin t) K) (b : Matrix (Fin t) (Fin n) K), b * a = 1 ∧ a * b = e := by
  classical
  set V := LinearMap.range e.mulVecLin with hV
  have hd : Module.finrank K V = t := hr
  let bs := Module.finBasisOfFinrankEq K V hd
  let P : (Fin n → K) →ₗ[K] V := e.mulVecLin.rangeRestrict
  let fa : (Fin t → K) →ₗ[K] (Fin n → K) := V.subtype ∘ₗ bs.equivFun.symm.toLinearMap
  let fb : (Fin n → K) →ₗ[K] (Fin t → K) := bs.equivFun.toLinearMap ∘ₗ P

  have hP : ∀ v : V, P v = v := by
    rintro ⟨v, w, rfl⟩
    apply Subtype.ext
    show e.mulVecLin (e.mulVecLin w) = e.mulVecLin w
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, he]
  refine ⟨LinearMap.toMatrix' fa, LinearMap.toMatrix' fb, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun y => ?_
    simp only [fa, fb, LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.coe_subtype, hP,
      LinearEquiv.apply_symm_apply, LinearMap.id_apply]
  · rw [← LinearMap.toMatrix'_comp]
    have hc : fa ∘ₗ fb = Matrix.toLin' e := by
      refine LinearMap.ext fun x => ?_
      simp only [fa, fb, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
        Submodule.coe_subtype, P, Matrix.toLin'_apply]
      rfl
    rw [hc, LinearMap.toMatrix'_toLin']

/- English proof (translation)
Unfold `blockPol`. Use `set A := a.map (C : K →+* K[X]) with hA`. Use `set B := b.map (C : K →+* K[X]) with hB`. Establish `hBA : B * A = 1`. Rewrite using `[hA, hB, ← Matrix.map_mul, hba, Matrix.map_one _ C.map_zero C.map_one]`.

Establish `hmat : (X : K[X]) • (a * b).map (C : K →+* K[X]) - (a * b * M * (a * b)).map (C : K →+* K[X]) + 1 - (a * b).map (C : K →+* K[X]) = 1 + (A * ((X : K[X]) • (1 : Matrix (Fin t) (Fin t) K[X]) - B * M.map (C : K →+* K[X]) * A - 1)) * B`. Simplify using `only [Matrix.map_mul, ← hA, ← hB, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]`. Normalize the expressions using the abelian group laws. Rewrite using `[hmat, Matrix.det_one_add_mul_comm, ← Matrix.mul_assoc, hBA, Matrix.one_mul, add_sub_cancel]`. Establish `hBMA : B * M.map (C : K →+* K[X]) * A = (b * M * a).map (C : K →+* K[X])`.

Rewrite using `[hA, hB, Matrix.map_mul, Matrix.map_mul]`. Rewrite using `[hBMA, Matrix.charpoly]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `only [Matrix.charmatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply, Matrix.map_apply, smul_eq_mul]`.

Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem blockPol_factor {K : Type} [Field K] {n t : ℕ} (a : Matrix (Fin n) (Fin t) K)
    (b : Matrix (Fin t) (Fin n) K) (hba : b * a = 1) (M : Matrix (Fin n) (Fin n) K) :
    blockPol (a * b) (a * b * M * (a * b)) = (b * M * a).charpoly := by
  unfold blockPol
  set A := a.map (C : K →+* K[X]) with hA
  set B := b.map (C : K →+* K[X]) with hB
  have hBA : B * A = 1 := by
    rw [hA, hB, ← Matrix.map_mul, hba, Matrix.map_one _ C.map_zero C.map_one]

  have hmat : (X : K[X]) • (a * b).map (C : K →+* K[X]) - (a * b * M * (a * b)).map (C : K →+* K[X])
        + 1 - (a * b).map (C : K →+* K[X])
      = 1 + (A * ((X : K[X]) • (1 : Matrix (Fin t) (Fin t) K[X]) - B * M.map (C : K →+* K[X]) * A - 1)) * B := by
    simp only [Matrix.map_mul, ← hA, ← hB, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
    abel
  rw [hmat, Matrix.det_one_add_mul_comm, ← Matrix.mul_assoc, hBA, Matrix.one_mul, add_sub_cancel]
  have hBMA : B * M.map (C : K →+* K[X]) * A = (b * M * a).map (C : K →+* K[X]) := by
    rw [hA, hB, Matrix.map_mul, Matrix.map_mul]
  rw [hBMA, Matrix.charpoly]
  congr 1
  ext i j
  simp only [Matrix.charmatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.diagonal_apply, Matrix.map_apply, smul_eq_mul]
  split_ifs <;> simp

/- English proof (translation)
Take `⟨a, b, hba, hab⟩` from `exists_factor_of_idempotent e he hr`. Use `⟨a, b, hba, hab, fun M => ?_⟩` and prove the remaining obligations. Substitute `hab` using the available equality. Conclude with `blockPol_factor a b hba M`.
-/
theorem blockPol_eq_charpoly {K : Type} [Field K] {n t : ℕ} (e : Matrix (Fin n) (Fin n) K)
    (he : e * e = e) (hr : e.rank = t) :
    ∃ (a : Matrix (Fin n) (Fin t) K) (b : Matrix (Fin t) (Fin n) K), b * a = 1 ∧ a * b = e ∧
      ∀ M : Matrix (Fin n) (Fin n) K, blockPol e (e * M * e) = (b * M * a).charpoly := by
  obtain ⟨a, b, hba, hab⟩ := exists_factor_of_idempotent e he hr
  refine ⟨a, b, hba, hab, fun M => ?_⟩
  subst hab
  exact blockPol_factor a b hba M

end GlobalTheory.BlockCharpoly
