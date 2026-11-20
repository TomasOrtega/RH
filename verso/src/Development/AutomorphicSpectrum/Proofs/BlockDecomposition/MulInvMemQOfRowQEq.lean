import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMatMir

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir

namespace GlobalTheory.CompanionTheory.BZPhiPhi

section Alg

variable {k : Type} [Field k]

/- English proof (translation)
Use `show GlobalTheory.BZMir.mirabolicProjection k (n + 1) (a * b⁻¹) ∈ GlobalTheory.BZMir.Mir k n`. Establish `hab : Matrix.vecMul (GlobalTheory.BZMir.eLast k n) (↑(GlobalTheory.BZMir.mirabolicProjection k (n + 1) a) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = Matrix.vecMul (GlobalTheory.BZMir.eLast k n) (↑(GlobalTheory.BZMir.mirabolicProjection k (n + 1) b) : Matrix (Fin (n + 1)) (Fin (n + …`. Rewrite using `[GlobalTheory.BZMir.vecMul_eLast, GlobalTheory.BZMir.vecMul_eLast]`. Use function extensionality and compare the values at `j`. Conclude with `congrFun h j`.

Rewrite using `[GlobalTheory.BZMir.mem_Mir_iff, ← GlobalTheory.BZMir.vecMul_eLast k n (↑(GlobalTheory.BZMir.mirabolicProjection k (n + 1) (a * b⁻¹)) : Matrix (Fin (n + 1)) (Fin (n + 1)) k), map_mul, map_inv, Units.val_mul, ← Matrix.vecMul_vecMul, hab, Matrix.vecMul_vecMul, ← Units.val_mul, mul_ …`.
-/
theorem mul_inv_mem_Q_of_rowQ_eq (n : ℕ) (a b : Mir k (n + 1)) (h : rowQ k n a = rowQ k n b) :
    a * b⁻¹ ∈ Q k n := by
  show GlobalTheory.BZMir.mirabolicProjection k (n + 1) (a * b⁻¹) ∈ GlobalTheory.BZMir.Mir k n
  have hab : Matrix.vecMul (GlobalTheory.BZMir.eLast k n)
      (↑(GlobalTheory.BZMir.mirabolicProjection k (n + 1) a) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      Matrix.vecMul (GlobalTheory.BZMir.eLast k n)
      (↑(GlobalTheory.BZMir.mirabolicProjection k (n + 1) b) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
    rw [GlobalTheory.BZMir.vecMul_eLast, GlobalTheory.BZMir.vecMul_eLast]
    funext j
    exact congrFun h j
  rw [GlobalTheory.BZMir.mem_Mir_iff, ← GlobalTheory.BZMir.vecMul_eLast k n
    (↑(GlobalTheory.BZMir.mirabolicProjection k (n + 1) (a * b⁻¹)) : Matrix (Fin (n + 1)) (Fin (n + 1)) k),
    map_mul, map_inv, Units.val_mul, ← Matrix.vecMul_vecMul, hab, Matrix.vecMul_vecMul,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]

def rowMat (n : ℕ) (r : Fin (n + 1) → k) : Matrix (Fin (n + 2)) (Fin (n + 2)) k :=
  (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) k).updateRow (Fin.castSucc (Fin.last n))
    (Fin.lastCases (motive := fun _ => k) 0 r)

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[GlobalTheory.CompanionTheory.BZPhiPhi.rowMat, Matrix.updateRow_apply]`. Use `split_ifs with hi`. Substitute `hi` using the available equality. Proceed by induction on `j using Fin.lastCases with`.

Consider the case `last => simp [Matrix.one_apply, Fin.castSucc_ne_last]`. Consider the case `cast j`. Distinguish the cases in `hj : j = Fin.last n`. Substitute `hj` using the available equality. Simplify using `[Matrix.one_apply]`.

Simplify using `[Matrix.one_apply, Pi.single_apply, hj, Ne.symm hj]`. Both sides reduce to the same expression.
-/
theorem rowMat_single (n : ℕ) : rowMat n (Pi.single (Fin.last n) (1 : k)) = 1 := by
  ext i j
  rw [GlobalTheory.CompanionTheory.BZPhiPhi.rowMat, Matrix.updateRow_apply]
  split_ifs with hi
  · subst hi
    induction j using Fin.lastCases with
    | last => simp [Matrix.one_apply, Fin.castSucc_ne_last]
    | cast j =>
      by_cases hj : j = Fin.last n
      · subst hj
        simp [Matrix.one_apply]
      · simp [Matrix.one_apply, Pi.single_apply, hj, Ne.symm hj]
  · rfl

def rowEl (n : ℕ) (r : Fin (n + 1) → k) (h : (rowMat n r).det ≠ 0) : Mir k (n + 1) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (rowMat n r) h, by
    rw [mem_Mir_iff]
    show rowMat n r (Fin.last (n + 1)) = eLast k (n + 1)
    rw [rowMat, updateRow_ne (Fin.castSucc_ne_last _).symm]
    funext j
    simp [eLast, one_apply, Pi.single_apply, eq_comm]⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rowEl_val (n : ℕ) (r : Fin (n + 1) → k) (h : (rowMat n r).det ≠ 0) :
    (((rowEl n r h : Mir k (n + 1)) : GL (Fin (n + 2)) k) : Matrix (Fin (n + 2)) (Fin (n + 2)) k) = rowMat n r := rfl

/- English proof (translation)
Use function extensionality and compare the values at `j`. Use `show GlobalTheory.CompanionTheory.BZPhiPhi.rowMat n r (Fin.castSucc (Fin.last n)) (Fin.castSucc j) = r j`. Rewrite using `[GlobalTheory.CompanionTheory.BZPhiPhi.rowMat, Matrix.updateRow_self, Fin.lastCases_castSucc]`.
-/
theorem rowQ_rowEl (n : ℕ) (r : Fin (n + 1) → k) (h : (rowMat n r).det ≠ 0) :
    rowQ k n (rowEl n r h) = r := by
  funext j
  show GlobalTheory.CompanionTheory.BZPhiPhi.rowMat n r (Fin.castSucc (Fin.last n)) (Fin.castSucc j) = r j
  rw [GlobalTheory.CompanionTheory.BZPhiPhi.rowMat, Matrix.updateRow_self, Fin.lastCases_castSucc]

end Alg

section Top

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Simplify using `only [GlobalTheory.CompanionTheory.BZPhiPhi.rowMat]`. Distinguish the cases in `hi : i = Fin.castSucc (Fin.last n)`. Substitute `hi` using the available equality. Simplify using `only [Matrix.updateRow_self]`.

Proceed by induction on `j using Fin.lastCases with`. Consider the case `last`. Simplify using `only [Fin.lastCases_last]`. Conclude with `continuous_const`. Consider the case `cast j`.

Simplify using `only [Fin.lastCases_castSucc]`. Conclude with `continuous_apply j`. Simplify using `only [Matrix.updateRow_ne hi]`. Conclude with `continuous_const`.
-/
theorem continuous_rowMat (n : ℕ) : Continuous (rowMat (k := k) n) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [GlobalTheory.CompanionTheory.BZPhiPhi.rowMat]
  by_cases hi : i = Fin.castSucc (Fin.last n)
  · subst hi
    simp only [Matrix.updateRow_self]
    induction j using Fin.lastCases with
    | last =>
      simp only [Fin.lastCases_last]
      exact continuous_const
    | cast j =>
      simp only [Fin.lastCases_castSucc]
      exact continuous_apply j
  · simp only [Matrix.updateRow_ne hi]
    exact continuous_const

/- English proof (translation)
Establish `hM : Continuous fun r : {r : Fin (n + 1) → k // (GlobalTheory.CompanionTheory.BZPhiPhi.rowMat n r).det ≠ 0} => GlobalTheory.CompanionTheory.BZPhiPhi.rowMat n r.1` using `(GlobalTheory.CompanionTheory.BZPhiPhi.continuous_rowMat n).comp continuous_subtype_val`. Apply `continuous_induced_rng.2` to reduce the goal to its premises. Rewrite using `[Units.continuous_iff]`. Use `⟨hM, ?_⟩` and prove the remaining obligations. Simplify using `only [Function.comp_apply, Matrix.coe_units_inv]`.

Use `show Continuous fun r : {r : Fin (n + 1) → k // (GlobalTheory.CompanionTheory.BZPhiPhi.rowMat n r).det ≠ 0} => (GlobalTheory.CompanionTheory.BZPhiPhi.rowMat n r.1)⁻¹`. Simplify using `only [Matrix.inv_def, Ring.inverse_eq_inv']`. Conclude with `(hM.matrix_det.inv₀ fun r => r.2).smul hM.matrix_adjugate`.
-/
theorem continuous_rowEl (n : ℕ) :
    Continuous fun r : {r : Fin (n + 1) → k // (rowMat n r).det ≠ 0} => rowEl n r.1 r.2 := by
  have hM : Continuous fun r : {r : Fin (n + 1) → k // (GlobalTheory.CompanionTheory.BZPhiPhi.rowMat n r).det ≠ 0} =>
      GlobalTheory.CompanionTheory.BZPhiPhi.rowMat n r.1 :=
    (GlobalTheory.CompanionTheory.BZPhiPhi.continuous_rowMat n).comp continuous_subtype_val
  apply continuous_induced_rng.2
  rw [Units.continuous_iff]
  refine ⟨hM, ?_⟩
  simp only [Function.comp_apply, Matrix.coe_units_inv]
  show Continuous fun r : {r : Fin (n + 1) → k // (GlobalTheory.CompanionTheory.BZPhiPhi.rowMat n r).det ≠ 0} =>
    (GlobalTheory.CompanionTheory.BZPhiPhi.rowMat n r.1)⁻¹
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']
  exact (hM.matrix_det.inv₀ fun r => r.2).smul hM.matrix_adjugate

end Top

end GlobalTheory.CompanionTheory.BZPhiPhi

end
