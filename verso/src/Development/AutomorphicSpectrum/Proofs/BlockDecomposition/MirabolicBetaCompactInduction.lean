import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMirProj
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCharacterEqStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedKernelConjugation

open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun Matrix ValuativeRel GlobalTheory.SplitWeil
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.BZBeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Use `Units.continuous_iff.2 ⟨hf, ?_⟩` and prove the remaining obligations. Establish `h : (fun x => (((f x)⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k)) = fun x => (Matrix.det (f x : Matrix (Fin m) (Fin m) k))⁻¹ • Matrix.adjugate (f x : Matrix (Fin m) (Fin m) k)`. Use function extensionality and compare the values at `x`. Rewrite using `[Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv']`. Use `show Continuous (fun x => (((f x)⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k))`.

Rewrite using `[h]`. Establish `hd : ∀ x, Matrix.det (f x : Matrix (Fin m) (Fin m) k) ≠ 0` using `fun x => ((Matrix.isUnit_iff_isUnit_det _).1 (f x).isUnit).ne_zero`. Conclude with `(Continuous.inv₀ hf.matrix_det hd).smul hf.matrix_adjugate`.
-/
theorem continuous_gl {X : Type*} [TopologicalSpace X] {m : ℕ} (f : X → GL (Fin m) k)
    (hf : Continuous fun x => ((f x : GL (Fin m) k) : Matrix (Fin m) (Fin m) k)) : Continuous f := by
  refine Units.continuous_iff.2 ⟨hf, ?_⟩
  have h : (fun x => (((f x)⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k)) =
      fun x => (Matrix.det (f x : Matrix (Fin m) (Fin m) k))⁻¹ •
        Matrix.adjugate (f x : Matrix (Fin m) (Fin m) k) := by
    funext x
    rw [Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv']
  show Continuous (fun x => (((f x)⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k))
  rw [h]
  have hd : ∀ x, Matrix.det (f x : Matrix (Fin m) (Fin m) k) ≠ 0 := fun x =>
    ((Matrix.isUnit_iff_isUnit_det _).1 (f x).isUnit).ne_zero
  exact (Continuous.inv₀ hf.matrix_det hd).smul hf.matrix_adjugate

/- English proof (translation)
Establish `hv : Continuous fun g : GL (Fin n) k => ((g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)` using `Units.continuous_val`. Establish `h : Continuous fun g : GL (Fin n) k => glEmb k n g`. Use `continuous_gl _ ?_` and prove the remaining obligations. Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Use `show Continuous fun g : GL (Fin n) k => glEmbMat k n (g : Matrix (Fin n) (Fin n) k) i j`.

Proceed by induction on `i using Fin.lastCases with`. Consider the case `last`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last => simpa [glEmbMat] using continuous_const`. Consider the case `cast j => simpa [glEmbMat] using continuous_const`.

Consider the case `cast i`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last => simpa [glEmbMat] using continuous_const`. Consider the case `cast j`. Simplify using `only [glEmbMat, Fin.lastCases_castSucc]`.

Conclude with `(continuous_apply j).comp ((continuous_apply i).comp hv)`. Conclude with `h.subtype_mk (fun g => glEmb_mem_Mir k n g)`.
-/
theorem continuous_levi (n : ℕ) : Continuous (levi k n) := by
  have hv : Continuous fun g : GL (Fin n) k => ((g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) :=
    Units.continuous_val
  have h : Continuous fun g : GL (Fin n) k => glEmb k n g := by
    refine continuous_gl _ ?_
    refine continuous_pi fun i => continuous_pi fun j => ?_
    show Continuous fun g : GL (Fin n) k => glEmbMat k n (g : Matrix (Fin n) (Fin n) k) i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simpa [glEmbMat] using continuous_const
      | cast j => simpa [glEmbMat] using continuous_const
    | cast i =>
      induction j using Fin.lastCases with
      | last => simpa [glEmbMat] using continuous_const
      | cast j =>
        simp only [glEmbMat, Fin.lastCases_castSucc]
        exact (continuous_apply j).comp ((continuous_apply i).comp hv)
  exact h.subtype_mk (fun g => glEmb_mem_Mir k n g)

def unipMir (m : ℕ) (x : Fin m → k) : Mir k m :=
  ⟨unip k m (Multiplicative.ofAdd x), MirU_le_Mir k m ⟨_, rfl⟩⟩

def secMat (n : ℕ) (j : Fin (n + 1)) (a : Fin (n + 1) → k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k :=
  ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k).updateRow (Fin.last n)
    (a ∘ Equiv.swap j (Fin.last n))).submatrix id (Equiv.swap j (Fin.last n))

end GlobalTheory.CompanionTheory.BZBeta

end
