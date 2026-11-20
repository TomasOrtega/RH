import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitHecke

/- English proof (translation)
Introduce `k _ m n j z`. Use `set B : LinearMap.BilinForm k (Fin m → k) := Matrix.toBilin' (1 : Matrix (Fin m) (Fin m) k) with hBdef`. Establish `hB : ∀ x y, B x y = x ⬝ᵥ y`. Introduce `x y`. Rewrite using `[hBdef, Matrix.toBilin'_apply', Matrix.one_mulVec]`.

Establish `hrefl : B.IsRefl`. Introduce `x y h`. Rewrite `h`, the goal using `[hB]`. Rewrite using `[dotProduct_comm]`. Conclude with `h`.

Establish `hnd : B.Nondegenerate`. Rewrite using `[hBdef]`. Conclude with `Matrix.Nondegenerate.toBilin' (Matrix.nondegenerate_of_det_ne_zero (by simp))`. Establish `hinv : ∀ W : Submodule k (Fin m → k), B.orthogonal (B.orthogonal W) = W` using `fun W => LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl W`. Establish `hdim : ∀ W : Submodule k (Fin m → k), Module.finrank k W + Module.finrank k (B.orthogonal W) = m`.

Introduce `W`. Establish `h1` using `LinearMap.BilinForm.finrank_orthogonal hnd W`. Establish `h2` using `Submodule.finrank_le W`. Simplify using `only [Module.finrank_fin_fun] at h1 h2`. Use linear arithmetic over natural numbers and integers.

Establish `hker : LinearMap.ker zᵀ.mulVecLin = B.orthogonal (LinearMap.range z.mulVecLin)`. Use extensionality with `x`. Rewrite using `[LinearMap.mem_ker, LinearMap.BilinForm.mem_orthogonal_iff, Matrix.mulVecLin_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `h _ ⟨y, rfl⟩ show B (z.mulVecLin y) x = 0`.

Rewrite using `[hB, Matrix.mulVecLin_apply, dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, h, zero_dotProduct]`. Introduce `h`. Use extensionality with `i`. Establish `h1 : B (z.mulVecLin (Pi.single i 1)) x = 0` using `h _ ⟨_, rfl⟩`. Rewrite `h1` using `[hB, Matrix.mulVecLin_apply, dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_single, mul_one]`.

Simplify using `using h1`. Set `e : Submodule k (Fin m → k) ≃ Submodule k (Fin m → k)` to `⟨B.orthogonal, B.orthogonal, hinv, hinv⟩`. Use `Nat.card_congr (e.subtypeEquiv fun W => ?_)` and prove the remaining obligations. Use `show _ ↔ Module.finrank k (B.orthogonal W) = j ∧ LinearMap.range z.mulVecLin ≤ B.orthogonal W`. Establish `hd` using `hdim W`.

Use `and_congr ⟨fun h => by omega, fun h => by omega⟩ ?_` and prove the remaining obligations. Rewrite using `[hker]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `LinearMap.BilinForm.orthogonal_le (B := B) h` as an intermediate fact.

Rewrite `this` using `[hinv]`. Then use the resulting hypothesis. Introduce `h`. Use `LinearMap.BilinForm.orthogonal_le (B := B) h` as an intermediate fact. Rewrite `this` using `[hinv]`. Then use the resulting hypothesis.
-/
theorem card_le_ker_transpose_eq_card_range_le :
    ∀ (k : Type) [Field k] (m n j : ℕ) (z : Matrix (Fin m) (Fin n) k), Nat.card {W : Submodule k (Fin m → k) // Module.finrank k W + j = m ∧ W ≤ LinearMap.ker zᵀ.mulVecLin} = Nat.card {W' : Submodule k (Fin m → k) // Module.finrank k W' = j ∧ LinearMap.range z.mulVecLin ≤ W'} := by
  intro k _ m n j z
  set B : LinearMap.BilinForm k (Fin m → k) := Matrix.toBilin' (1 : Matrix (Fin m) (Fin m) k) with hBdef
  have hB : ∀ x y, B x y = x ⬝ᵥ y := by
    intro x y
    rw [hBdef, Matrix.toBilin'_apply', Matrix.one_mulVec]
  have hrefl : B.IsRefl := by
    intro x y h
    rw [hB] at h ⊢
    rw [dotProduct_comm]; exact h
  have hnd : B.Nondegenerate := by
    rw [hBdef]
    exact Matrix.Nondegenerate.toBilin' (Matrix.nondegenerate_of_det_ne_zero (by simp))
  have hinv : ∀ W : Submodule k (Fin m → k), B.orthogonal (B.orthogonal W) = W :=
    fun W => LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl W
  have hdim : ∀ W : Submodule k (Fin m → k),
      Module.finrank k W + Module.finrank k (B.orthogonal W) = m := by
    intro W
    have h1 := LinearMap.BilinForm.finrank_orthogonal hnd W
    have h2 := Submodule.finrank_le W
    simp only [Module.finrank_fin_fun] at h1 h2
    omega
  have hker : LinearMap.ker zᵀ.mulVecLin = B.orthogonal (LinearMap.range z.mulVecLin) := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.BilinForm.mem_orthogonal_iff, Matrix.mulVecLin_apply]
    constructor
    · rintro h _ ⟨y, rfl⟩
      show B (z.mulVecLin y) x = 0
      rw [hB, Matrix.mulVecLin_apply, dotProduct_comm, Matrix.dotProduct_mulVec,
        ← Matrix.mulVec_transpose, h, zero_dotProduct]
    · intro h
      ext i
      have h1 : B (z.mulVecLin (Pi.single i 1)) x = 0 := h _ ⟨_, rfl⟩
      rw [hB, Matrix.mulVecLin_apply, dotProduct_comm, Matrix.dotProduct_mulVec,
        ← Matrix.mulVec_transpose, dotProduct_single, mul_one] at h1
      simpa using h1
  let e : Submodule k (Fin m → k) ≃ Submodule k (Fin m → k) :=
    ⟨B.orthogonal, B.orthogonal, hinv, hinv⟩
  refine Nat.card_congr (e.subtypeEquiv fun W => ?_)
  show _ ↔ Module.finrank k (B.orthogonal W) = j ∧ LinearMap.range z.mulVecLin ≤ B.orthogonal W
  have hd := hdim W
  refine and_congr ⟨fun h => by omega, fun h => by omega⟩ ?_
  rw [hker]
  constructor
  · intro h
    have := LinearMap.BilinForm.orthogonal_le (B := B) h
    rwa [hinv] at this
  · intro h
    have := LinearMap.BilinForm.orthogonal_le (B := B) h
    rwa [hinv] at this

end GlobalTheory.SplitHecke
