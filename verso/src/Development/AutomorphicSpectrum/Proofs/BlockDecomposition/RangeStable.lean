import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff

noncomputable section

open Matrix Finset
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RealCount.KHw

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)

variable {n : ℕ}

/- English proof (translation)
Rewrite using `[Matrix.mem_unitaryGroup_iff]`. Establish `h1 : star (NormedSpace.exp ((s : ℂ) • X)) = NormedSpace.exp (-((s : ℂ) • X))`. Rewrite using `[Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, conjTranspose_smul, hX]`. Simplify using the standard rewrite rules. Rewrite using `[h1, Matrix.exp_neg]`.

Conclude with `Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _))`.
-/
theorem exp_smul_mem (X : Mat n) (hX : Xᴴ = -X) (s : ℝ) :
    NormedSpace.exp ((s : ℂ) • X) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have h1 : star (NormedSpace.exp ((s : ℂ) • X)) = NormedSpace.exp (-((s : ℂ) • X)) := by
    rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, conjTranspose_smul, hX]
    simp
  rw [h1, Matrix.exp_neg]
  exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _))

def oneP (X : Mat n) (hX : Xᴴ = -X) (s : ℝ) : Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨NormedSpace.exp ((s : ℂ) • X), exp_smul_mem X hX s⟩

section

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)} {Kf : Fin n → Fin n → Module.End ℂ V}

/- English proof (translation)
Introduce `a b c d`. Establish `h1` using `h.gl1 a b c d`. Establish `h2` using `h.gl2 a b c d`. Establish `c1` using `h.comm a b c d`. Establish `c2` using `h.comm c d a b`.

Establish `key : kF E1 E2 a b * kF E1 E2 c d - kF E1 E2 c d * kF E1 E2 a b = (E1 a b * E1 c d - E1 c d * E1 a b) + (E2 a b * E2 c d - E2 c d * E2 a b)`. Simplify using `only [kF, add_mul, mul_add, c1, ← c2]`. Normalize the expressions using the abelian group laws. Rewrite using `[key, h1, h2]`. Simplify using `only [kF]`.

Apply the tactic sequence `split_ifs <;> abel`.
-/
theorem glRel_kF {E1 E2 : Fin n → Fin n → Module.End ℂ V} (h : IsPair E1 E2) : Formalism.REAL.GlRel (kF E1 E2) := by
  intro a b c d
  have h1 := h.gl1 a b c d
  have h2 := h.gl2 a b c d
  have c1 := h.comm a b c d
  have c2 := h.comm c d a b
  have key : kF E1 E2 a b * kF E1 E2 c d - kF E1 E2 c d * kF E1 E2 a b =
      (E1 a b * E1 c d - E1 c d * E1 a b) + (E2 a b * E2 c d - E2 c d * E2 a b) := by
    simp only [kF, add_mul, mul_add, c1, ← c2]
    abel
  rw [key, h1, h2]
  simp only [kF]
  split_ifs <;> abel

end

end GlobalTheory.CompanionTheory.RealCount.KHw
