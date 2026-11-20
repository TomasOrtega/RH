import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKMid

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Rewrite using `[Algebra.smul_def]`. Use `first`. Consider the case `(unfold HTGroup.psiR; erw [Algebra.TensorProduct.lift_tmul]; rfl)`. Consider the case `exact Algebra.TensorProduct.lift_tmul _ _ _ r c`.
-/
theorem psiR_tmul (G : HTGroup p) (v : InfinitePlace G.F) (r : ℝ) (c : G.C) :
    G.psiR v (r ⊗ₜ c) = r • G.psi v c := by
  rw [Algebra.smul_def]
  first
    | (unfold HTGroup.psiR; erw [Algebra.TensorProduct.lift_tmul]; rfl)
    | exact Algebra.TensorProduct.lift_tmul _ _ _ r c

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r c`. Rewrite using `[starT_tmul, psiR_tmul, psiR_tmul]`. Rewrite using `[G.psi_star, Matrix.conjTranspose_smul, star_trivial, Matrix.mul_smul, Matrix.smul_mul]`.

Consider the case `add x y hx hy`. Simplify using `only [map_add, MulOpposite.unop_add, hx, hy, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]`.
-/
theorem psiR_starT (G : HTGroup p) (v : InfinitePlace G.F) (x : ℝ ⊗[ℚ] G.C) :
    G.psiR v (starT G.star ℝ x).unop = (G.gram v)⁻¹ * (G.psiR v x)ᴴ * G.gram v := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r c =>
    rw [starT_tmul, psiR_tmul, psiR_tmul]
    rw [G.psi_star, Matrix.conjTranspose_smul, star_trivial, Matrix.mul_smul, Matrix.smul_mul]
  | add x y hx hy =>
    simp only [map_add, MulOpposite.unop_add, hx, hy, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]

/- English proof (translation)
Introduce `p _ G P v`. Take `⟨z, hz⟩` from `P.trivR`. Use `⟨Units.map (G.psiR v).toMonoidHom z, ?_⟩` and prove the remaining obligations. Use `set Zm : Matrix (Fin G.n) (Fin G.n) ℂ := G.psiR v (z : ℝ ⊗[ℚ] G.C) with hZm`. Express the relevant statement in the definitionally equal form `G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C) = Zmᴴ * G.gram v * Zm`.

Establish `hb : G.psiR v (inC G ℝ (P.β : G.C)) = G.psi v (P.β : G.C)`. Express the relevant statement in the definitionally equal form `G.psiR v ((1 : ℝ) ⊗ₜ (P.β : G.C)) = _`. Rewrite using `[psiR_tmul, one_smul]`. Establish `h1` using `congrArg (G.psiR v) hz`. Rewrite `h1` using `[map_mul, map_mul, psiR_starT, hb]`.

Simplify using `only [Units.val_one, map_one] at h1`. Rewrite `h1` using `[← hZm]`. Establish `hg : IsUnit (G.gram v).det` using `isUnit_iff_ne_zero.2 (G.gram_det v)`. Use `set M := G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)`. Establish `hMb : M * G.psi v (P.β : G.C) = 1`.

Rewrite using `[← map_mul, Units.inv_mul, map_one]`. Establish `h2 : G.psi v (P.β : G.C) * ((G.gram v)⁻¹ * Zmᴴ * G.gram v * Zm) = 1`. Use `mul_eq_one_comm.1 (by simpa [Matrix.mul_assoc] using h1 : Zm * (G.psi v (P.β : G.C) * ((G.gram v)⁻¹ * Zmᴴ * G.gram v)) = 1)` as an intermediate fact. Simplify `this` using `[Matrix.mul_assoc]`. Establish `h3 : M = (G.gram v)⁻¹ * Zmᴴ * G.gram v * Zm`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h3]`. Simplify using `only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hg, Matrix.one_mul]`.
-/
theorem Pair.gram_psi_inv_congr : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (v : InfinitePlace G.F),
    ∃ Z : GL (Fin G.n) ℂ, (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) =
      (Z : Matrix (Fin G.n) (Fin G.n) ℂ)ᴴ * G.gram v * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) := by
  intro p _ G P v
  obtain ⟨z, hz⟩ := P.trivR
  refine ⟨Units.map (G.psiR v).toMonoidHom z, ?_⟩
  set Zm : Matrix (Fin G.n) (Fin G.n) ℂ := G.psiR v (z : ℝ ⊗[ℚ] G.C) with hZm
  change G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C) = Zmᴴ * G.gram v * Zm
  have hb : G.psiR v (inC G ℝ (P.β : G.C)) = G.psi v (P.β : G.C) := by
    change G.psiR v ((1 : ℝ) ⊗ₜ (P.β : G.C)) = _
    rw [psiR_tmul, one_smul]
  have h1 := congrArg (G.psiR v) hz
  rw [map_mul, map_mul, psiR_starT, hb] at h1
  simp only [Units.val_one, map_one] at h1
  rw [← hZm] at h1
  have hg : IsUnit (G.gram v).det := isUnit_iff_ne_zero.2 (G.gram_det v)
  set M := G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)
  have hMb : M * G.psi v (P.β : G.C) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have h2 : G.psi v (P.β : G.C) * ((G.gram v)⁻¹ * Zmᴴ * G.gram v * Zm) = 1 := by
    have := mul_eq_one_comm.1 (by simpa [Matrix.mul_assoc] using h1 :
      Zm * (G.psi v (P.β : G.C) * ((G.gram v)⁻¹ * Zmᴴ * G.gram v)) = 1)
    simpa [Matrix.mul_assoc] using this
  have h3 : M = (G.gram v)⁻¹ * Zmᴴ * G.gram v * Zm := by
    calc M = M * (G.psi v (P.β : G.C) * ((G.gram v)⁻¹ * Zmᴴ * G.gram v * Zm)) := by rw [h2, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hMb, Matrix.one_mul]
  rw [h3]
  simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hg, Matrix.one_mul]

end GlobalTheory.LKMid
