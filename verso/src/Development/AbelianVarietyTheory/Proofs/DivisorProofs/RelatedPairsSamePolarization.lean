import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SigmaSplitSymmInl
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKMid.Pair

def innerAlgEquiv (R : Type) {A : Type} [CommRing R] [Ring A] [Algebra R A] (y : Aˣ) : A ≃ₐ[R] A :=
  GlobalTheory.InnerAutomorphism.innerAut R y

/- English proof (translation)
Introduce `p _ G P Q ⟨y, s, _, hβ, hγ⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `h` using `minpoly.algEquiv_eq (innerAlgEquiv G.F y) (P.γ : G.C)`. Simplify using `only [pol, hγ, Units.val_mul]`. Conclude with `h`.

Establish `hsh : ∀ a b : G.C, sh G (a * b) = sh G b * sh G a`. Introduce `a b`. Simplify using `[sh]`. Establish `hy : ∀ X : G.C, sh G (y : G.C) * (sh G ((y⁻¹ : G.Cˣ) : G.C) * X) = X`. Introduce `X`.

Rewrite using `[← mul_assoc, ← hsh, Units.inv_mul, sh, map_one, MulOpposite.unop_one, one_mul]`. Establish `core : (y : G.C) * P.γ * ((y⁻¹ : G.Cˣ) : G.C) * ((y : G.C) * P.β * sh G y) * (sh G ((y⁻¹ : G.Cˣ) : G.C) * (sh G P.γ * sh G y)) = (P.c : ℚ) • ((y : G.C) * P.β * sh G y)`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc, Units.inv_mul_cancel_left, hy]`. Use `_ = _ := by`.

Rewrite using `[P.sim, ← Algebra.smul_def]`. Simplify using `only [mul_smul_comm, smul_mul_assoc]`. Establish `key : algebraMap ℚ G.C (Q.c : ℚ) * Q.β = algebraMap ℚ G.C (P.c : ℚ) * Q.β`. Rewrite using `[← Q.sim, hγ, hβ]`. Simplify using `only [Units.val_mul, hsh, ← Algebra.smul_def, mul_smul_comm, smul_mul_assoc]`.

Rewrite using `[core, smul_comm]`. Establish `hinj : Function.Injective (algebraMap ℚ G.C)` using `(algebraMap ℚ G.C).injective`. Conclude with `Units.ext (hinj ((Units.mul_left_inj Q.β).mp key))`.
-/
theorem rel_pol_c : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P Q : Pair G), P.Rel Q → Q.pol = P.pol ∧ Q.c = P.c := by
  intro p _ G P Q ⟨y, s, _, hβ, hγ⟩
  refine ⟨?_, ?_⟩
  · have h := minpoly.algEquiv_eq (innerAlgEquiv G.F y) (P.γ : G.C)
    simp only [pol, hγ, Units.val_mul]
    exact h
  · have hsh : ∀ a b : G.C, sh G (a * b) = sh G b * sh G a := by
      intro a b; simp [sh]
    have hy : ∀ X : G.C, sh G (y : G.C) * (sh G ((y⁻¹ : G.Cˣ) : G.C) * X) = X := by
      intro X
      rw [← mul_assoc, ← hsh, Units.inv_mul, sh, map_one, MulOpposite.unop_one, one_mul]
    have core : (y : G.C) * P.γ * ((y⁻¹ : G.Cˣ) : G.C) * ((y : G.C) * P.β * sh G y) *
        (sh G ((y⁻¹ : G.Cˣ) : G.C) * (sh G P.γ * sh G y)) = (P.c : ℚ) • ((y : G.C) * P.β * sh G y) := by
      calc (y : G.C) * P.γ * ((y⁻¹ : G.Cˣ) : G.C) * ((y : G.C) * P.β * sh G y) *
            (sh G ((y⁻¹ : G.Cˣ) : G.C) * (sh G P.γ * sh G y))
          = y * (P.γ * P.β * sh G P.γ) * sh G y := by
            simp only [mul_assoc, Units.inv_mul_cancel_left, hy]
        _ = _ := by
            rw [P.sim, ← Algebra.smul_def]
            simp only [mul_smul_comm, smul_mul_assoc]
    have key : algebraMap ℚ G.C (Q.c : ℚ) * Q.β = algebraMap ℚ G.C (P.c : ℚ) * Q.β := by
      rw [← Q.sim, hγ, hβ]
      simp only [Units.val_mul, hsh, ← Algebra.smul_def, mul_smul_comm, smul_mul_assoc]
      rw [core, smul_comm]
    have hinj : Function.Injective (algebraMap ℚ G.C) := (algebraMap ℚ G.C).injective
    exact Units.ext (hinj ((Units.mul_left_inj Q.β).mp key))

end GlobalTheory.LKMid.Pair
