import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

/- English proof (translation)
Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem mul_triv_star {S A : Type*} [Ring S] [CommRing A] [Algebra A S] (σ : S →+* Sᵐᵒᵖ) (b h x : S) (t d : A)
    (hx : x * b * (σ x).unop = algebraMap A S t) (hh : h * (σ h).unop = algebraMap A S d) :
    h * x * b * (σ (h * x)).unop = algebraMap A S (t * d) := by
  calc h * x * b * (σ (h * x)).unop = h * (x * b * (σ x).unop) * (σ h).unop := by
        simp only [map_mul, MulOpposite.unop_mul, mul_assoc]
    _ = algebraMap A S t * (h * (σ h).unop) := by rw [hx, ← Algebra.commutes, mul_assoc]
    _ = _ := by rw [hh, map_mul]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Express the relevant assertion in an equivalent form by its definition.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem Pair.exists_triv_toAf_eq_conj : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G)
    (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) P.β x t) (g : G.GAf), ∃ (x' : (AfP p ⊗[ℚ] G.C)ˣ) (t' : (AfP p)ˣ)
    (hx' : Triv G (AfP p) P.β x' t'), P.toAf x' t' hx' P.self = g⁻¹ * P.toAf x t hx P.self * g := by
  intro p _ G P x t hx g
  refine ⟨g.1.1⁻¹ * x, t * g.1.2⁻¹, ?_, ?_⟩
  · exact mul_triv_star (starT G.star (AfP p)) (inC G (AfP p) P.β) ((g.1.1⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)
      (x : AfP p ⊗[ℚ] G.C) (t : AfP p) ((g.1.2⁻¹ : (AfP p)ˣ) : AfP p) hx (mem_uGroup.1 (g⁻¹).2)
  · apply Subtype.ext
    apply Prod.ext
    · change (g.1.1⁻¹ * x) * Units.map (inC G (AfP p)).toMonoidHom P.γ * (g.1.1⁻¹ * x)⁻¹ =
        g.1.1⁻¹ * (x * Units.map (inC G (AfP p)).toMonoidHom P.γ * x⁻¹) * g.1.1
      group
    · change Units.map (algebraMap ℚ (AfP p)).toMonoidHom P.c =
        g.1.2⁻¹ * Units.map (algebraMap ℚ (AfP p)).toMonoidHom P.c * g.1.2
      rw [mul_comm g.1.2⁻¹, inv_mul_cancel_right]

end GlobalTheory.LKMid
