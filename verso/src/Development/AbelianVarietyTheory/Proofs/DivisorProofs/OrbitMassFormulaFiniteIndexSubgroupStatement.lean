import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitMassFormulaFiniteIndexSubgroup
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.OrbitMass.mass_formula` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FOrbitMassFormulaFiniteIndexSubgroup.lean&line=141#L141)
-/
theorem _root_.GlobalTheory.T.orbit_mass_formula_finiteIndex_subgroup : ∀ {G H D : Type} [Group G] [Group H] [MulAction G D] [MulAction H D] (ι : H →* G), Function.Injective ι → (∀ (h : H) (d : D), ι h • d = h • d) → ι.range.FiniteIndex → (∀ d : D, Finite (MulAction.stabilizer G d)) → ∀ [Fintype (MulAction.orbitRel.Quotient G D)] [Fintype (MulAction.orbitRel.Quotient H D)] (f : D → ℂ), (∀ (g : G) (d : D), f (g • d) = f d) → ∑ c : MulAction.orbitRel.Quotient H D, ((Nat.card (MulAction.stabilizer H (Quotient.out c)) : ℂ))⁻¹ * f (Quotient.out c) = (ι.range.index : ℂ) * ∑ c : MulAction.orbitRel.Quotient G D, ((Nat.card (MulAction.stabilizer G (Quotient.out c)) : ℂ))⁻¹ * f (Quotient.out c) := by
  first | exact @GlobalTheory.OrbitMass.mass_formula | exact GlobalTheory.OrbitMass.mass_formula | (intros; apply GlobalTheory.OrbitMass.mass_formula <;> assumption)
