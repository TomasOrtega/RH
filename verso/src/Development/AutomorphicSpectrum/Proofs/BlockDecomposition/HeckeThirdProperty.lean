import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development

namespace GlobalTheory.CompanionTheory.TwistedCent

open PositivityTheory.Rg.Tf.Loc

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Chain the equalities or inequalities of the calculation.

Fix the arbitrary inputs or assume the hypotheses. Chain the equalities or inequalities of the calculation.
-/
theorem mem_twCent_twConj_iff {G : Type} [Group G] (θ : Monoid.End G) (g δ x : G) :
    x ∈ twCent θ (twConj θ g δ) ↔ g * x * g⁻¹ ∈ twCent θ δ := by
  rw [mem_twCent, mem_twCent]
  simp only [twConj, map_mul, map_inv]
  constructor
  · intro h
    calc (g * x * g⁻¹)⁻¹ * δ * (θ g * θ x * (θ g)⁻¹)
        = g * (x⁻¹ * (g⁻¹ * δ * θ g) * θ x) * (θ g)⁻¹ := by group
      _ = g * (g⁻¹ * δ * θ g) * (θ g)⁻¹ := by rw [h]
      _ = δ := by group
  · intro h
    calc x⁻¹ * (g⁻¹ * δ * θ g) * θ x
        = g⁻¹ * ((g * x * g⁻¹)⁻¹ * δ * (θ g * θ x * (θ g)⁻¹)) * θ g := by group
      _ = g⁻¹ * δ * θ g := by rw [h]

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem h3 : PositivityTheory.Rg.Tf.Loc.H3 := fun _ _ θ g δ x => mem_twCent_twConj_iff θ g δ x

end GlobalTheory.CompanionTheory.TwistedCent
