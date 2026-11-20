import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteLocalBaseAtClosedPointGroupImports
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction.

Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Chain the equalities or inequalities of the calculation.

Combine the linear equalities and inequalities to obtain the conclusion. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem GlobalTheory.Poinc.norm_lift_le_one_iff_mem_range : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (i : V →+* OO p), IsLocalHom i → ∀ (hi : Function.Injective ((OO p).subtype.comp i)) (x : FractionRing V), ‖IsFractionRing.lift (K := FractionRing V) hi x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V)) := by
  intro p _ V _ _ _ i hloc hi x
  have hV : ValuationRing V := inferInstance
  constructor
  · intro hx
    by_contra hnot
    have hx0 : x ≠ 0 := fun h => hnot ⟨0, by simp [h]⟩
    rcases ValuationRing.isInteger_or_isInteger V x with ⟨a, ha⟩ | ⟨w, hw⟩
    · exact hnot ⟨a, ha⟩
    · have hwu : ¬ IsUnit w := by
        intro hu
        apply hnot
        refine ⟨(hu.unit⁻¹ : Vˣ), ?_⟩
        have h1 : algebraMap V (FractionRing V) (hu.unit⁻¹ : Vˣ) * algebraMap V (FractionRing V) w = 1 := by
          rw [← map_mul]; simp
        rw [hw] at h1
        exact (eq_inv_of_mul_eq_one_left h1).trans (inv_inv x)
      have hiw : ¬ IsUnit (i w) := fun h => hwu (IsLocalHom.map_nonunit w h)
      have hlt : ‖((i w : OO p) : PadicAlgCl p)‖ < 1 := (GlobalTheory.ZH.not_isUnit_OO_iff _).1 hiw
      have hlw : IsFractionRing.lift (K := FractionRing V) hi x⁻¹ = ((i w : OO p) : PadicAlgCl p) := by
        rw [← hw, IsFractionRing.lift_algebraMap]; rfl
      have hprod : ‖IsFractionRing.lift (K := FractionRing V) hi x‖ * ‖IsFractionRing.lift (K := FractionRing V) hi x⁻¹‖ = 1 := by
        rw [← norm_mul, ← map_mul, mul_inv_cancel₀ hx0, map_one, norm_one]
      rw [hlw] at hprod
      have : ‖IsFractionRing.lift (K := FractionRing V) hi x‖ * ‖((i w : OO p) : PadicAlgCl p)‖ < 1 :=
        calc _ ≤ 1 * ‖((i w : OO p) : PadicAlgCl p)‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg _)
          _ < 1 := by rw [_root_.one_mul]; exact hlt
      linarith
  · rintro ⟨v, rfl⟩
    rw [IsFractionRing.lift_algebraMap]
    exact (GlobalTheory.ZH.mem_OO_iff _).1 (i v).2
