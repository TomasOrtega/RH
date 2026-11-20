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
Introduce `p _ V _ _ _ i hloc hi x`. Establish `hV : ValuationRing V` using `inferInstance`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Assume the negation of the conclusion as `hnot`.

Establish `hx0 : x ≠ 0` using `fun h => hnot ⟨0, by simp [h]⟩`. Break down `ValuationRing.isInteger_or_isInteger V x with ⟨a, ha⟩ | ⟨w, hw⟩` into its components or cases. Conclude with `hnot ⟨a, ha⟩`. Establish `hwu : ¬ IsUnit w`. Introduce `hu`.

Apply `hnot` to reduce the goal to its premises. Use `⟨(hu.unit⁻¹ : Vˣ), ?_⟩` and prove the remaining obligations. Establish `h1 : algebraMap V (FractionRing V) (hu.unit⁻¹ : Vˣ) * algebraMap V (FractionRing V) w = 1`. Rewrite using `[← map_mul]`. Simplify using the standard rewrite rules.

Rewrite `h1` using `[hw]`. Conclude with `(eq_inv_of_mul_eq_one_left h1).trans (inv_inv x)`. Establish `hiw : ¬ IsUnit (i w)` using `fun h => hwu (IsLocalHom.map_nonunit w h)`. Establish `hlt : ‖((i w : OO p) : PadicAlgCl p)‖ < 1` using `(GlobalTheory.ZH.not_isUnit_OO_iff _).1 hiw`. Establish `hlw : IsFractionRing.lift (K` using `FractionRing V) hi x⁻¹ = ((i w : OO p) : PadicAlgCl p) := by`.

Rewrite using `[← hw, IsFractionRing.lift_algebraMap]`. Both sides reduce to the same expression. Establish `hprod : ‖IsFractionRing.lift (K` using `FractionRing V) hi x‖ * ‖IsFractionRing.lift (K := FractionRing V) hi x⁻¹‖ = 1 := by`. Rewrite using `[← norm_mul, ← map_mul, mul_inv_cancel₀ hx0, map_one, norm_one]`. Rewrite `hprod` using `[hlw]`.

Establish `: ‖IsFractionRing.lift (K` using `FractionRing V) hi x‖ * ‖((i w : OO p) : PadicAlgCl p)‖ < 1 :=`. Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion. Introduce and unpack `⟨v, rfl⟩`. Rewrite using `[IsFractionRing.lift_algebraMap]`.

Conclude with `(GlobalTheory.ZH.mem_OO_iff _).1 (i v).2`.
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
