import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ColValMonomial
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCharactersDlogMinorsGe
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowEqScaleAndExistsUniqueTorsion
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermEvalOneStandardPointSelf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LieEig
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsAlgHomValuationSubring
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLieCoordinates
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFiniteFlatTorsionOfIsGt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsReducedTorsionGeometricFibre
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNnrealValuationOfAddValuation
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorusExtensionOverCompleteLocalDvrStatement

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionCharacter

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FamGerm GlobalTheory.HodgeTateStep GlobalTheory.KernelNoTorsion

/- English proof (translation)
Proceed by induction. Treat this case separately. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Rewrite the conclusion using the stated equalities. Treat this case separately. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem ringAct_natCast {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {Λ : Type} [Ring Λ]
    (ρ : RingAct A Λ) (n : ℕ) : ρ.act n = (𝟙 A) ^ n := by
  induction n with
  | zero =>
    have h : ρ.act 0 = ρ.act 0 * ρ.act 0 := by
      have := ρ.map_add 0 0
      rwa [add_zero] at this
    rw [Nat.cast_zero, pow_zero]
    exact left_eq_mul.mp h
  | succ n ih =>
    rw [Nat.cast_succ, ρ.map_add, ih, ρ.map_one, pow_succ]
    rfl

abbrev Admissible {V O : Type} [CommRing V] [IsLocalRing V] [CommRing O] (f : V →+* O) (A : Type) [CommRing A]
    [Algebra O A] : Prop :=
  (Module.Finite O A ∧ Module.Free O A) ∨ ∃ n : ℕ, ∀ a ∈ maximalIdeal V ^ n, algebraMap O A (f a) = 0

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dualBC_inr {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (s : O) :
    dualBC (Algebra.ofId O R) (TrivSqZeroExt.inr s) = TrivSqZeroExt.inr (algebraMap O R s) :=
  TrivSqZeroExt.lift_apply_inr _ _ _ _ _ s

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem fst_comp_dualBC {O R : Type} [CommRing O] [CommRing R] [Algebra O R] :
    (TrivSqZeroExt.fstHom O R R).comp (dualBC (Algebra.ofId O R)) =
      (Algebra.ofId O R).comp (TrivSqZeroExt.fstHom O O O) := by
  apply DualNumber.algHom_ext
  show (dualBC (Algebra.ofId O R) (TrivSqZeroExt.inr 1)).fst =
    algebraMap O R (TrivSqZeroExt.inr 1 : DualNumber O).fst
  rw [dualBC_inr, TrivSqZeroExt.fst_inr, TrivSqZeroExt.fst_inr, map_zero]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V] {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (y : Pt1 E H V F)

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem dAct_eq_map {R O F Λ : Type} [CommRing R] [CommRing O] [CommRing F] [CommRing Λ] [StarRing Λ] [Algebra R F]
    [Algebra O F] (f : R →+* O) (hf : ∀ r, algebraMap O F (f r) = algebraMap R F r) {d : ℕ}
    (B : Geo.Tor.Germ.FB R d Λ) (a : Λ) :
    TB.dAct F B a = ((TB.dLin (B.A.act a)).map f).map (algebraMap O F) := by
  ext i k
  simp [TB.dAct, TB.dLin, Geo.Tor.Germ.FB.actK, hf]

end GlobalTheory.TorsionCharacter
