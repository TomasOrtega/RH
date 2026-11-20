import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqPowOfModEqSim
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

namespace GlobalTheory.LKGeo

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately.

Establish an intermediate fact. Simplify using the standard rewrite rules. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Treat this case separately. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem baseChangeAlgebraRepresentationAction_injective {C V : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (rep : C →ₐ[ℚ] Module.End ℚ V) (hrep : Function.Injective rep) (R : Type) [CommRing R] [Algebra ℚ R] :
    Function.Injective (actOn rep R) := by
  classical
  set b := Module.finBasis ℚ V
  let g : C →ₗ[ℚ] (Fin (Module.finrank ℚ V) × Fin (Module.finrank ℚ V) → ℚ) :=
    LinearMap.pi (fun ij => (b.coord ij.2).comp ((LinearMap.applyₗ (b ij.1)).comp rep.toLinearMap))
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply hrep
    rw [map_zero]
    refine b.ext (fun i => b.ext_elem (fun j => ?_))
    have := congrFun hx (i, j)
    simpa [g] using this
  have hlg : Function.Injective (LinearMap.lTensor R g) :=
    Module.Flat.lTensor_preserves_injective_linearMap g hg
  have key : ∀ (y : R ⊗[ℚ] C) (i j : Fin (Module.finrank ℚ V)),
      TensorProduct.piScalarRight ℚ R R _ (LinearMap.lTensor R g y) (i, j) =
        TensorProduct.rid ℚ R (LinearMap.lTensor R (b.coord j) (actOn rep R y ((1 : R) ⊗ₜ b i))) := by
    intro y i j
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r x =>
      have h1 : actOn rep R (r ⊗ₜ x) ((1 : R) ⊗ₜ b i) = r ⊗ₜ (rep x (b i)) := by
        simp only [actOn, Algebra.TensorProduct.lift_tmul, Module.End.mul_apply]
        change r • ((rep x).baseChange R ((1 : R) ⊗ₜ b i)) = _
        rw [LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [h1]
      simp [g, Algebra.smul_def]
    | add y z hy hz => simp only [map_add, Pi.add_apply, LinearMap.add_apply, hy, hz]
  rw [injective_iff_map_eq_zero]
  intro y hy
  apply hlg
  rw [map_zero]
  apply (TensorProduct.piScalarRight ℚ R R _).injective
  rw [map_zero]
  funext ij
  rw [key, hy]
  simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem actOn_rep_afP_injective : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G),
    Function.Injective (actOn L.rep (AfP p)) := by
  intro p _ D G L
  haveI := D.finLa
  exact baseChangeAlgebraRepresentationAction_injective L.rep L.rep_inj (AfP p)

end GlobalTheory.LKGeo
