import Mathlib
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Height
import GroundTheory.AutomorphicForms.TraceFormulaConvolution
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsAreCuspForms
import GroundTheory.AutomorphicForms.MultiplicityOne.OpenSubgroupRep
import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteLevelGroups
import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteAdelicHaar
import GroundTheory.AutomorphicForms.L2LocalComponents.CenterCommute
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.InfEmbGrpEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.GrpEqMemArchCompact
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.ExpGen

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

open Matrix GlobalTheory.CuspRep in
/- English proof (translation)
Equip the data with the indicated structure. A detailed English derivation is pending.
-/
private theorem matEq_exp (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ)
    (X : Matrix (Fin n) (Fin n) (Cinf K)) :
    UpperTheory.V.Cm.matEq K n (NormedSpace.exp X) = NormedSpace.exp (UpperTheory.V.Cm.matEq K n X) := by
  letI : Algebra ℚ (ArchMatrix K n) := Algebra.compHom _ (algebraMap ℚ ℝ)
  open scoped Matrix.Norms.Operator in
  exact NormedSpace.map_exp (𝔸 := Matrix (Fin n) (Fin n) (Cinf K)) (UpperTheory.V.Cm.matEq K n)
    (show Continuous (UpperTheory.V.Cm.matEq K n) from (UpperTheory.V.Cm.archEq K n).continuous) X

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem UpperTheory.ConvolutionTheory.Tf.expGen :
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ),
      Subgroup.closure (Set.range (isExpLieAlgebra K n).expG) = ⊤ := by
  intro K _ _ _ n
  rw [eq_top_iff]
  intro z _
  have key := UpperTheory.V.AlgRepEndIrreducible.expGen K n
    ((Subgroup.closure (Set.range (isExpLieAlgebra K n).expG)).toSubmonoid.comap
      (UpperTheory.V.Cm.grpEq K n).toMonoidHom) ?_ ((UpperTheory.V.Cm.grpEq K n).symm z)
  · simpa using key
  · intro X y hy
    refine Subgroup.subset_closure ⟨⟨UpperTheory.V.Cm.matEq K n X, Submodule.mem_top⟩, ?_⟩
    refine Subtype.ext (Units.ext ?_)
    change NormedSpace.exp (UpperTheory.V.Cm.matEq K n X) = UpperTheory.V.Cm.matEq K n y.val
    rw [hy, matEq_exp]
