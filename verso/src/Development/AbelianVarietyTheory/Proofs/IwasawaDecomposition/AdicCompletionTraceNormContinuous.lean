import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Equip the data with the indicated structure. Fix the arbitrary inputs or assume the hypotheses. Equip the data with the indicated structure. Reduce the conclusion to the remaining proof obligations.

Introduce a local definition for the expression. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

A detailed English derivation is pending.
-/
theorem adicCompletion_trace_norm_continuous : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (f : v.adicCompletion K →+* v'.adicCompletion L), Continuous f → letI := f.toAlgebra; FiniteDimensional (v.adicCompletion K) (v'.adicCompletion L) → Continuous (Algebra.trace (v.adicCompletion K) (v'.adicCompletion L)) ∧ Continuous (Algebra.norm (v.adicCompletion K) : v'.adicCompletion L → v.adicCompletion K) := by
  intro K L _ _ _ _ v v' f hf
  letI := f.toAlgebra
  intro hfd
  letI : NontriviallyNormedField (v.adicCompletion K) := Valued.toNontriviallyNormedField _ _
  haveI : CompleteSpace (v.adicCompletion K) := inferInstance
  haveI : ContinuousSMul (v.adicCompletion K) (v'.adicCompletion L) := continuousSMul_of_algebraMap _ _ hf
  refine ⟨LinearMap.continuous_of_finiteDimensional _, ?_⟩
  let b := Module.finBasis (v.adicCompletion K) (v'.adicCompletion L)
  have hn : (Algebra.norm (v.adicCompletion K) : v'.adicCompletion L → v.adicCompletion K) = fun y => (Algebra.leftMulMatrix b y).det := by
    funext y; exact Algebra.norm_eq_matrix_det b y
  rw [hn]
  have hl : Continuous (fun y => Algebra.leftMulMatrix b y) :=
    (LinearMap.continuous_of_finiteDimensional (Algebra.leftMulMatrix b).toLinearMap)
  exact hl.matrix_det

end GlobalTheory
