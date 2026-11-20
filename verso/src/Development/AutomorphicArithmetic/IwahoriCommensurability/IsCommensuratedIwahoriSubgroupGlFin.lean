import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.AuxiliaryPrimeFunction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriDoubleCosetTorusNilpotent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAddCharConductorMaxIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeedOrbKVanish
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IwahoriSubgroupDefinitionsAgree
import Development.AutomorphicArithmetic.IwahoriCommensurability.IsCommensuratedIwahoriGl
open Formalism.UG

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.isCommensurated_iwahoriSubgroup_gl_fin :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), Formalism.UG.IsCommensurated (GlobalTheory.SmGL.iwahori k (Fin n)) := by
  intro k _ _ _ _ n
  rw [GlobalTheory.IwEq.iwahori_eq_glnLocal_iwahori k n]
  exact UpperTheory.isCommensurated_iwahori_gl k n
