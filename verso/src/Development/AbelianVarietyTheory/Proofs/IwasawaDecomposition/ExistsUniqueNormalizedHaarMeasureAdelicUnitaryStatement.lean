import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueNormalizedHaarMeasureAdelicUnitary
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mem.VolMeasure.existsUnique_isVolMeasG` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsUniqueNormalizedHaarMeasureAdelicUnitary.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.existsUnique_normalizedHaarMeasure_adelicUnitary : ∀ (D : D7) (V : HSp D), V.SigOK → ∃! μ, IsVolMeasG D V (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) μ := by
  first | exact @GlobalTheory.Mem.VolMeasure.existsUnique_isVolMeasG | exact GlobalTheory.Mem.VolMeasure.existsUnique_isVolMeasG | (intros; apply GlobalTheory.Mem.VolMeasure.existsUnique_isVolMeasG <;> assumption)
