import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalisationPointEigenSystemMem
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PointEigen.ptSys_mem_eigSet` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FLocalisationPointEigenSystemMem.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.localisationPointEigenSystem_mem : ∀ (D : D7) (M : MtFam D), AVTied D M → ∀ (i : D.nd.Loc) (x : D.nd.X i), ptSys D i x ∈ EigSet (M.loc i) (D.nd.l i) (D.nd.Q i) := by
  first | exact @GlobalTheory.PointEigen.ptSys_mem_eigSet | exact GlobalTheory.PointEigen.ptSys_mem_eigSet | (intros; apply GlobalTheory.PointEigen.ptSys_mem_eigSet <;> assumption)
