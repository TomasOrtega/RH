import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentIntegralValued
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HeightCounting.Up.eExp_int_allSt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExponentIntegralValued.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exponent_integral_valued : PrN → AllSt fun _ _ _ _ _ _ x => ∀ (j : Fin (Dof x).R.m) (g : ↥((Dof x).R.Psi)), ∃ z : ℤ, eExp (Dof x) j g = (z : ℚ) := by
  first | exact @GlobalTheory.HeightCounting.Up.eExp_int_allSt | exact GlobalTheory.HeightCounting.Up.eExp_int_allSt | (intros; apply GlobalTheory.HeightCounting.Up.eExp_int_allSt <;> assumption)
