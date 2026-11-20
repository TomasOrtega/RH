import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjMemStandardLeviOfReducibleCharpoly
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticTraceFromModelStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsConjMemStandardLeviOfReducibleCharpoly.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.exists_conj_mem_standardLevi_of_reducible_charpoly : ∀ {D : D7} {V : HSp D}, 0 < V.rank → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple → ∀ (Φ : WittFrame V) (γ : GF V), IsRegSS γ.1.1 → ¬ Irreducible γ.1.1.charpoly → ¬ IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1 → ∃ (g : GF V) (P : Finset (SV (wittIndex V))), IsPar P ∧ P.Nonempty ∧ rat V (g * γ * g⁻¹) ∈ Φ.levi D.sp.cm (AF D.host.F) P := by
  first | exact @GlobalTheory.ConjLevi.exists_conj_mem_levi | exact GlobalTheory.ConjLevi.exists_conj_mem_levi | (intros; apply GlobalTheory.ConjLevi.exists_conj_mem_levi <;> assumption)
