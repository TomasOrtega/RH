import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatDegreeMinpolyRootNegPrimeUnramified
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FNatDegreeMinpolyRootNegPrimeUnramified.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.natDegree_minpoly_root_neg_prime_unramified : ∀ (l : ℕ) [Fact l.Prime] (N : ℕ) (π : Om l), 0 < N → π ^ N = -(l : Om l) → ∀ (E : Type) [Field E] [Algebra E (Om l)], (∀ y : E, algebraMap E (Om l) y ∈ MaximalUnramifiedExtension l) → (minpoly E π).natDegree = N := by
  first | exact @GlobalTheory.InertiaDeg.natDegree_minpoly_root_neg_l | exact GlobalTheory.InertiaDeg.natDegree_minpoly_root_neg_l | (intros; apply GlobalTheory.InertiaDeg.natDegree_minpoly_root_neg_l <;> assumption)
