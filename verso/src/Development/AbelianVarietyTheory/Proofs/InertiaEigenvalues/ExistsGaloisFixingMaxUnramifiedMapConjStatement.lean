import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisFixingMaxUnramifiedMapConj
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCyclic
import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsGaloisFixingMaxUnramifiedMapConj.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.exists_galois_fixing_maxUnramified_map_conj : ∀ (l : ℕ) [Fact l.Prime] (x y : Om l), Polynomial.aeval y (minpoly ↥(MaximalUnramifiedExtension l) x) = 0 → ∃ g : GQ l, (∀ z ∈ MaximalUnramifiedExtension l, g z = z) ∧ g x = y := by
  first | exact @GlobalTheory.LiftKur.exists_gal_fix_Kur_map | exact GlobalTheory.LiftKur.exists_gal_fix_Kur_map | (intros; apply GlobalTheory.LiftKur.exists_gal_fix_Kur_map <;> assumption)
