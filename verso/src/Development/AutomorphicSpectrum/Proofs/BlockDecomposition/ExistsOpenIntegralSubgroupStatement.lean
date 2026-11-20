import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenIntegralSubgroup
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UfamConst
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FExistsOpenIntegralSubgroup.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.exists_open_integral_subgroup : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (L : Subgroup (GL (Fin N) (Af E))), IsOpen (L : Set (GL (Fin N) (Af E))) →
  ∃ U : Subgroup (AdelicGLn.integralFiniteGL E N), IsOpen (U : Set (AdelicGLn.integralFiniteGL E N)) ∧ ∀ u : U, ∃ k ∈ L,
    finEmb E N ((u : AdelicGLn.integralFiniteGL E N) : AdelicGLn.FiniteAdelicGL E N) = finGL E N k := by
  first | exact @GlobalTheory.CompanionTheory.Conc.LevelU.exists_level | exact GlobalTheory.CompanionTheory.Conc.LevelU.exists_level | (intros; apply GlobalTheory.CompanionTheory.Conc.LevelU.exists_level <;> assumption)
