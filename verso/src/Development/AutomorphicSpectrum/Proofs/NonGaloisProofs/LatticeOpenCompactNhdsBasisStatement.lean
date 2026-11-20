import Mathlib
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.LatticeOpenCompactNhdsBasis
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.ChainRows
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FNonGaloisProofs%2FLatticeOpenCompactNhdsBasis.lean&line=177#L177)
-/
theorem _root_.GlobalTheory.T.lattice_open_compact_nhds_basis : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l), ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → IsOpen (LA.T : Set A.V) ∧ (nhds (0 : A.V)).HasBasis (fun _ : ℕ => True) (fun n => (fun x => ϖ ^ n • x) '' (LA.T : Set A.V)) ∧ IsCompact (LA.T : Set A.V) ∧ (∀ c : ↥(GK K) → A.V, Continuous c → ∃ n : ℕ, ∀ g, ϖ ^ n • c g ∈ LA.T) ∧ ∀ (A' : GRep ↥(GK K) ℚ_[l] LL O) (LA' : Lattice (O := O) A'.ρ) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 ((D.loc l).PD K) LA LA' P → IsDualLat1 ((D.loc l).PD K) LA' LA P.flip := by
  first | exact @GlobalTheory.CompanionTheory.LatTop.lattice_top | exact GlobalTheory.CompanionTheory.LatTop.lattice_top | (intros; apply GlobalTheory.CompanionTheory.LatTop.lattice_top <;> assumption)
