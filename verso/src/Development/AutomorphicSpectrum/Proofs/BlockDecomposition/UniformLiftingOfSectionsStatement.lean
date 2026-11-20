import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformLiftingOfSections
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonzeroLocusSecMonoConst
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.FormalAlg.Lift.exists_uniform_lift` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUniformLiftingOfSections.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.formal_line_bundle_very_ample_system : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, IsProper (Y e).hom) → ∀ (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, (N e).IsLB ∧ (v e).IsGen) → ∀ (d : ℕ), 1 ≤ d → ∀ (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (N 0) (d : ℤ))), VeryAmpleBy (Y 0).hom (pw (N 0) (d : ℤ)) s → ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → ∀ D : ℤ, D = d * t → ∀ (e : ℕ) (σ : LB.Sec (pw (N e) D)), ∃ σ' : LB.Sec (pw (N (e + 1)) D), SecMaps (pullPow (v e) D) σ (secPull σ' (β e)) := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.Lift.exists_uniform_lift | exact GlobalTheory.CompanionTheory.FormalAlg.Lift.exists_uniform_lift | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.Lift.exists_uniform_lift <;> assumption)
