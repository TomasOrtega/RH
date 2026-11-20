import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArtinMapSplitPlaceUniformiserEqFrobeniusInv
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinPartMulIncAMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.L2.NTheta (IsIdemAt IsHeckeElt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.SeriesTie
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FArtinMapSplitPlaceUniformiserEqFrobeniusInv.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.artinMap_splitPlaceUniformiser_eq_frobenius_inv : ∀ (D : D7) (Ω : Type) [Field Ω] [Algebra D.host.E Ω] (A : Type) [CommGroup A] (a : Recip D Ω), a.Good → ∀ φ : G D.host.E Ω →* A, IsOpen (φ.ker : Set (G D.host.E Ω)) → ∀ (P : Pl D.host.E) (e : AE D), IsIdemAt e P → ∀ ϖ : 𝓞 D.host.E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ∀ x : (AE D)ˣ, (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) → ∀ B : ValuationSubring Ω, IsPlaceOver B P → (∀ τ ∈ Ine (F := D.host.E) B, φ τ = 1) → ∀ σ : G D.host.E Ω, IsFrob (F := D.host.E) B (normV P) σ → a.pull φ x = (φ σ)⁻¹ := by
  first | exact @GlobalTheory.SeriesTie.Recip.pull_locUnif | exact GlobalTheory.SeriesTie.Recip.pull_locUnif | (intros; apply GlobalTheory.SeriesTie.Recip.pull_locUnif <;> assumption)
