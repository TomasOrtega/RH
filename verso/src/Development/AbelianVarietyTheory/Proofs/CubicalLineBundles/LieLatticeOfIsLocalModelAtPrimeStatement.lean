import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeOfIsLocalModelAtPrime
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCubicalLineBundles%2FLieLatticeOfIsLocalModelAtPrime.lean&line=115#L115)
-/
theorem _root_.GlobalTheory.T.lieLattice_of_isLocalModel_at_prime : HomExtDvr → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (hg rig hr th hth) (𝔭 : HeightOneSpectrum (𝓞 K)) (a : K) (M : Matrix (Fin F.P₀.g) (Fin F.P₀.g) K), KeyPow.IsLocalModel (F.key hg rig hr th hth) 𝔭 a M → (∀ i, ∃ s : 𝓞 K, s ∉ 𝔭.asIdeal ∧ s • M i ∈ F.lieLat) ∧ ∀ c ∈ F.lieLat, ∃ s : 𝓞 K, s ∉ 𝔭.asIdeal ∧ s • c ∈ Submodule.span (𝓞 K) (Set.range fun i => M i) := by
  first | exact @GlobalTheory.CM.lieLat_of_isLocalModel | exact GlobalTheory.CM.lieLat_of_isLocalModel | (intros; apply GlobalTheory.CM.lieLat_of_isLocalModel <;> assumption)
