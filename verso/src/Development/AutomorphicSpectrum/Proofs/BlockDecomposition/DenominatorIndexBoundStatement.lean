import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenominatorIndexBound
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FDenominatorIndexBound.lean&line=116#L116)
-/
theorem _root_.GlobalTheory.T.denominator_index_bound : ∀ (K : Type) [Field K] [NumberField K] (𝔱 : Ideal (𝓞 K)), 𝔱 ≠ ⊥ → ∀ c : Submodule (𝓞 K) K, c.FG → (1 : Submodule (𝓞 K) K) ≤ c → (∀ b : K, (∀ a ∈ 𝔱, (a : K) * b ∈ (1 : Submodule (𝓞 K) K)) → b ∈ c) → ∀ (t : 𝓞 K) (w x : K), t ∈ 𝔱 → w ∈ c → (t : K) * w - x ∈ (1 : Submodule (𝓞 K) K) → Ideal.absNorm 𝔱 * Ideal.absNorm (den K x) ≤ idx K c := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.IdxGe.absNorm_mul_den_le_idx | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.IdxGe.absNorm_mul_den_le_idx | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.IdxGe.absNorm_mul_den_le_idx <;> assumption)
