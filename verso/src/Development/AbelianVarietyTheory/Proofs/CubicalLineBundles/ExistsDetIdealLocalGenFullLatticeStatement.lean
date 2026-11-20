import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsDetIdealLocalGenFullLattice
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LamF.exists_detIdeal_isLocGen` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCubicalLineBundles%2FExistsDetIdealLocalGenFullLattice.lean&line=46#L46)
-/
theorem _root_.GlobalTheory.T.exists_detIdeal_localGen_full_lattice : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (Λ : Submodule (𝓞 K) (Fin n → K)), Λ.FG → Submodule.span K (Λ : Set (Fin n → K)) = ⊤ → ∃ I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K, I ≠ 0 ∧ ∀ (p : HeightOneSpectrum (𝓞 K)) (M : Matrix (Fin n) (Fin n) K), (∀ i, ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • M i ∈ Λ) → (∀ c ∈ Λ, ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • c ∈ Submodule.span (𝓞 K) (Set.range fun i => M i)) → IsLocGen p M.det I := by
  first | exact @GlobalTheory.LamF.exists_detIdeal_isLocGen | exact GlobalTheory.LamF.exists_detIdeal_isLocGen | (intros; apply GlobalTheory.LamF.exists_detIdeal_isLocGen <;> assumption)
