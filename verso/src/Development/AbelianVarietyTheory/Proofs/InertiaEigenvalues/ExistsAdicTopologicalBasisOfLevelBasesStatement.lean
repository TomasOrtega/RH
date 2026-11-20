import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdicTopologicalBasisOfLevelBases
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BSP.exists_topBasis_of_levels` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsAdicTopologicalBasisOfLevelBases.lean&line=71#L71)
-/
theorem _root_.GlobalTheory.T.exists_adicTopologicalBasis_of_level_bases : ∀ (A : Type) [CommRing A] (L : Type) [CommRing L] (Q : Type) [CommRing Q] (s : A →+* L) (i : L →+* Q) (J : Ideal A) (ι : Type) (m : ι → L) (k₀ : ι), m k₀ = 1 → IsAdicComplete J A → IsCompl i (J.map s) → (∀ (n : ℕ) (x : L), ∃ c : ι →₀ A, x - c.sum (fun k a => s a * m k) ∈ (J ^ n).map s) → (∀ (n : ℕ) (c : ι →₀ A), c.sum (fun k a => s a * m k) ∈ (J ^ n).map s → ∀ k, c k ∈ J ^ n) → ∃ tb : TopBasis (i.comp s) J ι, ∀ k, tb.b k = i (m k) := by
  first | exact @GlobalTheory.BSP.exists_topBasis_of_levels | exact GlobalTheory.BSP.exists_topBasis_of_levels | (intros; apply GlobalTheory.BSP.exists_topBasis_of_levels <;> assumption)
