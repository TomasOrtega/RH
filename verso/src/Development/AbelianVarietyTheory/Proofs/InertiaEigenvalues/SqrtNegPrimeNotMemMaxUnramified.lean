import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.UsedConclusionOfUsedInputs
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory

/- English proof (translation)
Introduce `l _ y hy hK`. Establish `hl1 : (1 : ℝ) < (l : ℝ)` using `Formalism.MainNotions.N.PreambleDegrees.Loc.one_lt_l`. Establish `hl0 : (0 : ℝ) < l` using `by linarith`. Establish `hn : ‖y‖ ^ 2 = (l : ℝ)⁻¹`. Rewrite using `[← norm_pow, hy, norm_neg]`.

Conclude with `Formalism.MainNotions.N.PreambleDegrees.Loc.norm_l`. Establish `hy0 : y ≠ 0`. Introduce and unpack `rfl`. Rewrite `hn` using `[norm_zero]`. Establish `: (l : ℝ)⁻¹ ≠ 0` using `inv_ne_zero hl0.ne'`.

Conclude with `this (by rw [← hn]; norm_num)`. Take `⟨k, hk⟩` from `Formalism.MainNotions.N.PreambleDegrees.Loc.norm_Kur_zpow hK hy0`. Rewrite `hn` using `[hk, ← zpow_natCast, ← zpow_mul, ← zpow_neg_one]`. Establish `h` using `zpow_right_injective₀ hl0 hl1.ne' hn`. Use linear arithmetic over natural numbers and integers.
-/
theorem sqrt_neg_l_not_mem_Kur : ∀ (l : ℕ) [Fact l.Prime] (y : Om l), y ^ 2 = -(l : Om l) → y ∉ MaximalUnramifiedExtension l := by
  intro l _ y hy hK
  have hl1 : (1 : ℝ) < (l : ℝ) := Formalism.MainNotions.N.PreambleDegrees.Loc.one_lt_l
  have hl0 : (0 : ℝ) < l := by linarith
  have hn : ‖y‖ ^ 2 = (l : ℝ)⁻¹ := by
    rw [← norm_pow, hy, norm_neg]
    exact Formalism.MainNotions.N.PreambleDegrees.Loc.norm_l
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hn
    have : (l : ℝ)⁻¹ ≠ 0 := inv_ne_zero hl0.ne'
    exact this (by rw [← hn]; norm_num)
  obtain ⟨k, hk⟩ := Formalism.MainNotions.N.PreambleDegrees.Loc.norm_Kur_zpow hK hy0
  rw [hk, ← zpow_natCast, ← zpow_mul, ← zpow_neg_one] at hn
  have h := zpow_right_injective₀ hl0 hl1.ne' hn
  omega

end GlobalTheory
