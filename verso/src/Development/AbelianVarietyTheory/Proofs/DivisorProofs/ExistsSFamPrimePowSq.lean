import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptySiegelFamilyOverArithmeticBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaUniformisationComplexAbelianVarieties
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianScheme
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeCycAway

open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SiegelTor GlobalTheory.ZM

namespace GlobalTheory.SiegelTor

/- English proof (translation)
Introduce `g l hg hl _hodd`. Take `⟨hLaws, hLaws2⟩` from `GlobalTheory.abelianSchemeLaws_all`. Take `⟨j₀, hj₀⟩` from `GlobalTheory.ZM.SiegelArithFamily.nonempty_sFam hLaws hLaws2 GlobalTheory.Moduli.cube_of_isLB GlobalTheory.thetaUnifAV_closed g l hg hl _hodd`. Use `⟨max j₀ 1, le_max_right _ _, ?_⟩` and prove the remaining obligations. Establish `hn : (l ^ max j₀ 1) ^ 2 ≠ 0` using `pow_ne_zero _ (pow_ne_zero _ hl.ne_zero)`.

Establish `key` using `hj₀ (max j₀ 1) (le_max_left _ _) (cycAway ((l ^ max j₀ 1) ^ 2)) (cycBase hn) (cycAway ((l ^ max j₀ 1) ^ 2)).subtype (arBase_cycAway _ hn)`. Rewrite `key` using `[cycBase_ζ hn]`. Then use the resulting hypothesis.
-/
theorem exists_sFam_primePow_sq :
    ∀ g l : ℕ, 1 ≤ g → l.Prime → Odd l →
      ∃ j : ℕ, 1 ≤ j ∧ Nonempty (SFam g ((l ^ j) ^ 2) (zetaAway ((l ^ j) ^ 2))) := by
  intro g l hg hl _hodd
  obtain ⟨hLaws, hLaws2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.ZM.SiegelArithFamily.nonempty_sFam hLaws hLaws2 GlobalTheory.Moduli.cube_of_isLB
    GlobalTheory.thetaUnifAV_closed g l hg hl _hodd

  refine ⟨max j₀ 1, le_max_right _ _, ?_⟩
  have hn : (l ^ max j₀ 1) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hl.ne_zero)

  have key := hj₀ (max j₀ 1) (le_max_left _ _) (cycAway ((l ^ max j₀ 1) ^ 2)) (cycBase hn)
    (cycAway ((l ^ max j₀ 1) ^ 2)).subtype (arBase_cycAway _ hn)
  rwa [cycBase_ζ hn] at key

end GlobalTheory.SiegelTor
