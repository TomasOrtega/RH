import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianLifting
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CanonicalOfAbelianDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.abelianDeRham` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAbelianSchemeFirstDeRhamStructure.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.abelianScheme_firstDeRham_structure : GlobalTheory.Published.AbelianDeRham := by
  first | exact @GlobalTheory.abelianDeRham | exact GlobalTheory.abelianDeRham | (intros; apply GlobalTheory.abelianDeRham <;> assumption)
