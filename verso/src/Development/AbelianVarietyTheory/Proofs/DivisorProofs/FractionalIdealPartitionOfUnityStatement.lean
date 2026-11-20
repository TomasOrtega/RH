import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealPartitionOfUnity
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetGroupMorphismBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracIdExistsTotPos

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PartitionFracId.exists_partition` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFractionalIdealPartitionOfUnity.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.fractional_ideal_partition_of_unity : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F), ∃ (n : ℕ) (d : Fin n → 𝔠.elt) (a : Fin n → 𝓞 F),
    (∀ j (e : 𝔠.elt), ∃ b : 𝓞 F, a j • e = b • d j) ∧ ∑ j, a j = 1 := by
  first | exact @GlobalTheory.PartitionFracId.exists_partition | exact GlobalTheory.PartitionFracId.exists_partition | (intros; apply GlobalTheory.PartitionFracId.exists_partition <;> assumption)
