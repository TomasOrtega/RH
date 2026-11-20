import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLevelStructureComplex
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNonemptyLevelStructureComplex.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.nonempty_level_structure_complex : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ), 1 ≤ N →
    ∀ X : Obj F 𝔠 (Sp ℂ), Nonempty (X.Level N) := by
  first | exact @GlobalTheory.RealMult.Obj.nonempty_level_complex | exact GlobalTheory.RealMult.Obj.nonempty_level_complex | (intros; apply GlobalTheory.RealMult.Obj.nonempty_level_complex <;> assumption)
