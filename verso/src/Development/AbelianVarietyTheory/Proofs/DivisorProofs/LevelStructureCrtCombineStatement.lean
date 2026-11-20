import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureCrtCombine
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDPModel
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLevelStructureCrtCombine.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.level_structure_crt_combine : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S : Scheme.{0}} {X : Obj F 𝔠 S} {N N' : ℕ}, Nat.Coprime N N' → ∀ (β : X.Level N) (β' : X.Level N'),
    ∃ ξ : X.Level (N * N'), (∀ i, ξ.pt i ^ N' = β.pt i) ∧ ∀ i, ξ.pt i ^ N = β'.pt i := by
  first | exact @GlobalTheory.RealMult.Obj.Level.comb | exact GlobalTheory.RealMult.Obj.Level.comb | (intros; apply GlobalTheory.RealMult.Obj.Level.comb <;> assumption)
