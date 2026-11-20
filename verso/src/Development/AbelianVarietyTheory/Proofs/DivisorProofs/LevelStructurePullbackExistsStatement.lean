import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructurePullbackExists
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLevelStructurePullbackExists.lean&line=66#L66)
-/
theorem _root_.GlobalTheory.T.level_structure_pullback_exists : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {b : S' ⟶ S}
    {φ : X'.A.left ⟶ X.A.left}, X'.IsPullBy X b φ → ∀ {N : ℕ} (α : X.Level N),
    ∃ α' : X'.Level N, ∀ i, (α'.pt i).left ≫ φ = b ≫ (α.pt i).left := by
  first | exact @GlobalTheory.RealMult.LevelPull.exists_level_pull | exact GlobalTheory.RealMult.LevelPull.exists_level_pull | (intros; apply GlobalTheory.RealMult.LevelPull.exists_level_pull <;> assumption)
