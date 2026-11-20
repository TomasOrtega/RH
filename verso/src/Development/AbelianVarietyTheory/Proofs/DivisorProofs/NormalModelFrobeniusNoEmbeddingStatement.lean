import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalModelFrobeniusNoEmbedding
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroPresZeroMod
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open GlobalTheory GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.FrobFilt
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FrobFilt.noEmb_frob_rankOne` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNormalModelFrobeniusNoEmbedding.lean&line=151#L151)
-/
theorem _root_.GlobalTheory.T.normal_model_frobenius_no_embedding : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (g : Γ(B.X, ⊤)), IsRootOfP p g p → ∀ R : Pres B, R.r = 1 → Kills g R.mod → NoEmb B ((frob p B).obj R.mod) := by
  first | exact @GlobalTheory.FrobFilt.noEmb_frob_rankOne | exact GlobalTheory.FrobFilt.noEmb_frob_rankOne | (intros; apply GlobalTheory.FrobFilt.noEmb_frob_rankOne <;> assumption)
