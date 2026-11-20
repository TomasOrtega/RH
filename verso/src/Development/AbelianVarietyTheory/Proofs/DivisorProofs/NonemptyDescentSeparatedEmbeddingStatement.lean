import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyDescentSeparatedEmbedding
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Desc.nonempty_emb` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNonemptyDescentSeparatedEmbedding.lean&line=135#L135)
-/
theorem _root_.GlobalTheory.T.nonempty_descentSeparatedEmbedding : ∀ σ : Setup, σ.Common → Nonempty (Emb σ) := by
  first | exact @GlobalTheory.Desc.nonempty_emb | exact GlobalTheory.Desc.nonempty_emb | (intros; apply GlobalTheory.Desc.nonempty_emb <;> assumption)
