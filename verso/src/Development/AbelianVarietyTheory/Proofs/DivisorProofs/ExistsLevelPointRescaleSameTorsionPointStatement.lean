import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointRescaleSameTorsionPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.QLevelRescale.exists_qkPt_rescale` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsLevelPointRescaleSameTorsionPoint.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.exists_levelPoint_rescale_same_torsionPoint : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (k k' d : ℕ) (pk : QkPt u.D.toPre (PadicAlgCl p) k) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), 1 ≤ k → 1 ≤ d → k' = d * k → QkToAkU u.U.toUnifPre (PadicAlgCl p) k pk x → ∃ pk' : QkPt u.D.toPre (PadicAlgCl p) k', pk'.y = d • pk.y ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) k' pk' x := by
  first | exact @GlobalTheory.QLevelRescale.exists_qkPt_rescale | exact GlobalTheory.QLevelRescale.exists_qkPt_rescale | (intros; apply GlobalTheory.QLevelRescale.exists_qkPt_rescale <;> assumption)
