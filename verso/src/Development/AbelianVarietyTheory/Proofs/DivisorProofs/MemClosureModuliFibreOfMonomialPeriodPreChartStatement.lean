import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureModuliFibreOfMonomialPeriodPreChart
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMemClosureModuliFibreOfMonomialPeriodPreChart.lean&line=64#L64)
-/
theorem _root_.GlobalTheory.T.mem_closure_moduliFibre_of_monomialPeriodPreChart : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (s : S ⟶ Sp o) (j : F.X ⟶ S) [IsOpenImmersion j] (φ : InvFun ℤ) (BD : GlobalTheory.EffCartierData S) (d : ℕ) (x : S) [IsNoetherianRing o] [Smooth s], PreChart F s j φ BD d x → x ∈ closure (Set.range j ∩ s ⁻¹' {s x}) := by
  first | exact @GlobalTheory.FibreDense.mem_closure_fibre | exact GlobalTheory.FibreDense.mem_closure_fibre | (intros; apply GlobalTheory.FibreDense.mem_closure_fibre <;> assumption)
