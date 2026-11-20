import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsGenFamRevInvSubfamily
import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenUIsGenFam
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl.isGenFam_revInv_ite` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FIsGenFamRevInvSubfamily.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.isGenFam_revInv_subfamily : ∀ (Ω G : Type) [Field Ω] [Field G] [Algebra Ω G] (S : Type) [Finite S] (r : S → ℕ) (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G) (P : S → Prop) [DecidablePred P], IsGenFam Ω G u → IsGenFam Ω G (fun s => if P s then revInv (u s) else u s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl.isGenFam_revInv_ite | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl.isGenFam_revInv_ite | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl.isGenFam_revInv_ite <;> assumption)
