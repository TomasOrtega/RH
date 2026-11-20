import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadsCompareOfScaledLocalNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FReadsCompareOfScaledLocalNorms.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.reads_compare_of_scaled_local_norms : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (C : CxSt F) (V : Cover Y) (M : HermLB V.p) (lg : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → AlgPt Y → ℝ) (r : M.B.ι → V.X.functionFieldˣ) (hr : IsRatSec M.B r), NormsX V M lg r hr → ∀ (p m : ℕ), p.Prime → ∀ (A A' : Adl C Y) (c c' : V.X → V.X.functionFieldˣ), A'.D = A.D → Reads V p A c → Reads V p A' c' → (∀ v, resP v = p → ∀ e y, lg v e y = (m : ℝ) * (A.lg v e y - A'.lg v e y)) → ∀ x, Ov p x → (M.div hr).IsEqn x ((c x / c' x) ^ m) := by
  first | exact @GlobalTheory.LatChain.isEqn_pow_div_of_reads | exact GlobalTheory.LatChain.isEqn_pow_div_of_reads | (intros; apply GlobalTheory.LatChain.isEqn_pow_div_of_reads <;> assumption)
