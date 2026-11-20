import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsTensorPower
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CoverNorm.norms_pow` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNormsTensorPower.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.norms_tensor_power : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (L : HermLB V.p) (f : Y.X → Y.Fn) (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ) (l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ) (m : ℕ), Norms V L f a l → Norms V (L.pow m) (fun x => f x ^ m) (fun σ y => m * a σ y) (fun v e y => m * l v e y) := by
  first | exact @GlobalTheory.CoverNorm.norms_pow | exact GlobalTheory.CoverNorm.norms_pow | (intros; apply GlobalTheory.CoverNorm.norms_pow <;> assumption)
