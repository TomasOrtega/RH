import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

/- English proof (translation)
Introduce `D A m hm u hu N`. Use `haveI := hm`. Establish `: BorelSpace (GA D A)` using `⟨rfl⟩`. Use `set f : GA D A → ℝ := fun g => GlobalTheory.Grow.quotHeight A g ^ N * ‖u g‖ with hf`. Establish `hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ A) f` using `fun γ hγ g => by`.

Simplify using `only [f, GlobalTheory.Grow.quotHeight_left A hγ, hu.left hγ]`. Establish `hfc : Continuous f` using `((GlobalTheory.Grow.continuous_quotHeight A).pow N).mul hu.continuous.norm`. Establish `e : (fun q : AutQ A => GlobalTheory.Grow.quotHeight A q.out ^ N * ‖u q.out‖) = GlobalTheory.AutomorphicL2Unitary.descend (GQ A) f` using `rfl`. Rewrite using `[e]`. Establish `hfd : IsFundamentalDomain (GQ A) (GlobalTheory.AutomorphicL2Unitary.stdDom (GQ A)) m` using `GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom _ m`.

Use `haveI : IsFiniteMeasure (GlobalTheory.AutomorphicL2Unitary.autMeasure A m) := ⟨by`. Rewrite using `[GlobalTheory.AutomorphicL2Unitary.autMeasure, GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ hfd]`. Conclude with `GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol A m _ hm hfd⟩`. Take `⟨C, hC⟩` from `hu.decay N`. Establish `hmeas : Measurable (GlobalTheory.AutomorphicL2Unitary.descend (GQ A) f)`.

Use `measurable_from_quotient.2 ?_` and prove the remaining obligations. Establish `h' : (GlobalTheory.AutomorphicL2Unitary.descend (GQ A) f ∘ Quotient.mk'') = f` using `funext fun g => hL.descend_mk g`. Rewrite using `[h']`. Conclude with `hfc.measurable`. Use `Integrable.of_bound hmeas.aestronglyMeasurable C (.of_forall fun q => ?_)` and prove the remaining obligations.

Establish `hq : 0 ≤ GlobalTheory.AutomorphicL2Unitary.descend (GQ A) f q` using `mul_nonneg (pow_nonneg (GlobalTheory.Grow.quotHeight_pos A _).le N) (norm_nonneg _)`. Rewrite using `[Real.norm_of_nonneg hq]`. Use `show GlobalTheory.Grow.quotHeight A q.out ^ N * ‖u q.out‖ ≤ C`. Rewrite using `[mul_comm]`. Conclude with `hC _`.
-/
theorem integrable_quotHeight_pow_mul_norm_of_rapidDec : ∀ (D : D7) (A : HSp D) (m : Measure (GA D A)), m.IsHaarMeasure → ∀ (u : GA D A → ℂ), GlobalTheory.Grow.RapidDec A u → ∀ N : ℕ, Integrable (fun q : AutQ A => GlobalTheory.Grow.quotHeight A q.out ^ N * ‖u q.out‖) (autMeasure A m) := by
  intro D A m hm u hu N
  haveI := hm
  have : BorelSpace (GA D A) := ⟨rfl⟩
  set f : GA D A → ℝ := fun g => GlobalTheory.Grow.quotHeight A g ^ N * ‖u g‖ with hf
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ A) f := fun γ hγ g => by
    simp only [f, GlobalTheory.Grow.quotHeight_left A hγ, hu.left hγ]
  have hfc : Continuous f := ((GlobalTheory.Grow.continuous_quotHeight A).pow N).mul hu.continuous.norm
  have e : (fun q : AutQ A => GlobalTheory.Grow.quotHeight A q.out ^ N * ‖u q.out‖) = GlobalTheory.AutomorphicL2Unitary.descend (GQ A) f := rfl
  rw [e]
  have hfd : IsFundamentalDomain (GQ A) (GlobalTheory.AutomorphicL2Unitary.stdDom (GQ A)) m := GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom _ m
  haveI : IsFiniteMeasure (GlobalTheory.AutomorphicL2Unitary.autMeasure A m) := ⟨by
    rw [GlobalTheory.AutomorphicL2Unitary.autMeasure, GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ hfd]
    exact GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol A m _ hm hfd⟩
  obtain ⟨C, hC⟩ := hu.decay N
  have hmeas : Measurable (GlobalTheory.AutomorphicL2Unitary.descend (GQ A) f) := by
    refine measurable_from_quotient.2 ?_
    have h' : (GlobalTheory.AutomorphicL2Unitary.descend (GQ A) f ∘ Quotient.mk'') = f := funext fun g => hL.descend_mk g
    rw [h']
    exact hfc.measurable
  refine Integrable.of_bound hmeas.aestronglyMeasurable C (.of_forall fun q => ?_)
  have hq : 0 ≤ GlobalTheory.AutomorphicL2Unitary.descend (GQ A) f q :=
    mul_nonneg (pow_nonneg (GlobalTheory.Grow.quotHeight_pos A _).le N) (norm_nonneg _)
  rw [Real.norm_of_nonneg hq]
  show GlobalTheory.Grow.quotHeight A q.out ^ N * ‖u q.out‖ ≤ C
  rw [mul_comm]
  exact hC _

end GlobalTheory.Core.Rk.IP
