import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilEisensteinSiegelConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilSiegelFormula
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelEqTsumSchrodingerFunction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerThetaEqSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
open scoped TensorProduct ENNReal Matrix Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilThetaInt

/- English proof (translation)
Introduce `hP D A B m hm hA hw ψ χ ω hW f hf g`. Take `⟨θ, hθ⟩` from `GlobalTheory.AdelicU.exists_isInfFam D`. Take `⟨ν, 𝓨, hν⟩` from `GlobalTheory.Size.exists_isCovolOne A B`. Establish `hF` using `hW.om_pres (g, 1) f hf`. Establish `hS : GlobalTheory.Core.Rk.SW.sch ψ A B ν 𝓨 (ω (g, 1) f) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ B.rank A.rank` using `(GlobalTheory.SchSchwartzAll.schSchwartz D ψ hW.std θ hθ A B ν 𝓨 hν).1 _ hF`.

Establish `hfin` using `hP D A.rank B hA hw θ hθ m hm ⟨_, hS⟩`. Establish `hleft` using `GlobalTheory.SiegelFormula.leftInv_thetaKO hW hf g`. Establish `hcont : Continuous fun h => thetaKO ω g h f` using `(hW.om_cont f hf 0).comp (Continuous.prodMk_right g)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[autMeasure, aestronglyMeasurable_quotMeasure_iff_lift, hleft.lift_descend]`.

Conclude with `hcont.aestronglyMeasurable`. Use `lt_of_le_of_lt (lintegral_mono fun q => ?_) hfin` and prove the remaining obligations. Simplify using `only [GlobalTheory.AutomorphicL2Unitary.descend, GlobalTheory.SiegelFormula.absTheta]`. Rewrite using `[GlobalTheory.StdUnn.thetaKO_eq_tsum_sch D ψ A B χ ω hW ν 𝓨 hν f hf g]`. Conclude with `enorm_tsum_le_tsum_enorm`.
-/
theorem integrable_thetaKO : GlobalTheory.Published.WeilThetaConvergence → ∀ (D : D7) (A B : HSp D) (m : Measure (GA D B)), m.IsHaarMeasure → 1 ≤ A.rank → (Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 ∨ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χ ω → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ g, Integrable (descend (GQ B) fun h => thetaKO ω g h f) (autMeasure B m) := by
  intro hP D A B m hm hA hw ψ χ ω hW f hf g
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  obtain ⟨ν, 𝓨, hν⟩ := GlobalTheory.Size.exists_isCovolOne A B
  have hF := hW.om_pres (g, 1) f hf
  have hS : GlobalTheory.Core.Rk.SW.sch ψ A B ν 𝓨 (ω (g, 1) f) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ B.rank A.rank :=
    (GlobalTheory.SchSchwartzAll.schSchwartz D ψ hW.std θ hθ A B ν 𝓨 hν).1 _ hF
  have hfin := hP D A.rank B hA hw θ hθ m hm ⟨_, hS⟩
  have hleft := GlobalTheory.SiegelFormula.leftInv_thetaKO hW hf g
  have hcont : Continuous fun h => thetaKO ω g h f :=
    (hW.om_cont f hf 0).comp (Continuous.prodMk_right g)
  refine ⟨?_, ?_⟩
  · rw [autMeasure, aestronglyMeasurable_quotMeasure_iff_lift, hleft.lift_descend]
    exact hcont.aestronglyMeasurable
  · refine lt_of_le_of_lt (lintegral_mono fun q => ?_) hfin
    simp only [GlobalTheory.AutomorphicL2Unitary.descend, GlobalTheory.SiegelFormula.absTheta]
    rw [GlobalTheory.StdUnn.thetaKO_eq_tsum_sch D ψ A B χ ω hW ν 𝓨 hν f hf g]
    exact enorm_tsum_le_tsum_enorm

end GlobalTheory.WeilThetaInt
