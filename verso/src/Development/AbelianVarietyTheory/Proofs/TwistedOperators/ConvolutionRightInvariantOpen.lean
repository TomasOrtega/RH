import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetIntegralNormRmulLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousIntegralInvMulOfLocallyIntegrable
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CcGASmoothAndRderMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousSetIntegralConstTermOn

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConvLevel

/- English proof (translation)
Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem f hf`. Take `⟨a, -, b, hb, rfl⟩` from `hf`. Take `⟨K, hK, hb'⟩` from `GlobalTheory.Orb.exists_biinvariant hb`. Use `⟨K.comap (GlobalTheory.AdelicU.projFin D.sp.cm.sig V.gram), hK.preimage (GlobalTheory.AdelicU.continuous_projFin _ _), fun k hk hk' y => ?_⟩` and prove the remaining obligations.

Establish `h1 : GlobalTheory.AdelicU.projInf D.sp.cm.sig V.gram k = 1` using `GlobalTheory.AdelicU.mem_finPts.1 hk'`. Simplify using `only [GlobalTheory.Orb.infFin, map_mul, h1, one_mul]`. Rewrite using `[(hb' _ hk _).1]`. Consider the case `zero => exact ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩`. Consider the case `add f f' _ _ h h'`.

Take `⟨U, hU, e⟩` from `h`. Take `⟨U', hU', e'⟩` from `h'`. Conclude with `⟨U ⊓ U', hU.inter hU', fun k hk hk' y => by`. Simplify using `only [Pi.add_apply, e k hk.1 hk' y, e' k hk.2 hk' y]⟩`. Consider the case `smul c f _ h`.

Take `⟨U, hU, e⟩` from `h`. Conclude with `⟨U, hU, fun k hk hk' y => by simp only [Pi.smul_apply, e k hk hk' y]⟩`.
-/
theorem ccGA_leftInv {D : D7} {V : HSp D} {f : GA D V → ℂ} (hf : f ∈ GlobalTheory.Orb.CcGA V) :
    ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → ∀ y, f (k * y) = f y := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, -, b, hb, rfl⟩ := hf
    obtain ⟨K, hK, hb'⟩ := GlobalTheory.Orb.exists_biinvariant hb
    refine ⟨K.comap (GlobalTheory.AdelicU.projFin D.sp.cm.sig V.gram),
      hK.preimage (GlobalTheory.AdelicU.continuous_projFin _ _), fun k hk hk' y => ?_⟩
    have h1 : GlobalTheory.AdelicU.projInf D.sp.cm.sig V.gram k = 1 := GlobalTheory.AdelicU.mem_finPts.1 hk'
    simp only [GlobalTheory.Orb.infFin, map_mul, h1, one_mul]
    rw [(hb' _ hk _).1]
  | zero => exact ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩
  | add f f' _ _ h h' =>
    obtain ⟨U, hU, e⟩ := h
    obtain ⟨U', hU', e'⟩ := h'
    exact ⟨U ⊓ U', hU.inter hU', fun k hk hk' y => by
      simp only [Pi.add_apply, e k hk.1 hk' y, e' k hk.2 hk' y]⟩
  | smul c f _ h =>
    obtain ⟨U, hU, e⟩ := h
    exact ⟨U, hU, fun k hk hk' y => by simp only [Pi.smul_apply, e k hk hk' y]⟩

/- English proof (translation)
Introduce `D V μ _ _ f hf`. Take `⟨U, hU, e⟩` from `ccGA_leftInv hf`. Use `⟨U, hU, fun F k hk hk' g => ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.AutomorphicL2Unitary.convR_eq, GlobalTheory.AutomorphicL2Unitary.convR_eq]`. Use `congr 1`.

Use function extensionality and compare the values at `y`. Rewrite using `[mul_inv_rev, mul_assoc, e _ (U.inv_mem hk) ((GfC V).inv_mem hk')]`.
-/
theorem convR_level : ∀ {D : D7} {V : HSp D} (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {f : GA D V → ℂ}, f ∈ GlobalTheory.Orb.CcGA V → ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ F : GlobalTheory.AutomorphicL2Unitary.DividedPowerChartLift V μ, ∀ k ∈ U, k ∈ GfC V → ∀ g, GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) (g * k) = GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) g := by
  intro D V μ _ _ f hf
  obtain ⟨U, hU, e⟩ := ccGA_leftInv hf
  refine ⟨U, hU, fun F k hk hk' g => ?_⟩
  rw [GlobalTheory.AutomorphicL2Unitary.convR_eq, GlobalTheory.AutomorphicL2Unitary.convR_eq]
  congr 1
  funext y
  rw [mul_inv_rev, mul_assoc, e _ (U.inv_mem hk) ((GfC V).inv_mem hk')]

end GlobalTheory.ConvLevel
