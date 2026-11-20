import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemKFinOfMemLowT
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KFiniteLevel

/- English proof (translation)
Introduce `D V S M θ hθ J χ hJ F hF hk`. Rewrite `hF`, the goal using `[mem_multT, GlobalTheory.MultMem.mem_mult_iff]`. Use `set T : MMap M := PiTensorProduct.lift.symm F with hTdef`. Establish `hT : ∀ v : M.Vec, T v = F (PiTensorProduct.tprod ℂ v)` using `fun v => by`. Rewrite using `[hTdef, PiTensorProduct.lift_symm]`.

Both sides reduce to the same expression. Use `⟨hF.aut, hF.cusp, fun v κ hκ g => ?_, hF.equiv, hF.cont⟩` and prove the remaining obligations. Use `set U : MMap M := heckeOn M {κ} T - χ κ • T with hUdef`. Establish `hU : U ∈ Mult θ M ∅ 1` using `sub_mem ((GlobalTheory.MultMem.mem_mult_iff ..).2 (GlobalTheory.SphericalOps.isMultMap_single hF (hJ κ hκ))) (Submodule.smul_mem _ _ ((GlobalTheory.MultMem.mem_mult_iff ..).2 hF))`. Establish `hUv : ∀ (u : M.Vec) (x : GA D V), U u x = T u (x * κ) - χ κ * T u x` using `fun u x => by`.

Simplify using `[hUdef, heckeOn, postOn_apply, heckeLin_apply]`. Establish `h0 : U = 0` using `GlobalTheory.KFiniteDetermined.restrInj D θ hθ V S M ∅ 1 U hU fun u hu => by`. Use function extensionality and compare the values at `x`. Rewrite using `[hUv, hT, Pi.zero_apply, sub_eq_zero]`. Conclude with `hk _ (Submodule.subset_span ⟨u, fun τ => Submodule.subset_span (hu τ), rfl⟩) κ hκ x`.

Use `hUv v g` as an intermediate fact. Rewrite `this` using `[h0]`. Conclude with `(sub_eq_zero.1 this.symm)`.
-/
theorem mem_multT_of_kfin : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (θ : InfFam D), IsInfFam θ → ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), (∀ κ ∈ J, κ ∈ GfC V) → ∀ F ∈ MultT θ M ∅ 1, (∀ w ∈ (Submodule.span ℂ {w : SmT M | ∃ v : (M).Vec, (∀ τ, (v τ : (M).H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧ w = PiTensorProduct.tprod ℂ v}), ∀ κ ∈ J, ∀ g, F w (g * κ) = χ κ * F w g) → F ∈ MultT θ M J χ := by
  intro D V S M θ hθ J χ hJ F hF hk
  rw [mem_multT, GlobalTheory.MultMem.mem_mult_iff] at hF ⊢
  set T : MMap M := PiTensorProduct.lift.symm F with hTdef
  have hT : ∀ v : M.Vec, T v = F (PiTensorProduct.tprod ℂ v) := fun v => by
    rw [hTdef, PiTensorProduct.lift_symm]; rfl
  refine ⟨hF.aut, hF.cusp, fun v κ hκ g => ?_, hF.equiv, hF.cont⟩
  set U : MMap M := heckeOn M {κ} T - χ κ • T with hUdef
  have hU : U ∈ Mult θ M ∅ 1 :=
    sub_mem ((GlobalTheory.MultMem.mem_mult_iff ..).2 (GlobalTheory.SphericalOps.isMultMap_single hF (hJ κ hκ)))
      (Submodule.smul_mem _ _ ((GlobalTheory.MultMem.mem_mult_iff ..).2 hF))
  have hUv : ∀ (u : M.Vec) (x : GA D V), U u x = T u (x * κ) - χ κ * T u x := fun u x => by
    simp [hUdef, heckeOn, postOn_apply, heckeLin_apply]
  have h0 : U = 0 := GlobalTheory.KFiniteDetermined.restrInj D θ hθ V S M ∅ 1 U hU fun u hu => by
    funext x
    rw [hUv, hT, Pi.zero_apply, sub_eq_zero]
    exact hk _ (Submodule.subset_span ⟨u, fun τ => Submodule.subset_span (hu τ), rfl⟩) κ hκ x
  have := hUv v g
  rw [h0] at this
  exact (sub_eq_zero.1 this.symm)

end GlobalTheory.KFiniteLevel
