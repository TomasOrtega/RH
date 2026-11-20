import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLast
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealTranslationCuspFormMapsEqSmoothLinearMapStatement
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ValMoveProof

/- English proof (translation)
Proceed by induction on `hT using Submodule.span_induction with`. Consider the case `mem x hx => exact hx.lev`. Consider the case `zero => intros`. Simplify using the standard rewrite rules. Consider the case `add x y _ _ hx hy`.

Introduce `v k hk g`. Simplify using `only [MultilinearMap.add_apply, Pi.add_apply, hx v k hk g, hy v k hk g, mul_add]`. Consider the case `smul a x _ hx`. Introduce `v k hk g`. Simplify using `only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hx v k hk g]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem lev_of_mem {D : D7} (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M) (hT : T ∈ Mult θ M J χ) :
    ∀ v, ∀ k ∈ J, ∀ g, T v (g * k) = χ k * T v g := by
  induction hT using Submodule.span_induction with
  | mem x hx => exact hx.lev
  | zero => intros; simp
  | add x y _ _ hx hy =>
    intro v k hk g
    simp only [MultilinearMap.add_apply, Pi.add_apply, hx v k hk g, hy v k hk g, mul_add]
  | smul a x _ hx =>
    intro v k hk g
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hx v k hk g]
    ring

/- English proof (translation)
Introduce `D θ hθ V S M J χ`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `G hG x k hk`. Rewrite `hG` using `[mem_multT]`. Establish `h` using `lev_of_mem θ M J χ _ hG`.

Establish `e : ∀ f, G (PiTensorProduct.tprod ℂ f) = (PiTensorProduct.lift.symm G) f` using `fun f => by`. Simplify using `[PiTensorProduct.lift_symm]`. Proceed by induction on `x using PiTensorProduct.induction_on with`. Consider the case `smul_tprod r f`. Use function extensionality and compare the values at `g`.

Simplify using `only [rTrans, map_smul, Pi.smul_apply, smul_eq_mul, e, h f k hk g]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `add x y hx hy`. Use function extensionality and compare the values at `g`. Establish `hx'` using `congrFun hx g`.

Establish `hy'` using `congrFun hy g`. Simplify using `only [rTrans, map_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx' hy' ⊢`. Rewrite using `[hx', hy', mul_add]`. Introduce `a ha v`. Take `⟨σ, hσ⟩` from `GlobalTheory.T.realTranslation_cuspFormMaps_eq_smooth_linear_map D θ V S M hθ a ha`.

Conclude with `⟨σ v, fun G hG => (hσ J χ G hG v).symm⟩`.
-/
theorem valMove : ∀ D : D7, ValMove D := by
  intro D θ hθ V S M J χ
  refine ⟨?_, ?_⟩
  · intro G hG x k hk
    rw [mem_multT] at hG
    have h := lev_of_mem θ M J χ _ hG
    have e : ∀ f, G (PiTensorProduct.tprod ℂ f) = (PiTensorProduct.lift.symm G) f := fun f => by
      simp [PiTensorProduct.lift_symm]
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r f =>
      funext g
      simp only [rTrans, map_smul, Pi.smul_apply, smul_eq_mul, e, h f k hk g]
      ring
    | add x y hx hy =>
      funext g
      have hx' := congrFun hx g
      have hy' := congrFun hy g
      simp only [rTrans, map_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx' hy' ⊢
      rw [hx', hy', mul_add]
  · intro a ha v
    obtain ⟨σ, hσ⟩ := GlobalTheory.T.realTranslation_cuspFormMaps_eq_smooth_linear_map D θ V S M hθ a ha
    exact ⟨σ v, fun G hG => (hσ J χ G hG v).symm⟩

end GlobalTheory.ValMoveProof

end
