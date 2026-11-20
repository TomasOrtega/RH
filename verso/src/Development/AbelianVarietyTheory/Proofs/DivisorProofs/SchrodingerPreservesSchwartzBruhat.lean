import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodingerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTerAlt

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.SchrSB

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.IterativeScalingBound.main`. Consider the case `exact _root_.GlobalTheory.IterativeScalingBound.main`. Consider the case `(apply _root_.GlobalTheory.IterativeScalingBound.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.IterativeScalingBound.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.IterativeScalingBound.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.IterativeScalingBound.main ..)`.
-/
theorem eq_one_of_pow_two_pow (z : ℂ) (h : ∀ k : ℕ, ‖z ^ (2 ^ k) - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.IterativeScalingBound.main
  | exact _root_.GlobalTheory.IterativeScalingBound.main
  | (apply _root_.GlobalTheory.IterativeScalingBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IterativeScalingBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IterativeScalingBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IterativeScalingBound.main ..)

/- English proof (translation)
Establish `hU : (⇑ψ) ⁻¹' Metric.ball 1 (1 / 2) ∈ nhds (0 : G)`. Apply `hψ.continuousAt.preimage_mem_nhds` to reduce the goal to its premises. Rewrite using `[AddChar.map_zero_eq_one]`. Conclude with `Metric.ball_mem_nhds _ (by norm_num)`. Take `⟨V, hV⟩` from `NonarchimedeanAddGroup.is_nonarchimedean _ hU`.

Establish `hker : ∀ y ∈ V, ψ y = 1`. Introduce `y hy`. Apply `eq_one_of_pow_two_pow` to reduce the goal to its premises. Introduce `k`. Establish `hm : (2 ^ k) • y ∈ V` using `V.toAddSubgroup.nsmul_mem hy _`.

Use `hV hm` as an intermediate fact. Rewrite `this` using `[Set.mem_preimage, Metric.mem_ball, dist_eq_norm, AddChar.map_nsmul_eq_pow]`. Conclude with `this`. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`.

Establish `hx : Filter.Tendsto (fun y => y - x) (nhds x) (nhds 0)`. Establish `h` using `((continuous_sub_right x).tendsto x)`. Rewrite `h` using `[sub_self]`. Then use the resulting hypothesis. Use `filter_upwards [hx (V.isOpen.mem_nhds V.zero_mem)] with y hy`. Establish `e : y = x + (y - x)` using `by abel`.

Rewrite using `[e, AddChar.map_add_eq_mul, hker _ hy, mul_one]`.
-/
theorem isLocallyConstant_addChar {G : Type} [AddCommGroup G] [TopologicalSpace G] [NonarchimedeanAddGroup G]
    (ψ : AddChar G ℂ) (hψ : Continuous ψ) : IsLocallyConstant ψ := by
  have hU : (⇑ψ) ⁻¹' Metric.ball 1 (1 / 2) ∈ nhds (0 : G) := by
    apply hψ.continuousAt.preimage_mem_nhds
    rw [AddChar.map_zero_eq_one]
    exact Metric.ball_mem_nhds _ (by norm_num)
  obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hU
  have hker : ∀ y ∈ V, ψ y = 1 := by
    intro y hy
    apply eq_one_of_pow_two_pow
    intro k
    have hm : (2 ^ k) • y ∈ V := V.toAddSubgroup.nsmul_mem hy _
    have := hV hm
    rw [Set.mem_preimage, Metric.mem_ball, dist_eq_norm, AddChar.map_nsmul_eq_pow] at this
    exact this
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hx : Filter.Tendsto (fun y => y - x) (nhds x) (nhds 0) := by
    have h := ((continuous_sub_right x).tendsto x)
    rwa [sub_self] at h
  filter_upwards [hx (V.isOpen.mem_nhds V.zero_mem)] with y hy
  have e : y = x + (y - x) := by abel
  rw [e, AddChar.map_add_eq_mul, hker _ hy, mul_one]

/- English proof (translation)
Establish `h : Continuous (GlobalTheory.LatVac.liftV v)`. Express the relevant statement in the definitionally equal form `Continuous fun a => ((0 : Ainf F), GlobalTheory.AdelicU.singleFin v a)`. Conclude with `continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v)`. Conclude with `hψ.comp h`.
-/
theorem continuous_psiAt {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ)
    (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : Continuous (GlobalTheory.LatVac.psiAt ψ v) := by
  have h : Continuous (GlobalTheory.LatVac.liftV v) := by
    change Continuous fun a => ((0 : Ainf F), GlobalTheory.AdelicU.singleFin v a)
    exact continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v)
  exact hψ.comp h

/- English proof (translation)
Introduce `F _ _ κ _ ψ hψ v w φ hφ`. Establish `hloc` using `isLocallyConstant_addChar _ (continuous_psiAt ψ hψ v)`. Establish `hlin : Continuous fun x : κ → Fv F v => x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)` using `(continuous_id.dotProduct continuous_const).add continuous_const`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `(hloc.comp_continuous hlin).mul (hφ.1.comp_continuous (continuous_add_const w.1))`.

Establish `hc : HasCompactSupport fun x : κ → Fv F v => φ (x + w.1)` using `hφ.2.comp_homeomorph (Homeomorph.addRight w.1)`. Conclude with `hc.mul_left (f := fun x => GlobalTheory.LatVac.psiAt ψ v (x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)))`.
-/
theorem schr_mem_SB : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ), Continuous ψ →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (w : (κ → Fv F v) × (κ → Fv F v)), ∀ φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v),
      GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt ψ v) w φ ∈ GlobalTheory.WeilM.SB _ := by
  intro F _ _ κ _ ψ hψ v w φ hφ
  have hloc := isLocallyConstant_addChar _ (continuous_psiAt ψ hψ v)
  have hlin : Continuous fun x : κ → Fv F v => x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2) :=
    (continuous_id.dotProduct continuous_const).add continuous_const
  refine ⟨?_, ?_⟩
  · exact (hloc.comp_continuous hlin).mul (hφ.1.comp_continuous (continuous_add_const w.1))
  · have hc : HasCompactSupport fun x : κ → Fv F v => φ (x + w.1) :=
      hφ.2.comp_homeomorph (Homeomorph.addRight w.1)
    exact hc.mul_left (f := fun x => GlobalTheory.LatVac.psiAt ψ v (x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)))

end GlobalTheory.SchrSB
