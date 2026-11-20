import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

open scoped Pointwise

namespace GlobalTheory.OpConv

/- English proof (translation)
Introduce `G _ _ _ _ _ _ μ _ W _ _ σ hσ f hf f' hf' A B hA hB`. Establish `hfc : Continuous f` using `hf.1.continuous`. Establish `hf'c : Continuous f'` using `hf'.1.continuous`. Establish `horb : ∀ (l : Module.Dual ℂ W) (v : W), Continuous fun y => l (σ y v)` using `fun l v => ((hσ.isLocallyConstant_orbit v).comp l).continuous`. Use `⟨fun v l => ?_, fun g v l => ?_⟩` and prove the remaining obligations.

Establish `h0 : ∀ x y : G, (x, y) ∉ tsupport f ×ˢ (tsupport f * tsupport f') → f x * f' (x⁻¹ * y) = 0`. Introduce `x y h`. Assume the negation of the conclusion as `hne`. Establish `h1` using `subset_tsupport f (left_ne_zero_of_mul hne)`. Establish `h2` using `subset_tsupport f' (right_ne_zero_of_mul hne)`.

Conclude with `h ⟨h1, x, h1, _, h2, by simp⟩`. Establish `hK : IsCompact (tsupport f ×ˢ (tsupport f * tsupport f'))` using `hf.2.prod (hf.2.mul hf'.2)`. Establish `hcont : Continuous fun y => ∫ x, f x * f' (x⁻¹ * y) ∂μ`. Use `continuousOn_univ.1 (continuousOn_integral_of_compact_support (f := fun y x => f x * f' (x⁻¹ * y)) (s := Set.univ) hf.2 ?_ fun y x _ hx => ?_)` and prove the remaining obligations. Conclude with `((hfc.comp continuous_snd).mul (hf'c.comp (continuous_snd.inv.mul continuous_fst))).continuousOn`.

Simplify using `[image_eq_zero_of_notMem_tsupport hx]`. Establish `hcs : HasCompactSupport fun y => ∫ x, f x * f' (x⁻¹ * y) ∂μ` using `HasCompactSupport.intro (hf.2.mul hf'.2) fun y hy => by`. Simplify using `[fun x => h0 x y fun h => hy h.2]`. Establish `hF : Continuous (Function.uncurry fun x y : G => f x * f' (x⁻¹ * y) * l (σ y v))` using `((hfc.comp continuous_fst).mul (hf'c.comp (continuous_fst.inv.mul continuous_snd))).mul ((horb l v).comp continuous_snd)`. Establish `hFc : HasCompactSupport (Function.uncurry fun x y : G => f x * f' (x⁻¹ * y) * l (σ y v))` using `HasCompactSupport.intro hK fun p hp => by simp [Function.uncurry, h0 p.1 p.2 hp]`.

Establish `hconv : conv μ f f' = fun y => ∫ x, f x * f' (x⁻¹ * y) ∂μ` using `rfl`. Rewrite using `[hconv]`. Use `⟨(hcont.mul (horb l v)).integrable_of_hasCompactSupport (hcs.mul_right), ?_⟩` and prove the remaining obligations. Establish `hx : ∀ x, l (σ x (B v)) = ∫ y, f' (x⁻¹ * y) * l (σ y v) ∂μ`. Introduce `x`.

Use `(hB v (l ∘ₗ σ x)).2` as an intermediate fact. Simplify using `only [LinearMap.comp_apply] at this`. Rewrite using `[this, ← integral_mul_left_eq_self (fun y => f' (x⁻¹ * y) * l (σ y v)) x]`. Use `integral_congr_ae (.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `[map_mul, Module.End.mul_apply]`.

Rewrite using `[LinearMap.comp_apply, (hA (B v) l).2]`. Repeatedly rewrite using `[hx, ← integral_const_mul, ← mul_assoc]`. Rewrite using `[integral_integral_swap_of_hasCompactSupport hF hFc]`. Repeatedly rewrite using `[integral_mul_const]`. Establish `hx : ∀ y, f' y * l (σ g (σ y v)) = (fun x => f' (g⁻¹ * x) * l (σ x v)) (g * y)`.

Introduce `y`. Simplify using `[map_mul, Module.End.mul_apply]`. Establish `hc : Continuous fun x => f' (g⁻¹ * x) * l (σ x v)` using `(hf'c.comp (continuous_const.mul continuous_id)).mul (horb l v)`. Establish `hs : HasCompactSupport fun x => f' (g⁻¹ * x) * l (σ x v)` using `((hf'.2.comp_homeomorph (Homeomorph.mulLeft g⁻¹))).mul_right`. Use `⟨hc.integrable_of_hasCompactSupport hs, ?_⟩` and prove the remaining obligations.

Use `(hB v (l ∘ₗ σ g)).2` as an intermediate fact. Simplify using `only [LinearMap.comp_apply] at this`. Rewrite using `[LinearMap.comp_apply, this, ← integral_mul_left_eq_self (fun x => f' (g⁻¹ * x) * l (σ x v)) g]`. Conclude with `integral_congr_ae (.of_forall fun y => hx y)`.
-/
theorem isIntegralOp_conv_and_translate : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W), GlobalTheory.PRep.IsSmooth σ → ∀ f ∈ GlobalTheory.SplitWeil.SB G, ∀ f' ∈ GlobalTheory.SplitWeil.SB G, ∀ A B, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ σ f A → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ σ f' B → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ σ (conv μ f f') (A ∘ₗ B) ∧ ∀ g : G, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ σ (fun x => f' (g⁻¹ * x)) (σ g ∘ₗ B) := by
  intro G _ _ _ _ _ _ μ _ W _ _ σ hσ f hf f' hf' A B hA hB
  have hfc : Continuous f := hf.1.continuous
  have hf'c : Continuous f' := hf'.1.continuous
  have horb : ∀ (l : Module.Dual ℂ W) (v : W), Continuous fun y => l (σ y v) := fun l v =>
    ((hσ.isLocallyConstant_orbit v).comp l).continuous
  refine ⟨fun v l => ?_, fun g v l => ?_⟩
  ·
    have h0 : ∀ x y : G, (x, y) ∉ tsupport f ×ˢ (tsupport f * tsupport f') →
        f x * f' (x⁻¹ * y) = 0 := by
      intro x y h
      by_contra hne
      have h1 := subset_tsupport f (left_ne_zero_of_mul hne)
      have h2 := subset_tsupport f' (right_ne_zero_of_mul hne)
      exact h ⟨h1, x, h1, _, h2, by simp⟩
    have hK : IsCompact (tsupport f ×ˢ (tsupport f * tsupport f')) := hf.2.prod (hf.2.mul hf'.2)
    have hcont : Continuous fun y => ∫ x, f x * f' (x⁻¹ * y) ∂μ := by
      refine continuousOn_univ.1 (continuousOn_integral_of_compact_support
        (f := fun y x => f x * f' (x⁻¹ * y)) (s := Set.univ) hf.2 ?_ fun y x _ hx => ?_)
      · exact ((hfc.comp continuous_snd).mul
          (hf'c.comp (continuous_snd.inv.mul continuous_fst))).continuousOn
      · simp [image_eq_zero_of_notMem_tsupport hx]
    have hcs : HasCompactSupport fun y => ∫ x, f x * f' (x⁻¹ * y) ∂μ :=
      HasCompactSupport.intro (hf.2.mul hf'.2) fun y hy => by
        simp [fun x => h0 x y fun h => hy h.2]
    have hF : Continuous (Function.uncurry fun x y : G => f x * f' (x⁻¹ * y) * l (σ y v)) :=
      ((hfc.comp continuous_fst).mul (hf'c.comp (continuous_fst.inv.mul continuous_snd))).mul
        ((horb l v).comp continuous_snd)
    have hFc : HasCompactSupport (Function.uncurry fun x y : G => f x * f' (x⁻¹ * y) * l (σ y v)) :=
      HasCompactSupport.intro hK fun p hp => by simp [Function.uncurry, h0 p.1 p.2 hp]
    have hconv : conv μ f f' = fun y => ∫ x, f x * f' (x⁻¹ * y) ∂μ := rfl
    rw [hconv]
    refine ⟨(hcont.mul (horb l v)).integrable_of_hasCompactSupport (hcs.mul_right), ?_⟩
    have hx : ∀ x, l (σ x (B v)) = ∫ y, f' (x⁻¹ * y) * l (σ y v) ∂μ := by
      intro x
      have := (hB v (l ∘ₗ σ x)).2
      simp only [LinearMap.comp_apply] at this
      rw [this, ← integral_mul_left_eq_self (fun y => f' (x⁻¹ * y) * l (σ y v)) x]
      refine integral_congr_ae (.of_forall fun y => ?_)
      simp [map_mul, Module.End.mul_apply]
    rw [LinearMap.comp_apply, (hA (B v) l).2]
    simp_rw [hx, ← integral_const_mul, ← mul_assoc]
    rw [integral_integral_swap_of_hasCompactSupport hF hFc]
    simp_rw [integral_mul_const]
  ·
    have hx : ∀ y, f' y * l (σ g (σ y v)) = (fun x => f' (g⁻¹ * x) * l (σ x v)) (g * y) := by
      intro y
      simp [map_mul, Module.End.mul_apply]
    have hc : Continuous fun x => f' (g⁻¹ * x) * l (σ x v) :=
      (hf'c.comp (continuous_const.mul continuous_id)).mul (horb l v)
    have hs : HasCompactSupport fun x => f' (g⁻¹ * x) * l (σ x v) :=
      ((hf'.2.comp_homeomorph (Homeomorph.mulLeft g⁻¹))).mul_right
    refine ⟨hc.integrable_of_hasCompactSupport hs, ?_⟩
    have := (hB v (l ∘ₗ σ g)).2
    simp only [LinearMap.comp_apply] at this
    rw [LinearMap.comp_apply, this,
      ← integral_mul_left_eq_self (fun x => f' (g⁻¹ * x) * l (σ x v)) g]
    exact integral_congr_ae (.of_forall fun y => hx y)

end GlobalTheory.OpConv
