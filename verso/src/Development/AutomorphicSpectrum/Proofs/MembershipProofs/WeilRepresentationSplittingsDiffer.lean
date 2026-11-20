import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaSumAdmissibility
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.WeilRepresentationThetaEquivarianceStatement
import GroundTheory.GlobalFields.Adele.IntegersLattice

open Matrix NumberField IsDedekindDomain GlobalTheory.WeilM MeasureTheory
open scoped TensorProduct SchwartzMap Classical

namespace GlobalTheory.CompanionTheory.SplitRatio

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Establish `hm : Measurable fun y => ‖f y‖ₑ ^ 2` using `hf.measurable.enorm.pow_const 2`. Use `((lintegral_pos_iff_support hm).mpr ?_).ne'` and prove the remaining obligations. Establish `: Function.support (fun y => ‖f y‖ₑ ^ 2) = Function.support f`. Use extensionality with `y`.

Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `hf.isOpen_support.measure_pos μ ⟨x, hx⟩`. Establish `h1 : Continuous fun y => f y ^ 2` using `hf.pow 2`. Establish `h2 : HasCompactSupport fun y => f y ^ 2` using `hc.comp_left (g := fun z : ℂ => z ^ 2) (by simp)`.

Establish `hi : Integrable (fun y => f y ^ 2) μ` using `h1.integrable_of_hasCompactSupport h2`. Use `hi.2` as an intermediate fact. Simplify using `only [HasFiniteIntegral, enorm_pow] at this`. Conclude with `this.ne`.
-/
theorem lintegral_sq_ne {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
    [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ] {f : X → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    {x : X} (hx : f x ≠ 0) : ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ ≠ 0 ∧ ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ ≠ ⊤ := by
  constructor
  · have hm : Measurable fun y => ‖f y‖ₑ ^ 2 := hf.measurable.enorm.pow_const 2
    refine ((lintegral_pos_iff_support hm).mpr ?_).ne'
    have : Function.support (fun y => ‖f y‖ₑ ^ 2) = Function.support f := by
      ext y; simp
    rw [this]
    exact hf.isOpen_support.measure_pos μ ⟨x, hx⟩
  · have h1 : Continuous fun y => f y ^ 2 := hf.pow 2
    have h2 : HasCompactSupport fun y => f y ^ 2 := hc.comp_left (g := fun z : ℂ => z ^ 2) (by simp)
    have hi : Integrable (fun y => f y ^ 2) μ := h1.integrable_of_hasCompactSupport h2
    have := hi.2
    simp only [HasFiniteIntegral, enorm_pow] at this
    exact this.ne

variable (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]

open GroundTheory.Global in

/- English proof (translation)
Set `b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F)` to `default`. Establish `hb : HasCompactSupport fun v => (b v : ℂ)` using `b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)`. Establish `hb' : ContDiff ℝ (⊤ : ℕ∞) fun v => (b v : ℂ)` using `Complex.ofRealCLM.contDiff.comp b.contDiff`. Set `f : 𝓢(κ → mixedEmbedding.mixedSpace F, ℂ)` to `hb.toSchwartzMap hb'`. Establish `hf : ∀ v, f v = (b v : ℂ)` using `fun _ => rfl`.

Establish `hg` using `ThetaAdm.indicator_mem_SB F (κ := κ)`. Use `set O := Set.univ.pi fun _ : κ => (integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) with hO`. Use `set g := O.indicator fun _ => (1 : ℂ) with hgd`. Use `⟨pureA F f g, Submodule.subset_span ⟨f, _, hg, rfl⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `(f.continuous.comp (continuous_pi fun i => ?_)).mul (hg.1.continuous.comp (continuous_pi fun i => ?_))` and prove the remaining obligations.

Conclude with `(homeomorphMixedSpace F).continuous.comp (continuous_fst.comp (continuous_apply i))`. Conclude with `continuous_snd.comp (continuous_apply i)`. Set `m : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F) → (κ → AdeleRing (𝓞 F) F)` to `fun p i => ((homeomorphMixedSpace F).symm (p.1 i), p.2 i)`. Establish `hm : Continuous m` using `continuous_pi fun i => ((homeomorphMixedSpace F).symm.continuous.comp ((continuous_apply i).comp continuous_fst)).prodMk ((continuous_apply i).comp continuous_snd)`. Use `HasCompactSupport.intro ((hb.isCompact.prod hg.2.isCompact).image hm) fun x hx => ?_` and prove the remaining obligations.

Assume the negation of the conclusion as `h`. Take `⟨h1, h2⟩` from `mul_ne_zero_iff.mp h`. Use `hx ⟨(_, _), ⟨subset_tsupport _ h1, subset_tsupport _ h2⟩, funext fun i => ?_⟩` and prove the remaining obligations. Conclude with `Prod.ext ((homeomorphMixedSpace F).symm_apply_apply (x i).1) rfl`. Establish `h0 : (fun i : κ => ((0 : κ → AdeleRing (𝓞 F) F) i).2) ∈ O` using `fun i _ => Subring.zero_mem _`.

Establish `h1 : (fun i : κ => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AdeleRing (𝓞 F) F) i).1) = 0`. Use function extensionality and compare the values at `fun i => map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)`. Rewrite using `[pureA, h1, hf, hgd, Set.indicator_of_mem h0, b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]`. Simplify using the standard rewrite rules.
-/
theorem exists_schA_compact : ∃ Φ ∈ schA F κ, Continuous Φ ∧ HasCompactSupport Φ ∧ Φ 0 ≠ 0 := by
  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := default
  have hb : HasCompactSupport fun v => (b v : ℂ) := b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hb' : ContDiff ℝ (⊤ : ℕ∞) fun v => (b v : ℂ) := Complex.ofRealCLM.contDiff.comp b.contDiff
  let f : 𝓢(κ → mixedEmbedding.mixedSpace F, ℂ) := hb.toSchwartzMap hb'
  have hf : ∀ v, f v = (b v : ℂ) := fun _ => rfl
  have hg := ThetaAdm.indicator_mem_SB F (κ := κ)
  set O := Set.univ.pi fun _ : κ => (integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) with hO
  set g := O.indicator fun _ => (1 : ℂ) with hgd
  refine ⟨pureA F f g, Submodule.subset_span ⟨f, _, hg, rfl⟩, ?_, ?_, ?_⟩
  · refine (f.continuous.comp (continuous_pi fun i => ?_)).mul (hg.1.continuous.comp (continuous_pi fun i => ?_))
    · exact (homeomorphMixedSpace F).continuous.comp (continuous_fst.comp (continuous_apply i))
    · exact continuous_snd.comp (continuous_apply i)
  · let m : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F) → (κ → AdeleRing (𝓞 F) F) :=
      fun p i => ((homeomorphMixedSpace F).symm (p.1 i), p.2 i)
    have hm : Continuous m := continuous_pi fun i =>
      ((homeomorphMixedSpace F).symm.continuous.comp ((continuous_apply i).comp continuous_fst)).prodMk
        ((continuous_apply i).comp continuous_snd)
    refine HasCompactSupport.intro ((hb.isCompact.prod hg.2.isCompact).image hm) fun x hx => ?_
    by_contra h
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp h
    refine hx ⟨(_, _), ⟨subset_tsupport _ h1, subset_tsupport _ h2⟩, funext fun i => ?_⟩
    exact Prod.ext ((homeomorphMixedSpace F).symm_apply_apply (x i).1) rfl
  · have h0 : (fun i : κ => ((0 : κ → AdeleRing (𝓞 F) F) i).2) ∈ O := fun i _ => Subring.zero_mem _
    have h1 : (fun i : κ => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AdeleRing (𝓞 F) F) i).1) = 0 :=
      funext fun i => map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    rw [pureA, h1, hf, hgd, Set.indicator_of_mem h0,
      b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]
    simp

/- English proof (translation)
Introduce `F _ _ _ _ κ _ ψ hψc hψ1 hψF V _ _ B d G _ _ act om om' _ h h'`. Establish `pres : ∀ g, ∀ Φ ∈ schA F κ, om g Φ ∈ schA F κ` using `h.pres`. Establish `pres' : ∀ g, ∀ Φ ∈ schA F κ, om' g Φ ∈ schA F κ` using `h'.pres`. Establish `inv1 : ∀ g Φ, om g (om g⁻¹ Φ) = Φ` using `fun g Φ => by`. Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`.

Establish `inv2 : ∀ g Φ, om g⁻¹ (om g Φ) = Φ` using `fun g Φ => by simpa using inv1 g⁻¹ Φ`. Establish `hs : ∀ g, ∃ a : ℂ, ∀ Φ ∈ schA F κ, om' g Φ = a • om g Φ`. Introduce `g`. Take `⟨a, ha⟩` from `GlobalTheory.T.heisenberg_commuting_operator_scalar F κ ψ hψc hψ1 hψF (om g⁻¹ * om' g) (fun Φ hΦ => pres _ _ (pres' _ _ hΦ)) (fun l hl => h'.adm g _ (h.adm g⁻¹ l hl)) (fun w Φ hΦ => by`. Take `⟨v, rfl⟩` from `d.e.surjective w`.

Establish `e1` using `h'.impl g v Φ hΦ`. Establish `e2` using `h.impl g v _ (pres g⁻¹ _ (pres' g Φ hΦ))`. Rewrite `e2` using `[inv1]`. Use `show om g⁻¹ (om' g (d.rho ψ v Φ)) = d.rho ψ v (om g⁻¹ (om' g Φ))`. Rewrite using `[e1, ← e2, inv2])`.

Use `⟨a, fun Φ hΦ => ?_⟩` and prove the remaining obligations. Rewrite using `[← map_smul, ← ha Φ hΦ, Module.End.mul_apply, inv1]`. Use `choose a ha using hs`. Take `⟨-, ⟨l, hl, hlθ⟩, Φ₀, hΦ₀, hθ⟩` from `ThetaAdm.theta_adm F κ`. Establish `hl0 : l Φ₀ ≠ 0` using `by rwa [hlθ _ hΦ₀]`.

Establish `hne : Φ₀ ≠ 0` using `fun e => hl0 (by rw [e, map_zero])`. Establish `hn : ∀ g, ‖a g‖ = 1`. Introduce `g`. Take `⟨Φ, hΦ, hc, hk, h0⟩` from `exists_schA_compact F κ`. Use `borelize (κ → AdeleRing (𝓞 F) F)`.

Take `⟨e0, e1⟩` from `lintegral_sq_ne (Measure.addHaar) hc hk h0`. Conclude with `h.unit.norm_eq_one h'.unit (μ := Measure.addHaar) inferInstance hΦ e0 e1 (ha g Φ hΦ)`. Establish `hmul : ∀ g g', a (g * g') = a g * a g'`. Introduce `g g'`. Establish `e` using `ha (g * g') Φ₀ hΦ₀`.

Rewrite `e` using `[map_mul om', Module.End.mul_apply, ha g' _ hΦ₀, map_smul, ha g _ (pres _ _ hΦ₀), smul_smul, ← Module.End.mul_apply, ← map_mul]`. Establish `hz : om (g * g') Φ₀ ≠ 0` using `fun z => hne (by rw [← inv2 (g * g') Φ₀, z, map_zero])`. Rewrite using `[← smul_left_injective ℂ hz e, mul_comm]`. Establish `hcont : Continuous a`. Rewrite using `[continuous_iff_continuousAt]`.

Introduce `g`. Establish `hΦ` using `pres g⁻¹ _ hΦ₀`. Establish `c1` using `h.cont l hl _ hΦ`. Establish `c2` using `h'.cont l hl _ hΦ`. Establish `n0 : l (om g (om g⁻¹ Φ₀)) ≠ 0` using `by rwa [inv1]`.

Use `(c2.continuousAt.div c1.continuousAt n0).congr ?_` and prove the remaining obligations. Use `filter_upwards [c1.continuousAt.eventually_ne n0] with x hx`. Rewrite using `[Pi.div_apply, ha x _ hΦ, map_smul, smul_eq_mul, mul_div_assoc, div_self hx, mul_one]`. Set `ν : G →* Circle` to `MonoidHom.mk' (fun g => ⟨a g, by simpa [Submonoid.unitSphere] using hn g⟩) (fun g g' => Circle.ext (hmul g g'))`. Use `⟨ν, hcont.subtype_mk _, ha, fun g t t' => Circle.ext ?_⟩` and prove the remaining obligations.

Establish `e` using `t' Φ₀ hΦ₀`. Rewrite `e` using `[← hlθ _ (pres' _ _ hΦ₀), ha g _ hΦ₀, map_smul, hlθ _ (pres _ _ hΦ₀), t _ hΦ₀, smul_eq_mul]`. Conclude with `(mul_eq_right₀ hθ).mp e`.
-/
theorem exists_ratio : ∀ (F : Type) [Field F] [NumberField F] [LocallyCompactSpace (AdeleRing (𝓞 F) F)] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), Continuous ψ → ψ ≠ 1 → (∀ a : F, ψ (algebraMap F (AdeleRing (𝓞 F) F) a) = 1) → ∀ (V : Type) [AddCommGroup V] [Module (AdeleRing (𝓞 F) F) V] (B : V → V → AdeleRing (𝓞 F) F) (d : Darboux B κ) (G : Type) [Group G] [TopologicalSpace G] (act : G → V → V) (om om' : G →* Module.End ℂ ((κ → AdeleRing (𝓞 F) F) → ℂ)), (∀ g, Function.Surjective (act g)) → IsUSplitting (adeleClass F) ψ d act om → IsUSplitting (adeleClass F) ψ d act om' → ∃ ν : G →* Circle, Continuous ν ∧ (∀ g, ∀ Φ ∈ schA F κ, om' g Φ = (ν g : ℂ) • om g Φ) ∧ ∀ g, (∀ Φ ∈ schA F κ, thetaSum F (om g Φ) = thetaSum F Φ) → (∀ Φ ∈ schA F κ, thetaSum F (om' g Φ) = thetaSum F Φ) → ν g = 1 := by
  intro F _ _ _ _ κ _ ψ hψc hψ1 hψF V _ _ B d G _ _ act om om' _ h h'
  have pres : ∀ g, ∀ Φ ∈ schA F κ, om g Φ ∈ schA F κ := h.pres
  have pres' : ∀ g, ∀ Φ ∈ schA F κ, om' g Φ ∈ schA F κ := h'.pres
  have inv1 : ∀ g Φ, om g (om g⁻¹ Φ) = Φ := fun g Φ => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have inv2 : ∀ g Φ, om g⁻¹ (om g Φ) = Φ := fun g Φ => by simpa using inv1 g⁻¹ Φ
  have hs : ∀ g, ∃ a : ℂ, ∀ Φ ∈ schA F κ, om' g Φ = a • om g Φ := by
    intro g
    obtain ⟨a, ha⟩ := GlobalTheory.T.heisenberg_commuting_operator_scalar F κ ψ hψc hψ1 hψF (om g⁻¹ * om' g)
      (fun Φ hΦ => pres _ _ (pres' _ _ hΦ)) (fun l hl => h'.adm g _ (h.adm g⁻¹ l hl)) (fun w Φ hΦ => by
        obtain ⟨v, rfl⟩ := d.e.surjective w
        have e1 := h'.impl g v Φ hΦ
        have e2 := h.impl g v _ (pres g⁻¹ _ (pres' g Φ hΦ))
        rw [inv1] at e2
        show om g⁻¹ (om' g (d.rho ψ v Φ)) = d.rho ψ v (om g⁻¹ (om' g Φ))
        rw [e1, ← e2, inv2])
    refine ⟨a, fun Φ hΦ => ?_⟩
    rw [← map_smul, ← ha Φ hΦ, Module.End.mul_apply, inv1]
  choose a ha using hs
  obtain ⟨-, ⟨l, hl, hlθ⟩, Φ₀, hΦ₀, hθ⟩ := ThetaAdm.theta_adm F κ
  have hl0 : l Φ₀ ≠ 0 := by rwa [hlθ _ hΦ₀]
  have hne : Φ₀ ≠ 0 := fun e => hl0 (by rw [e, map_zero])
  have hn : ∀ g, ‖a g‖ = 1 := by
    intro g
    obtain ⟨Φ, hΦ, hc, hk, h0⟩ := exists_schA_compact F κ
    borelize (κ → AdeleRing (𝓞 F) F)
    obtain ⟨e0, e1⟩ := lintegral_sq_ne (Measure.addHaar) hc hk h0
    exact h.unit.norm_eq_one h'.unit (μ := Measure.addHaar) inferInstance hΦ e0 e1 (ha g Φ hΦ)
  have hmul : ∀ g g', a (g * g') = a g * a g' := by
    intro g g'
    have e := ha (g * g') Φ₀ hΦ₀
    rw [map_mul om', Module.End.mul_apply, ha g' _ hΦ₀, map_smul, ha g _ (pres _ _ hΦ₀), smul_smul,
      ← Module.End.mul_apply, ← map_mul] at e
    have hz : om (g * g') Φ₀ ≠ 0 := fun z => hne (by rw [← inv2 (g * g') Φ₀, z, map_zero])
    rw [← smul_left_injective ℂ hz e, mul_comm]
  have hcont : Continuous a := by
    rw [continuous_iff_continuousAt]
    intro g
    have hΦ := pres g⁻¹ _ hΦ₀
    have c1 := h.cont l hl _ hΦ
    have c2 := h'.cont l hl _ hΦ
    have n0 : l (om g (om g⁻¹ Φ₀)) ≠ 0 := by rwa [inv1]
    refine (c2.continuousAt.div c1.continuousAt n0).congr ?_
    filter_upwards [c1.continuousAt.eventually_ne n0] with x hx
    rw [Pi.div_apply, ha x _ hΦ, map_smul, smul_eq_mul, mul_div_assoc, div_self hx, mul_one]
  let ν : G →* Circle := MonoidHom.mk' (fun g => ⟨a g, by simpa [Submonoid.unitSphere] using hn g⟩)
    (fun g g' => Circle.ext (hmul g g'))
  refine ⟨ν, hcont.subtype_mk _, ha, fun g t t' => Circle.ext ?_⟩
  have e := t' Φ₀ hΦ₀
  rw [← hlθ _ (pres' _ _ hΦ₀), ha g _ hΦ₀, map_smul, hlθ _ (pres _ _ hΦ₀), t _ hΦ₀, smul_eq_mul] at e
  exact (mul_eq_right₀ hθ).mp e

end GlobalTheory.CompanionTheory.SplitRatio
