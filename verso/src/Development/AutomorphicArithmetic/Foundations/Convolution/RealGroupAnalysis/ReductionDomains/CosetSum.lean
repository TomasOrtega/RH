import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import GroundTheory.GlobalFields.TateThesis.AdeleScaling
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.RowCosets

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

/- English proof (translation)
Introduce `F _ _ M₀ σ β u hσ hβ hu hinv`. Establish `hc` using `(UpperTheory.ConvolutionTheory.R2.M.rowCosets F).2 σ hσ`. Use `haveI := M₀.haar`. Set `e : ({r : Fin 2 → F // r ≠ 0} × F) → Gam F` to `fun p => ⟨nU (rt p.2) * ratS F (σ p.1), (Gam F).mul_mem (M.nU_rt_mem _) ⟨_, rfl⟩⟩`. Establish `he : Function.Bijective e`.

Prove the components needed by the constructor for the conclusion. Introduce `p q h`. Take `⟨p0, _, hp⟩` from `hc (e p)`. Conclude with `(hp p rfl).trans (hp q (congrArg Subtype.val h)).symm`. Introduce `γ`.

Take `⟨p, hp, _⟩` from `hc γ`. Conclude with `⟨p, Subtype.ext hp.symm⟩`. Establish `key : ∀ g : G1 F, ∑' γ : Gam F, u (γ • g) * β (γ • g) = ∑' r, u (ratS F (σ r) * g)`. Introduce `g`. Rewrite using `[← (Equiv.ofBijective e he).tsum_eq, ENNReal.tsum_prod']`.

Use `tsum_congr fun r => ?_` and prove the remaining obligations. Establish `h1 : ∀ ξ : F, u ((Equiv.ofBijective e he (r, ξ)) • g) * β ((Equiv.ofBijective e he (r, ξ)) • g) = u (ratS F (σ r) * g) * β (nU (rt ξ) * (ratS F (σ r) * g))`. Introduce `ξ`. Establish `h2 : (Equiv.ofBijective e he (r, ξ)) • g = nU (rt ξ) * (ratS F (σ r) * g)`. Express the relevant statement in the definitionally equal form `(nU (rt ξ) * ratS F (σ r)) * g = _`.

Rewrite using `[mul_assoc]`. Rewrite using `[h2, hinv]`. Repeatedly rewrite using `[h1]`. Rewrite using `[ENNReal.tsum_mul_left, hβ.2, mul_one]`. Establish `hmeas : ∀ γ : Gam F, Measurable fun g : G1 F => u (γ • g) * β (γ • g)` using `fun γ => (hu.mul hβ.1).comp (measurable_const_smul γ)`.

Rewrite using `[M₀.fund.lintegral_eq_tsum'', ← lintegral_tsum fun γ => (hmeas γ).aemeasurable]`. Conclude with `lintegral_congr key`.
-/
theorem UpperTheory.ConvolutionTheory.R2.M.cosetSum :
    ∀ (F : Type) [Field F] [NumberField F] (M₀ : Meas F) (σ) (β u : G1 F → ℝ≥0∞), M.RowSec (F := F) σ → M.NWt β → Measurable u → (∀ (ξ : F) g, u (nU (rt ξ) * g) = u g) → ∫⁻ g, u g * β g ∂M₀.μ = ∫⁻ g in M₀.D, ∑' r, u (ratS F (σ r) * g) ∂M₀.μ := by
  intro F _ _ M₀ σ β u hσ hβ hu hinv
  have hc := (UpperTheory.ConvolutionTheory.R2.M.rowCosets F).2 σ hσ
  haveI := M₀.haar
  let e : ({r : Fin 2 → F // r ≠ 0} × F) → Gam F := fun p =>
    ⟨nU (rt p.2) * ratS F (σ p.1), (Gam F).mul_mem (M.nU_rt_mem _) ⟨_, rfl⟩⟩
  have he : Function.Bijective e := by
    constructor
    · intro p q h
      obtain ⟨p0, _, hp⟩ := hc (e p)
      exact (hp p rfl).trans (hp q (congrArg Subtype.val h)).symm
    · intro γ
      obtain ⟨p, hp, _⟩ := hc γ
      exact ⟨p, Subtype.ext hp.symm⟩
  have key : ∀ g : G1 F, ∑' γ : Gam F, u (γ • g) * β (γ • g) = ∑' r, u (ratS F (σ r) * g) := by
    intro g
    rw [← (Equiv.ofBijective e he).tsum_eq, ENNReal.tsum_prod']
    refine tsum_congr fun r => ?_
    have h1 : ∀ ξ : F, u ((Equiv.ofBijective e he (r, ξ)) • g) * β ((Equiv.ofBijective e he (r, ξ)) • g)
        = u (ratS F (σ r) * g) * β (nU (rt ξ) * (ratS F (σ r) * g)) := by
      intro ξ
      have h2 : (Equiv.ofBijective e he (r, ξ)) • g = nU (rt ξ) * (ratS F (σ r) * g) := by
        change (nU (rt ξ) * ratS F (σ r)) * g = _
        rw [mul_assoc]
      rw [h2, hinv]
    simp_rw [h1]
    rw [ENNReal.tsum_mul_left, hβ.2, mul_one]
  have hmeas : ∀ γ : Gam F, Measurable fun g : G1 F => u (γ • g) * β (γ • g) := fun γ =>
    (hu.mul hβ.1).comp (measurable_const_smul γ)
  rw [M₀.fund.lintegral_eq_tsum'', ← lintegral_tsum fun γ => (hmeas γ).aemeasurable]
  exact lintegral_congr key
