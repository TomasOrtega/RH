import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerIntegralBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigALocalPartProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.ConeSliceWeak

open GlobalTheory.HeisSchA GlobalTheory.Published.Metaplectic GlobalTheory.ConeMeasV GlobalTheory.ConeMeasSmall

/- English proof (translation)
Use `haveI : BarrelledSpace ℂ (SchwartzMap V ℂ) := GlobalTheory.schwartzMap_barrelledSpace V`. Take `⟨C, hC, hCn⟩` from `exists_compact_mem_nhds k₀`. Set `N : C → SchwartzMap V ℂ →L[ℂ] ℂ` to `fun k => M k`. Establish `hUE : UniformEquicontinuous ((↑) ∘ N)` using `(norm_withSeminorms ℂ ℂ).banach_steinhaus fun q x => by`. Establish `hc : Continuous fun k : K => ‖M k x‖` using `(hM x).norm`.

Use `hC.bddAbove_image hc.continuousOn` as an intermediate fact. Rewrite `this` using `[Set.image_eq_range]`. Conclude with `this`. Establish `h1 : Tendsto (fun i => M (κ i) (u i - f₀)) 𝓕 (𝓝 0)`. Establish `hE` using `hUE.equicontinuous 0`.

Rewrite using `[Metric.tendsto_nhds]`. Introduce `ε hε`. Establish `ev` using `(Metric.equicontinuousAt_iff_right.1 hE) ε hε`. Establish `hz : Tendsto (fun i => u i - f₀) 𝓕 (𝓝 0)` using `by simpa using hu.sub_const f₀`. Use `filter_upwards [hz.eventually ev, hκ.eventually hCn] with i hi hi'`.

Use `hi ⟨κ i, hi'⟩` as an intermediate fact. Rewrite using `[dist_comm]`. Simplify `this` using `[N]`. Establish `h2` using `h1.add (((hM f₀).tendsto k₀).comp hκ)`. Rewrite `h2` using `[zero_add]`.

Use `h2.congr fun i => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem tendsto_apply {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {K : Type} [TopologicalSpace K] [WeaklyLocallyCompactSpace K] (M : K → SchwartzMap V ℂ →L[ℂ] ℂ)
    (hM : ∀ f, Continuous fun k => M k f) {ι : Type} {𝓕 : Filter ι} {κ : ι → K} {k₀ : K} (hκ : Tendsto κ 𝓕 (𝓝 k₀))
    {u : ι → SchwartzMap V ℂ} {f₀ : SchwartzMap V ℂ} (hu : Tendsto u 𝓕 (𝓝 f₀)) :
    Tendsto (fun i => M (κ i) (u i)) 𝓕 (𝓝 (M k₀ f₀)) := by
  haveI : BarrelledSpace ℂ (SchwartzMap V ℂ) := GlobalTheory.schwartzMap_barrelledSpace V
  obtain ⟨C, hC, hCn⟩ := exists_compact_mem_nhds k₀
  let N : C → SchwartzMap V ℂ →L[ℂ] ℂ := fun k => M k
  have hUE : UniformEquicontinuous ((↑) ∘ N) := (norm_withSeminorms ℂ ℂ).banach_steinhaus fun q x => by
    have hc : Continuous fun k : K => ‖M k x‖ := (hM x).norm
    have := hC.bddAbove_image hc.continuousOn
    rw [Set.image_eq_range] at this
    exact this
  have h1 : Tendsto (fun i => M (κ i) (u i - f₀)) 𝓕 (𝓝 0) := by
    have hE := hUE.equicontinuous 0
    rw [Metric.tendsto_nhds]
    intro ε hε
    have ev := (Metric.equicontinuousAt_iff_right.1 hE) ε hε
    have hz : Tendsto (fun i => u i - f₀) 𝓕 (𝓝 0) := by simpa using hu.sub_const f₀
    filter_upwards [hz.eventually ev, hκ.eventually hCn] with i hi hi'
    have := hi ⟨κ i, hi'⟩
    rw [dist_comm]
    simpa [N] using this
  have h2 := h1.add (((hM f₀).tendsto k₀).comp hκ)
  rw [zero_add] at h2
  refine h2.congr fun i => ?_
  simp

def heisS {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) (p : (V →L[ℝ] ℝ) × ℝ × V) :
    SchwartzMap V ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun y => eChar (p.1 y + p.2.1)) (SchwartzMap.compSubConstCLM ℂ (-p.2.2) f)

/- English proof (translation)
Establish `htg : Function.HasTemperateGrowth (fun y => eChar (p.1 y + p.2.1))` using `hasTemperateGrowth_eChar.comp (p.1.hasTemperateGrowth.add (Function.HasTemperateGrowth.const _))`. Rewrite using `[heisS, SchwartzMap.smulLeftCLM_apply_apply htg, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, smul_eq_mul]`.
-/
theorem heisS_apply {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ)
    (p : (V →L[ℝ] ℝ) × ℝ × V) (y : V) : heisS f p y = eChar (p.1 y + p.2.1) * f (y + p.2.2) := by
  have htg : Function.HasTemperateGrowth (fun y => eChar (p.1 y + p.2.1)) :=
    hasTemperateGrowth_eChar.comp (p.1.hasTemperateGrowth.add (Function.HasTemperateGrowth.const _))
  rw [heisS, SchwartzMap.smulLeftCLM_apply_apply htg, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, smul_eq_mul]

/- English proof (translation)
Use `haveI : ProperSpace ((V →L[ℝ] ℝ) × ℝ × V) := FiniteDimensional.proper_real _`. Use `GlobalTheory.ArchWeilCont.continuous_of_weak _ fun T => continuous_iff_continuousAt.2 fun p₀ => ?_` and prove the remaining obligations. Establish `c1 : Continuous fun p : (V →L[ℝ] ℝ) × ℝ × V => p.1 - p₀.1` using `by fun_prop`. Establish `c2 : Continuous fun p : (V →L[ℝ] ℝ) × ℝ × V => p.2.1 - p₀.2.1 - p₀.1 (p.2.2 - p₀.2.2)` using `by fun_prop`. Establish `c3 : Continuous fun p : (V →L[ℝ] ℝ) × ℝ × V => p.2.2 - p₀.2.2` using `by fun_prop`.

Establish `h` using `tendsto_heis T (heisS f p₀) (c1.tendsto' p₀ 0 (by simp)) (c2.tendsto' p₀ 0 (by simp)) (c3.tendsto' p₀ 0 (by simp))`. Use `h.congr fun p => congrArg T ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `heisS (heisS f p₀) (p.1 - p₀.1, p.2.1 - p₀.2.1 - p₀.1 (p.2.2 - p₀.2.2), p.2.2 - p₀.2.2) = heisS f p`. Use extensionality with `y`. Rewrite using `[heisS_apply, heisS_apply, heisS_apply, ← mul_assoc, eChar_apply, eChar_apply, eChar_apply, ← Complex.exp_add]`.

Use `congr 2`. Simplify using `only [ContinuousLinearMap.sub_apply, map_add, map_sub]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `show y + (p.2.2 - p₀.2.2) + p₀.2.2 = y + p.2.2`.

Rewrite using `[add_assoc, sub_add_cancel]`.
-/
theorem continuous_heisS {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (f : SchwartzMap V ℂ) : Continuous (heisS f) := by
  haveI : ProperSpace ((V →L[ℝ] ℝ) × ℝ × V) := FiniteDimensional.proper_real _
  refine GlobalTheory.ArchWeilCont.continuous_of_weak _ fun T => continuous_iff_continuousAt.2 fun p₀ => ?_
  have c1 : Continuous fun p : (V →L[ℝ] ℝ) × ℝ × V => p.1 - p₀.1 := by fun_prop
  have c2 : Continuous fun p : (V →L[ℝ] ℝ) × ℝ × V => p.2.1 - p₀.2.1 - p₀.1 (p.2.2 - p₀.2.2) := by fun_prop
  have c3 : Continuous fun p : (V →L[ℝ] ℝ) × ℝ × V => p.2.2 - p₀.2.2 := by fun_prop
  have h := tendsto_heis T (heisS f p₀) (c1.tendsto' p₀ 0 (by simp)) (c2.tendsto' p₀ 0 (by simp))
    (c3.tendsto' p₀ 0 (by simp))
  refine h.congr fun p => congrArg T ?_
  change heisS (heisS f p₀) (p.1 - p₀.1, p.2.1 - p₀.2.1 - p₀.1 (p.2.2 - p₀.2.2), p.2.2 - p₀.2.2) = heisS f p
  ext y
  rw [heisS_apply, heisS_apply, heisS_apply, ← mul_assoc, eChar_apply, eChar_apply, eChar_apply, ← Complex.exp_add]
  congr 2
  · simp only [ContinuousLinearMap.sub_apply, map_add, map_sub]
    push_cast
    ring
  · show y + (p.2.2 - p₀.2.2) + p₀.2.2 = y + p.2.2
    rw [add_assoc, sub_add_cancel]

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

/- English proof (translation)
Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `zero => simpa using tendsto_const_nhds`. Consider the case `add Φ Ψ _ _ h1 h2 => simpa only [map_add] using h1.add h2`. Consider the case `smul c Φ _ h => simpa only [map_smul] using h.const_smul c`. Consider the case `mem Φ h`.

Take `⟨f, g, hg, rfl⟩` from `h`. Use `choose T hT using fun k => hl k g hg`. Establish `hTc : ∀ f, Continuous fun k => T k f` using `fun f => (hc _ (Submodule.subset_span ⟨f, g, hg, rfl⟩)).congr fun k => hT k f`. Establish `hh : Continuous fun w : (κ → AF F) × (κ → AF F) => ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)` using `continuous_const.mul (continuous_fst.dotProduct continuous_snd)`. Establish `cfin : Continuous fun w : (κ → AF F) × (κ → AF F) => ((fun i => p2 (w.2 i), fun i => p2 (w.1 i), p2 (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2))) : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) × FiniteAdeleRing (𝓞 F) F)` using `(continuous_pi fun i => continuous_p2.comp ((continuous_apply i).comp continuous_snd)).prodMk ((continuous_pi fun i => continuous_p2.comp ((continuous_apply i).comp continuous_fst)).prodMk (continuous_p2.comp hh))`.

Establish `hfin` using `(cfin.tendsto' 0 0 (by`. Use `Prod.ext (funext fun i => map_zero _) (Prod.ext (funext fun i => map_zero _) ?_)` and prove the remaining obligations. Use the proof step `simp)).eventually (eventually_fixed (finChar ψ) (finChar_isLocallyConstant ψ hψ.1) hg)`. Establish `c1 : Continuous fun w : (κ → AF F) × (κ → AF F) => fun i => qA (w.1 i)` using `continuous_pi fun i => continuous_qA.comp ((continuous_apply i).comp continuous_fst)`. Establish `c2 : Continuous fun w : (κ → AF F) × (κ → AF F) => -trL fun i => qA (w.2 i)` using `(continuous_trL.comp (continuous_pi fun i => continuous_qA.comp ((continuous_apply i).comp continuous_snd))).neg`.

Establish `c3 : Continuous fun w : (κ → AF F) × (κ → AF F) => -Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (qA (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)))` using `((Algebra.trace ℝ (mixedEmbedding.mixedSpace F)).continuous_of_finiteDimensional.comp (continuous_qA.comp hh)).neg`. Establish `c4` using `(continuous_heisS f).comp (c2.prodMk (c3.prodMk c1))`. Establish `t4` using `c4.tendsto' 0 f (by`. Use extensionality with `y`. Simplify using `[heisS_apply, trL_apply, dotProduct, eChar_apply]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Use the proof step `simp)`. Establish `hsnd : Tendsto (Prod.snd : K × ((κ → AF F) × (κ → AF F)) → _) (𝓝 (k₀, 0)) (𝓝 0)` using `continuous_snd.tendsto _`. Establish `hfst : Tendsto (Prod.fst : K × ((κ → AF F) × (κ → AF F)) → _) (𝓝 (k₀, 0)) (𝓝 k₀)` using `continuous_fst.tendsto _`.

Use `tendsto_apply T hTc hfst (t4.comp hsnd)` as an intermediate fact. Rewrite using `[hT]`. Use `this.congr' ((hsnd.eventually hfin).mono fun p hw => ?_)` and prove the remaining obligations. Establish `e : finS ψ g (fun i => p2 (p.2.2 i)) (fun i => p2 (p.2.1 i)) (p2 (⅟(2 : AF F) * (p.2.1 ⬝ᵥ p.2.2))) = g`. Use function extensionality and compare the values at `hw`.

Use `show _ = l p.1 (schr ψ p.2 (pureA F f g))`. Rewrite using `[schr_pureA_eq hψ, e, hT]`. Both sides reduce to the same expression.
-/
theorem tendsto_family_zero {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {K : Type} [TopologicalSpace K]
    [WeaklyLocallyCompactSpace K] (l : K → ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (hl : ∀ k, l k ∈ (adeleClass F).adm κ)
    (hc : ∀ Φ ∈ schA F κ, Continuous fun k => l k Φ) (k₀ : K) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    Tendsto (fun p : K × ((κ → AF F) × (κ → AF F)) => l p.1 (schrLin ψ p.2 Φ)) (𝓝 (k₀, 0)) (𝓝 (l k₀ Φ)) := by
  induction hΦ using Submodule.span_induction with
  | zero => simpa using tendsto_const_nhds
  | add Φ Ψ _ _ h1 h2 => simpa only [map_add] using h1.add h2
  | smul c Φ _ h => simpa only [map_smul] using h.const_smul c
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    choose T hT using fun k => hl k g hg
    have hTc : ∀ f, Continuous fun k => T k f := fun f =>
      (hc _ (Submodule.subset_span ⟨f, g, hg, rfl⟩)).congr fun k => hT k f
    have hh : Continuous fun w : (κ → AF F) × (κ → AF F) => ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2) :=
      continuous_const.mul (continuous_fst.dotProduct continuous_snd)
    have cfin : Continuous fun w : (κ → AF F) × (κ → AF F) =>
        ((fun i => p2 (w.2 i), fun i => p2 (w.1 i), p2 (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2))) :
          (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) × FiniteAdeleRing (𝓞 F) F) :=
      (continuous_pi fun i => continuous_p2.comp ((continuous_apply i).comp continuous_snd)).prodMk
        ((continuous_pi fun i => continuous_p2.comp ((continuous_apply i).comp continuous_fst)).prodMk
          (continuous_p2.comp hh))
    have hfin := (cfin.tendsto' 0 0 (by
      refine Prod.ext (funext fun i => map_zero _) (Prod.ext (funext fun i => map_zero _) ?_)
      simp)).eventually (eventually_fixed (finChar ψ) (finChar_isLocallyConstant ψ hψ.1) hg)
    have c1 : Continuous fun w : (κ → AF F) × (κ → AF F) => fun i => qA (w.1 i) :=
      continuous_pi fun i => continuous_qA.comp ((continuous_apply i).comp continuous_fst)
    have c2 : Continuous fun w : (κ → AF F) × (κ → AF F) => -trL fun i => qA (w.2 i) :=
      (continuous_trL.comp (continuous_pi fun i => continuous_qA.comp ((continuous_apply i).comp continuous_snd))).neg
    have c3 : Continuous fun w : (κ → AF F) × (κ → AF F) =>
        -Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (qA (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2))) :=
      ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F)).continuous_of_finiteDimensional.comp (continuous_qA.comp hh)).neg
    have c4 := (continuous_heisS f).comp (c2.prodMk (c3.prodMk c1))
    have t4 := c4.tendsto' 0 f (by
      ext y
      simp [heisS_apply, trL_apply, dotProduct, eChar_apply]
      congr 1
      funext i
      simp)
    have hsnd : Tendsto (Prod.snd : K × ((κ → AF F) × (κ → AF F)) → _) (𝓝 (k₀, 0)) (𝓝 0) := continuous_snd.tendsto _
    have hfst : Tendsto (Prod.fst : K × ((κ → AF F) × (κ → AF F)) → _) (𝓝 (k₀, 0)) (𝓝 k₀) := continuous_fst.tendsto _
    have := tendsto_apply T hTc hfst (t4.comp hsnd)
    rw [hT]
    refine this.congr' ((hsnd.eventually hfin).mono fun p hw => ?_)
    have e : finS ψ g (fun i => p2 (p.2.2 i)) (fun i => p2 (p.2.1 i)) (p2 (⅟(2 : AF F) * (p.2.1 ⬝ᵥ p.2.2))) = g :=
      funext hw
    show _ = l p.1 (schr ψ p.2 (pureA F f g))
    rw [schr_pureA_eq hψ, e, hT]
    rfl

/- English proof (translation)
Use `continuous_iff_continuousAt.2 fun p₀ => ?_` and prove the remaining obligations. Take `⟨k₀, w₀⟩` from `p₀`. Establish `h1` using `tendsto_family_zero hψ l hl hc k₀ (GlobalTheory.ConeMeasV.schr_mem_schA hψ w₀ hΦ)`. Set `c : (κ → AF F) × (κ → AF F) → ℂ` to `fun u => ψ (⅟(2 : AF F) * (u.1 ⬝ᵥ w₀.2 + w₀.1 ⬝ᵥ u.2) - u.1 ⬝ᵥ w₀.2)`. Establish `hcc : Continuous c` using `hψ.1.comp ((continuous_const.mul ((continuous_fst.dotProduct continuous_const).add (continuous_const.dotProduct continuous_snd))).sub (continuous_fst.dotProduct continuous_const))`.

Establish `e : ∀ u, schr ψ (u + w₀) Φ = c u • schr ψ u (schr ψ w₀ Φ)` using `fun u => funext fun x => by`. Simplify using `only [schr, c, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add, ← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc, add_dotProduct, dotProduct_add]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Establish `h2` using `(((hcc.comp continuous_snd).tendsto' (k₀, 0) 1 (by simp [c])).mul h1)`.

Establish `h3 : Tendsto (fun p : K × ((κ → AF F) × (κ → AF F)) => (p.1, p.2 - w₀)) (𝓝 (k₀, w₀)) (𝓝 (k₀, 0))` using `(continuous_fst.prodMk (continuous_snd.sub continuous_const)).tendsto' _ _ (by simp)`. Establish `h4` using `h2.comp h3`. Rewrite `h4` using `[one_mul]`. Use `h4.congr fun p => ?_` and prove the remaining obligations. Use `e (p.2 - w₀)` as an intermediate fact.

Rewrite `this` using `[sub_add_cancel]`. Use `show _ = l p.1 (schr ψ p.2 Φ)`. Rewrite using `[this, map_smul]`. Both sides reduce to the same expression.
-/
theorem continuous_family {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {K : Type} [TopologicalSpace K]
    [WeaklyLocallyCompactSpace K] (l : K → ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (hl : ∀ k, l k ∈ (adeleClass F).adm κ)
    (hc : ∀ Φ ∈ schA F κ, Continuous fun k => l k Φ) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    Continuous fun p : K × ((κ → AF F) × (κ → AF F)) => l p.1 (schr ψ p.2 Φ) := by
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  obtain ⟨k₀, w₀⟩ := p₀
  have h1 := tendsto_family_zero hψ l hl hc k₀ (GlobalTheory.ConeMeasV.schr_mem_schA hψ w₀ hΦ)
  let c : (κ → AF F) × (κ → AF F) → ℂ := fun u => ψ (⅟(2 : AF F) * (u.1 ⬝ᵥ w₀.2 + w₀.1 ⬝ᵥ u.2) - u.1 ⬝ᵥ w₀.2)
  have hcc : Continuous c := hψ.1.comp ((continuous_const.mul ((continuous_fst.dotProduct continuous_const).add
    (continuous_const.dotProduct continuous_snd))).sub (continuous_fst.dotProduct continuous_const))
  have e : ∀ u, schr ψ (u + w₀) Φ = c u • schr ψ u (schr ψ w₀ Φ) := fun u => funext fun x => by
    simp only [schr, c, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add, ← mul_assoc, ← AddChar.map_add_eq_mul,
      add_assoc, add_dotProduct, dotProduct_add]
    congr 2
    ring
  have h2 := (((hcc.comp continuous_snd).tendsto' (k₀, 0) 1 (by simp [c])).mul h1)
  have h3 : Tendsto (fun p : K × ((κ → AF F) × (κ → AF F)) => (p.1, p.2 - w₀)) (𝓝 (k₀, w₀)) (𝓝 (k₀, 0)) :=
    (continuous_fst.prodMk (continuous_snd.sub continuous_const)).tendsto' _ _ (by simp)
  have h4 := h2.comp h3
  rw [one_mul] at h4
  refine h4.congr fun p => ?_
  have := e (p.2 - w₀)
  rw [sub_add_cancel] at this
  show _ = l p.1 (schr ψ p.2 Φ)
  rw [this, map_smul]
  rfl

def pt (c : κ → FiniteAdeleRing (𝓞 F) F) (s : κ → mixedEmbedding.mixedSpace F) : κ → AdeleRing (𝓞 F) F :=
  fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (s i), c i) : AdeleRing (𝓞 F) F)

omit [Fintype κ] in
/- English proof (translation)
Simplify using `only [pureA, pt, RingEquiv.apply_symm_apply]`.
-/
theorem pureA_pt (c : κ → FiniteAdeleRing (𝓞 F) F) (s : κ → mixedEmbedding.mixedSpace F)
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    pureA F f g (pt c s) = f s * g c := by
  simp only [pureA, pt, RingEquiv.apply_symm_apply]

/- English proof (translation)
Proceed by induction on `hΨ using Submodule.span_induction with`. Consider the case `zero => exact ⟨0, fun s => rfl⟩`. Consider the case `add Φ Ψ _ _ h1 h2`. Take `⟨f, hf⟩` from `h1`. Take `⟨f', hf'⟩` from `h2`.

Conclude with `⟨f + f', fun s => by rw [SchwartzMap.add_apply, hf, hf', Pi.add_apply]⟩`. Consider the case `smul a Φ _ h`. Take `⟨f, hf⟩` from `h`. Conclude with `⟨a • f, fun s => by rw [SchwartzMap.smul_apply, hf, Pi.smul_apply]⟩`. Consider the case `mem Φ h`.

Take `⟨f, g, -, rfl⟩` from `h`. Conclude with `⟨g c • f, fun s => by rw [pureA_pt, SchwartzMap.smul_apply, smul_eq_mul, mul_comm]⟩`.
-/
theorem exists_slice (c : κ → FiniteAdeleRing (𝓞 F) F) {Ψ : (κ → AF F) → ℂ} (hΨ : Ψ ∈ schA F κ) :
    ∃ f : SInf F κ, ∀ s, f s = Ψ (pt c s) := by
  induction hΨ using Submodule.span_induction with
  | zero => exact ⟨0, fun s => rfl⟩
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨f, hf⟩ := h1
    obtain ⟨f', hf'⟩ := h2
    exact ⟨f + f', fun s => by rw [SchwartzMap.add_apply, hf, hf', Pi.add_apply]⟩
  | smul a Φ _ h =>
    obtain ⟨f, hf⟩ := h
    exact ⟨a • f, fun s => by rw [SchwartzMap.smul_apply, hf, Pi.smul_apply]⟩
  | mem Φ h =>
    obtain ⟨f, g, -, rfl⟩ := h
    exact ⟨g c • f, fun s => by rw [pureA_pt, SchwartzMap.smul_apply, smul_eq_mul, mul_comm]⟩

/- English proof (translation)
Set `sl : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → mixedEmbedding.mixedSpace F) → ℂ)` to `LinearMap.funLeft ℂ ℂ (pt c)`. Set `co : SInf F κ →ₗ[ℂ] ((κ → mixedEmbedding.mixedSpace F) → ℂ)` to `{ toFun := fun f => ⇑f, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }`. Establish `hco : Function.Injective co` using `DFunLike.coe_injective`. Set `e` to `LinearEquiv.ofInjective co hco`. Take `⟨T₂, hT₂⟩` from `LinearMap.exists_extend (T.toLinearMap ∘ₗ e.symm.toLinearMap)`.

Establish `hT₂f : ∀ f : SInf F κ, T₂ ⇑f = T f` using `fun f => by`. Use `congrArg (fun m => m (e f)) hT₂` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, ContinuousLinearMap.coe_coe] at this`. Rewrite `this` using `[LinearEquiv.ofInjective_apply]`. Conclude with `this`.

Establish `key : ∀ (Ψ : (κ → AF F) → ℂ) (f : SInf F κ), (∀ s, f s = Ψ (pt c s)) → (T₂ ∘ₗ sl) Ψ = T f` using `fun Ψ f hf => by`. Rewrite using `[← hT₂f, LinearMap.comp_apply]`. Conclude with `congrArg T₂ (funext fun s => (hf s).symm)`. Use `⟨T₂ ∘ₗ sl, fun g _ => ⟨g c • T, fun f => ?_⟩, key⟩` and prove the remaining obligations. Rewrite using `[key _ (g c • f) fun s => by rw [pureA_pt, SchwartzMap.smul_apply, smul_eq_mul, mul_comm], map_smul]`.

Both sides reduce to the same expression.
-/
theorem exists_admissible_slice_functional (c : κ → FiniteAdeleRing (𝓞 F) F) (T : SInf F κ →L[ℂ] ℂ) :
    ∃ l ∈ (adeleClass F).adm κ, ∀ (Ψ : (κ → AF F) → ℂ) (f : SInf F κ), (∀ s, f s = Ψ (pt c s)) → l Ψ = T f := by
  let sl : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → mixedEmbedding.mixedSpace F) → ℂ) := LinearMap.funLeft ℂ ℂ (pt c)
  let co : SInf F κ →ₗ[ℂ] ((κ → mixedEmbedding.mixedSpace F) → ℂ) :=
    { toFun := fun f => ⇑f, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hco : Function.Injective co := DFunLike.coe_injective
  let e := LinearEquiv.ofInjective co hco
  obtain ⟨T₂, hT₂⟩ := LinearMap.exists_extend (T.toLinearMap ∘ₗ e.symm.toLinearMap)
  have hT₂f : ∀ f : SInf F κ, T₂ ⇑f = T f := fun f => by
    have := congrArg (fun m => m (e f)) hT₂
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      ContinuousLinearMap.coe_coe] at this
    rw [LinearEquiv.ofInjective_apply] at this
    exact this
  have key : ∀ (Ψ : (κ → AF F) → ℂ) (f : SInf F κ), (∀ s, f s = Ψ (pt c s)) → (T₂ ∘ₗ sl) Ψ = T f := fun Ψ f hf => by
    rw [← hT₂f, LinearMap.comp_apply]
    exact congrArg T₂ (funext fun s => (hf s).symm)
  refine ⟨T₂ ∘ₗ sl, fun g _ => ⟨g c • T, fun f => ?_⟩, key⟩
  rw [key _ (g c • f) fun s => by rw [pureA_pt, SchwartzMap.smul_apply, smul_eq_mul, mul_comm], map_smul]
  rfl

/- English proof (translation)
Introduce `_ F E _ _ _ _ _ σ B a b G G₁ H H' _ e' hE K μK μ _ _ _ X om om' om₁ om₁' hT hT₁ Φ' hΦ h c`. Establish `hM` using `hT.geo.hM'`. Establish `hM₁` using `hT₁.geo.hM'`. Establish `hψ` using `hT.base.std`. Establish `hS` using `IsUWeilPair.isUSplitting hT.weil'`.

Establish `hΦA` using `polData_le_schA hM hΦ.1`. Take `⟨t1, t2, t3, t4⟩` from `GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ _ G.V'.J`. Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _`. Use `haveI : IsModuleTopology (AF F) (Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (AE F E)) := inferInstanceAs (IsModuleTopology (AF F) (Fin (b + 2) → Fin (a + (b + 2)) → AE F E))`.

Establish `hco : Continuous G.M'.co.e` using `IsModuleTopology.continuous_of_linearMap G.M'.co.e.toLinearMap`. Establish `hcA : Continuous (cA σ)` using `IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap`. Establish `hsh : Continuous (shiftB σ H H')`. Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Conclude with `(hcA.comp Units.continuous_val).mul continuous_const`.

Establish `hmem : ∀ (k : UA σ G.V'.J) l, e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k, h) Φ')) ∈ schA F _` using `fun k l => hE.maps _ (GlobalTheory.ConeMeasV.schr_mem_schA hψ _ (hS.pres _ _ hΦA))`. Use `choose S₀ hS₀ using fun k l => exists_slice c (hmem k l)`. Set `wt : (AE F E)ˣ → ℂ` to `fun l => (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1)`. Establish `hν : Continuous fun l => X.ν l` using `hT.chars.heckeα.1.div' hT.chars.heckeβ.1`. Establish `hwt : Continuous wt` using `(continuous_subtype_val.comp hν).mul ((Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE)).pow _)`.

Use `⟨fun k l => wt l • S₀ k.1 l, fun k l s => ?_, fun T => ?_⟩` and prove the remaining obligations. Rewrite using `[SchwartzMap.smul_apply, hS₀, smul_eq_mul, mul_comm, mul_assoc]`. Both sides reduce to the same expression. Take `⟨l₀, hl₀, hl₀eq⟩` from `exists_admissible_slice_functional c T`. Establish `hL` using `comp_ev_mem_adm hM hM₁ hE hl₀`.

Establish `hfam` using `continuous_family hψ (fun k : UA σ G.V'.J => (l₀ ∘ₗ e') ∘ₗ om' (k, h)) (fun k => hS.adm _ _ hL) (fun Φ hΦ => (hS.cont _ hL Φ hΦ).comp (continuous_id.prodMk continuous_const)) hΦA`. Establish `hact : Continuous fun p : K × (AE F E)ˣ => actAB (cA σ) ((p.1.1, h)⁻¹ : UA σ G.V'.J × UA σ G.W.J) (shiftB σ H H' p.2)`. Establish `hm : Continuous fun p : K × (AE F E)ˣ => mat (p.1.1⁻¹ : UA σ G.V'.J)` using `(Units.continuous_val.comp continuous_subtype_val).comp ((continuous_subtype_val.comp continuous_fst).inv)`. Conclude with `(hm.matrix_mul (hsh.comp continuous_snd)).matrix_mul (continuous_const (y := (mat (h⁻¹ : UA σ G.W.J))ᵀ))`. Establish `h1` using `hfam.comp ((continuous_subtype_val.comp continuous_fst).prodMk (hco.comp hact))`.

Use `((hwt.comp continuous_snd).mul h1).congr fun p => ?_` and prove the remaining obligations. Establish `hx` using `hS.impl (p.1.1, h)⁻¹ (shiftB σ H H' p.2) _ (hS.pres (p.1.1, h) _ hΦA)`. Establish `hx2` using `congrArg (om' (p.1.1, h)) hx`. Rewrite `hx2` using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply, ← Module.End.mul_apply (om' (p.1.1, h)⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`. Rewrite using `[map_smul, smul_eq_mul, ← hl₀eq _ _ (hS₀ p.1.1 p.2), hx2]`.

Both sides reduce to the same expression.
-/
theorem slice_weakly_continuous : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b)
    (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
      ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
      ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ h, ∀ c : Fin b × Fin (a + b) → FiniteAdeleRing (𝓞 F) F,
      ∃ S : K → (AE F E)ˣ → SchwartzMap (Fin b × Fin (a + b) → mixedEmbedding.mixedSpace F) ℂ,
        (∀ k l s, S k l s = e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ'))
            (fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (s i), c i) : AdeleRing (𝓞 F) F)) * (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1)) ∧
        ∀ (T : SchwartzMap (Fin b × Fin (a + b) → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ),
          Continuous (fun p : K × (AE F E)ˣ => T (S p.1 p.2)) := by
  intro _ F E _ _ _ _ _ σ B a b G G₁ H H' _ e' hE K μK μ _ _ _ X om om' om₁ om₁' hT hT₁ Φ' hΦ h c
  have hM := hT.geo.hM'
  have hM₁ := hT₁.geo.hM'
  have hψ := hT.base.std
  have hS := IsUWeilPair.isUSplitting hT.weil'
  have hΦA := polData_le_schA hM hΦ.1
  obtain ⟨t1, t2, t3, t4⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ _ G.V'.J
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsModuleTopology (AF F) (Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (AE F E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin (b + 2) → Fin (a + (b + 2)) → AE F E))
  have hco : Continuous G.M'.co.e := IsModuleTopology.continuous_of_linearMap G.M'.co.e.toLinearMap
  have hcA : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hsh : Continuous (shiftB σ H H') := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (hcA.comp Units.continuous_val).mul continuous_const
  have hmem : ∀ (k : UA σ G.V'.J) l, e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k, h) Φ')) ∈ schA F _ := fun k l =>
    hE.maps _ (GlobalTheory.ConeMeasV.schr_mem_schA hψ _ (hS.pres _ _ hΦA))
  choose S₀ hS₀ using fun k l => exists_slice c (hmem k l)
  let wt : (AE F E)ˣ → ℂ := fun l => (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1)
  have hν : Continuous fun l => X.ν l := hT.chars.heckeα.1.div' hT.chars.heckeβ.1
  have hwt : Continuous wt :=
    (continuous_subtype_val.comp hν).mul
      ((Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE)).pow _)
  refine ⟨fun k l => wt l • S₀ k.1 l, fun k l s => ?_, fun T => ?_⟩
  · rw [SchwartzMap.smul_apply, hS₀, smul_eq_mul, mul_comm, mul_assoc]
    rfl
  · obtain ⟨l₀, hl₀, hl₀eq⟩ := exists_admissible_slice_functional c T
    have hL := comp_ev_mem_adm hM hM₁ hE hl₀
    have hfam := continuous_family hψ (fun k : UA σ G.V'.J => (l₀ ∘ₗ e') ∘ₗ om' (k, h)) (fun k => hS.adm _ _ hL)
      (fun Φ hΦ => (hS.cont _ hL Φ hΦ).comp (continuous_id.prodMk continuous_const)) hΦA
    have hact : Continuous fun p : K × (AE F E)ˣ => actAB (cA σ) ((p.1.1, h)⁻¹ : UA σ G.V'.J × UA σ G.W.J) (shiftB σ H H' p.2) := by
      have hm : Continuous fun p : K × (AE F E)ˣ => mat (p.1.1⁻¹ : UA σ G.V'.J) :=
        (Units.continuous_val.comp continuous_subtype_val).comp ((continuous_subtype_val.comp continuous_fst).inv)
      exact (hm.matrix_mul (hsh.comp continuous_snd)).matrix_mul (continuous_const (y := (mat (h⁻¹ : UA σ G.W.J))ᵀ))
    have h1 := hfam.comp ((continuous_subtype_val.comp continuous_fst).prodMk (hco.comp hact))
    refine ((hwt.comp continuous_snd).mul h1).congr fun p => ?_
    have hx := hS.impl (p.1.1, h)⁻¹ (shiftB σ H H' p.2) _ (hS.pres (p.1.1, h) _ hΦA)
    have hx2 := congrArg (om' (p.1.1, h)) hx
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply,
      ← Module.End.mul_apply (om' (p.1.1, h)⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at hx2
    rw [map_smul, smul_eq_mul, ← hl₀eq _ _ (hS₀ p.1.1 p.2), hx2]
    rfl

end GlobalTheory.ConeSliceWeak
