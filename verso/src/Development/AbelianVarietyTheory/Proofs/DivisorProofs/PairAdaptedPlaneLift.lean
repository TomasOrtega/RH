import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgFormApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairRestrictionGlobalFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPairDescentModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceNondegeneratePartialFourierIntegralStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.SiegelAvgCore

/- English proof (translation)
Introduce `g hg`. Use `haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F`. Take `⟨U, hU⟩` from `hl _ (GlobalTheory.ThK.Adapt.slice_mem_SB ε 0 hg)`. Take `⟨T, hT⟩` from `GlobalTheory.ThK.Adapt.exists_slice ε (0 : κa → mixedEmbedding.mixedSpace F)`. Use `⟨U.comp T, fun f => ?_⟩` and prove the remaining obligations.

Rewrite using `[ContinuousLinearMap.comp_apply, ← hU]`. Simplify using `only [LinearMap.comp_apply]`. Use `congr 1`. Use function extensionality and compare the values at `b`. Simplify using `only [LinearMap.funLeft_apply, pureA, hT]`.

Rewrite using `[GlobalTheory.ThK.Adapt.glue_map ε (fun z : AF F => InfiniteAdeleRing.ringEquiv_mixedSpace F z.1), GlobalTheory.ThK.Adapt.glue_map ε (fun z : AF F => z.2)]`. Simplify using `only [Pi.zero_apply]`. Establish `h1 : (fun _ : κa => InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : AF F).1) = 0`. Use function extensionality and compare the values at `k`. Conclude with `map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)`.

Rewrite using `[h1]`. Both sides reduce to the same expression.
-/
theorem sliceAdm {F : Type} [Field F] [NumberField F] {κ κa κb : Type} [Fintype κ] [Fintype κa] [Fintype κb]
    (ε : κ ≃ κa ⊕ κb) (l : ((κb → AF F) → ℂ) →ₗ[ℂ] ℂ) (hl : l ∈ (adeleClass F).adm κb) :
    l ∘ₗ LinearMap.funLeft ℂ ℂ (fun v => GlobalTheory.ThK.Adapt.glue ε 0 v) ∈ (adeleClass F).adm κ := by
  intro g hg
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  obtain ⟨U, hU⟩ := hl _ (GlobalTheory.ThK.Adapt.slice_mem_SB ε 0 hg)
  obtain ⟨T, hT⟩ := GlobalTheory.ThK.Adapt.exists_slice ε (0 : κa → mixedEmbedding.mixedSpace F)
  refine ⟨U.comp T, fun f => ?_⟩
  rw [ContinuousLinearMap.comp_apply, ← hU]
  simp only [LinearMap.comp_apply]
  congr 1
  funext b
  simp only [LinearMap.funLeft_apply, pureA, hT]
  rw [GlobalTheory.ThK.Adapt.glue_map ε (fun z : AF F => InfiniteAdeleRing.ringEquiv_mixedSpace F z.1),
    GlobalTheory.ThK.Adapt.glue_map ε (fun z : AF F => z.2)]
  simp only [Pi.zero_apply]
  have h1 : (fun _ : κa => InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : AF F).1) = 0 := by
    funext k; exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  rw [h1]
  rfl

/- English proof (translation)
Introduce `hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hpair₁ d' hd' d₁' hd₁' dd hdd dd₁ hdd₁ ed hmaps hheis hinv hadm hne μ₁ hμ₁ μ hμ g hg`. Take `⟨κa, _, ε, C, S, hC, hS, hSa, hTheis, hTinv, hTne, htr⟩` from `GlobalTheory.T.adapted_pair_descent_model hP F E σ B n d X W M χX χW om r s r' s' hpair d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hpair₁ d' hd' d₁' hd₁' dd hdd dd₁ hdd₁`. Set `T` to `LinearMap.funLeft ℂ ℂ (fun v => GlobalTheory.ThK.Adapt.glue ε 0 v) ∘ₗ S`. Establish `hTap : ∀ Φ, T Φ = fun v => S Φ (GlobalTheory.ThK.Adapt.glue ε 0 v)` using `fun Φ => rfl`. Establish `hT1 : ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), T Φ ∈ schA F ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁))` using `fun Φ hΦ => by rw [hTap]; exact GlobalTheory.ThK.Adapt.slice_mem_schA ε 0 (hS Φ hΦ)`.

Establish `hT2 : ∀ (z : Matrix (Fin d₁) (Fin n ⊕ Fin n) (AE F E)), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), T (dd.rho B.ψ (incM F H'.ι * z) Φ) = dd₁.rho B.ψ z (T Φ)` using `fun z Φ hΦ => by`. Rewrite using `[hTap, hTap]`. Conclude with `hTheis z Φ hΦ`. Establish `hT3 : ∀ (y : Fin n ⊕ Fin n → AE F E), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), T (dd.rho B.ψ (Matrix.vecMulVec (incV F H'.x) y) Φ) = T Φ` using `fun y Φ hΦ => by`. Rewrite using `[hTap, hTap]`.

Conclude with `funext (hTinv y Φ hΦ)`. Establish `hT4 : ∀ l ∈ (adeleClass F).adm ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁)), l ∘ₗ T ∈ (adeleClass F).adm ((Fin n × Fin d) ⊕ (Fin n × Fin d))`. Introduce `l hl g' hg'`. Take `⟨l', hl', e⟩` from `hSa _ (sliceAdm ε l hl)`. Take `⟨U, hU⟩` from `hl' g' hg'`.

Conclude with `⟨U, fun f => by rw [← hU f, e _ (Submodule.subset_span ⟨f, g', hg', rfl⟩)]; rfl⟩`. Establish `hT5 : ∃ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), T Φ ≠ 0`. Take `⟨Φ, hΦ, h⟩` from `hTne`. Conclude with `⟨Φ, hΦ, h⟩`. Take `⟨c, hc⟩` from `GlobalTheory.T.seesaw_pair_restriction_global_factor hP F E σ B n d X W M χX χW om r s r' s' hpair d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hpair₁ d' hd' d₁' hd₁' dd hdd dd₁ hdd₁ T hT1 hT2 hT3 hT4 hT5 ed hmaps hheis hinv hadm`.

Take `⟨hint, Λ, hΛ, hΛeq⟩` from `GlobalTheory.T.trace_nondegenerate_partial_fourier_integral F E n ((Fin n × Fin d) ⊕ (Fin n × Fin d)) κa (Fin n × Fin d₁) ε C hC μ₁ hμ₁ μ hμ`. Take `⟨l', hl', hl'eq⟩` from `hSa Λ hΛ`. Take `⟨U, hU⟩` from `hl' g hg`. Establish `hψ : IsStd B.ψ` using `hpair.base.std`. Establish `hΦ : ∀ f : SchwartzMap ((Fin n × Fin d) ⊕ (Fin n × Fin d) → NumberField.mixedEmbedding.mixedSpace F) ℂ, pureA F f g ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d))` using `fun f => Submodule.subset_span ⟨f, g, hg, rfl⟩`.

Establish `key : ∀ f : SchwartzMap ((Fin n × Fin d) ⊕ (Fin n × Fin d) → NumberField.mixedEmbedding.mixedSpace F) ℂ, ∀ y : Fin n → AE F E, GlobalTheory.DiagSiegel.diagInt μ₁ (ed (GlobalTheory.SiegelAvg.starFam dd B.ψ (incV F H'.y) y (pureA F f g))) = c * GlobalTheory.DiagSiegel.diagInt μ₁ (f …` using `F) (AF F) (C k j) * y j)) v)) := by`. Introduce `f y`. Establish `hm : GlobalTheory.SiegelAvg.starFam dd B.ψ (incV F H'.y) y (pureA F f g) ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d))` using `GlobalTheory.HeisSchA.schr_mem_schA B.ψ hψ (dd.e (Matrix.vecMulVec (incV F H'.y) (Sum.elim y y))) _ (hΦ f)`. Rewrite using `[hc _ hm]`. Establish `e1 : c • T (GlobalTheory.SiegelAvg.starFam dd B.ψ (incV F H'.y) y (pureA F f g)) = fun v => c * S (pureA F f g) (GlobalTheory.ThK.Adapt.glue ε (fun k => ∑ j, Algebra.trace (AF F) (AE F E) (inclR (F` using `F) (AF F) (C k j) * y j)) v) := by`.

Use function extensionality and compare the values at `v`. Rewrite using `[Pi.smul_apply, smul_eq_mul, hTap]`. Conclude with `congrArg (c * ·) (htr y _ (hΦ f) v)`. Rewrite using `[e1]`. Unfold `GlobalTheory.DiagSiegel.diagInt`.

Use `letI : MeasurableSpace ((Fin n × Fin d₁) → AF F) := borel _`. Conclude with `integral_const_mul c _`. Use `⟨c • U, fun f => ?_⟩` and prove the remaining obligations. Use `letI : MeasurableSpace (Fin n → AE F E) := borel _`. Establish `hk : (fun y => GlobalTheory.DiagSiegel.diagInt μ₁ (ed (GlobalTheory.SiegelAvg.starFam dd B.ψ (incV F H'.y) y (pureA F f g)))) = fun y => c * GlobalTheory.DiagSiegel.diagInt μ₁ (fun v => S (pureA F f g) (GlobalTheory.ThK.Adapt.glue ε (fun k => ∑ j, Algebra.trace (AF F) (AE F E) (i …` using `F) (AF F) (C k j) * y j)) v)) :=`.

Use function extensionality and compare the values at `(key f)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hk]`. Conclude with `(hint _ (hS _ (hΦ f))).const_mul c`. Rewrite using `[hk, integral_const_mul, ← hΛeq _ (hS _ (hΦ f)), ← hl'eq _ (hΦ f), hU, ContinuousLinearMap.smul_apply, smul_eq_mul]`.
-/
theorem main : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      ∀ (d' : Darboux (symp (cA σ) (-1) (incM F W.J) (incM F X.J)) (Fin n × Fin d)),
        (∀ x : Matrix (Fin n) (Fin d) (AE F E), d'.e xᵀ = M.co.e x) →
      ∀ (d₁' : Darboux (symp (cA σ) (-1) (incM F W₁.J) (incM F X.J)) (Fin n × Fin d₁)),
        (∀ x : Matrix (Fin n) (Fin d₁) (AE F E), d₁'.e xᵀ = M₁.co.e x) →
      ∀ (dd : Darboux (symp (cA σ) (-1) (incM F W.J) (dbl (incM F X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d))),
        IsDblCoord (cA σ) (-1) (incM F W.J) (incM F X.J) d' dd →
      ∀ (dd₁ : Darboux (symp (cA σ) (-1) (incM F W₁.J) (dbl (incM F X.J))) ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁))),
        IsDblCoord (cA σ) (-1) (incM F W₁.J) (incM F X.J) d₁' dd₁ →
      ∀ ed : (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ) →ₗ[ℂ] (((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁) → AF F) → ℂ),
        (∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), ed Φ ∈ schA F ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁))) →
        (∀ (z : Matrix (Fin d₁) (Fin n ⊕ Fin n) (AE F E)), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
          ed (dd.rho B.ψ (incM F H'.ι * z) Φ) = dd₁.rho B.ψ z (ed Φ)) →
        (∀ (y : Fin n ⊕ Fin n → AE F E), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
          ed (dd.rho B.ψ (Matrix.vecMulVec (incV F H'.x) y) Φ) = ed Φ) →
        (∀ l ∈ (adeleClass F).adm ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁)), l ∘ₗ ed ∈ (adeleClass F).adm ((Fin n × Fin d) ⊕ (Fin n × Fin d))) →
        (∃ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), ed Φ ≠ 0) →
      ∀ μ₁ : @Measure ((Fin n × Fin d₁) → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ₁ →
      ∀ μ : @Measure (Fin n → AE F E) (borel _), GlobalTheory.SiegelAvg.IsHaarB μ →
      ∀ g ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → FiniteAdeleRing (𝓞 F) F),
        ∃ T : SchwartzMap ((Fin n × Fin d) ⊕ (Fin n × Fin d) → NumberField.mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ,
          ∀ f : SchwartzMap ((Fin n × Fin d) ⊕ (Fin n × Fin d) → NumberField.mixedEmbedding.mixedSpace F) ℂ,
            (letI : MeasurableSpace (Fin n → AE F E) := borel _; Integrable (fun y => GlobalTheory.DiagSiegel.diagInt μ₁ (ed (GlobalTheory.SiegelAvg.starFam dd B.ψ (incV F H'.y) y (pureA F f g)))) μ) ∧
            (letI : MeasurableSpace (Fin n → AE F E) := borel _; ∫ y, GlobalTheory.DiagSiegel.diagInt μ₁ (ed (GlobalTheory.SiegelAvg.starFam dd B.ψ (incV F H'.y) y (pureA F f g))) ∂μ) = T f := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hpair₁ d' hd' d₁' hd₁'
    dd hdd dd₁ hdd₁ ed hmaps hheis hinv hadm hne μ₁ hμ₁ μ hμ g hg
  obtain ⟨κa, _, ε, C, S, hC, hS, hSa, hTheis, hTinv, hTne, htr⟩ := GlobalTheory.T.adapted_pair_descent_model hP F E σ B n d X W M χX χW om r s r' s' hpair
    d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hpair₁ d' hd' d₁' hd₁' dd hdd dd₁ hdd₁
  let T := LinearMap.funLeft ℂ ℂ (fun v => GlobalTheory.ThK.Adapt.glue ε 0 v) ∘ₗ S
  have hTap : ∀ Φ, T Φ = fun v => S Φ (GlobalTheory.ThK.Adapt.glue ε 0 v) := fun Φ => rfl
  have hT1 : ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), T Φ ∈ schA F ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁)) :=
    fun Φ hΦ => by rw [hTap]; exact GlobalTheory.ThK.Adapt.slice_mem_schA ε 0 (hS Φ hΦ)
  have hT2 : ∀ (z : Matrix (Fin d₁) (Fin n ⊕ Fin n) (AE F E)), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
      T (dd.rho B.ψ (incM F H'.ι * z) Φ) = dd₁.rho B.ψ z (T Φ) := fun z Φ hΦ => by
    rw [hTap, hTap]; exact hTheis z Φ hΦ
  have hT3 : ∀ (y : Fin n ⊕ Fin n → AE F E), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
      T (dd.rho B.ψ (Matrix.vecMulVec (incV F H'.x) y) Φ) = T Φ := fun y Φ hΦ => by
    rw [hTap, hTap]; exact funext (hTinv y Φ hΦ)
  have hT4 : ∀ l ∈ (adeleClass F).adm ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁)),
      l ∘ₗ T ∈ (adeleClass F).adm ((Fin n × Fin d) ⊕ (Fin n × Fin d)) := by
    intro l hl g' hg'
    obtain ⟨l', hl', e⟩ := hSa _ (sliceAdm ε l hl)
    obtain ⟨U, hU⟩ := hl' g' hg'
    exact ⟨U, fun f => by rw [← hU f, e _ (Submodule.subset_span ⟨f, g', hg', rfl⟩)]; rfl⟩
  have hT5 : ∃ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), T Φ ≠ 0 := by
    obtain ⟨Φ, hΦ, h⟩ := hTne
    exact ⟨Φ, hΦ, h⟩
  obtain ⟨c, hc⟩ := GlobalTheory.T.seesaw_pair_restriction_global_factor hP F E σ B n d X W M χX χW om r s r' s' hpair d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hpair₁
    d' hd' d₁' hd₁' dd hdd dd₁ hdd₁ T hT1 hT2 hT3 hT4 hT5 ed hmaps hheis hinv hadm
  obtain ⟨hint, Λ, hΛ, hΛeq⟩ := GlobalTheory.T.trace_nondegenerate_partial_fourier_integral F E n ((Fin n × Fin d) ⊕ (Fin n × Fin d)) κa (Fin n × Fin d₁) ε C hC μ₁ hμ₁ μ hμ
  obtain ⟨l', hl', hl'eq⟩ := hSa Λ hΛ
  obtain ⟨U, hU⟩ := hl' g hg
  have hψ : IsStd B.ψ := hpair.base.std
  have hΦ : ∀ f : SchwartzMap ((Fin n × Fin d) ⊕ (Fin n × Fin d) → NumberField.mixedEmbedding.mixedSpace F) ℂ,
      pureA F f g ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)) := fun f => Submodule.subset_span ⟨f, g, hg, rfl⟩
  have key : ∀ f : SchwartzMap ((Fin n × Fin d) ⊕ (Fin n × Fin d) → NumberField.mixedEmbedding.mixedSpace F) ℂ,
      ∀ y : Fin n → AE F E,
      GlobalTheory.DiagSiegel.diagInt μ₁ (ed (GlobalTheory.SiegelAvg.starFam dd B.ψ (incV F H'.y) y (pureA F f g))) =
        c * GlobalTheory.DiagSiegel.diagInt μ₁ (fun v => S (pureA F f g) (GlobalTheory.ThK.Adapt.glue ε (fun k => ∑ j, Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) (C k j) * y j)) v)) := by
    intro f y
    have hm : GlobalTheory.SiegelAvg.starFam dd B.ψ (incV F H'.y) y (pureA F f g) ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)) :=
      GlobalTheory.HeisSchA.schr_mem_schA B.ψ hψ (dd.e (Matrix.vecMulVec (incV F H'.y) (Sum.elim y y))) _ (hΦ f)
    rw [hc _ hm]
    have e1 : c • T (GlobalTheory.SiegelAvg.starFam dd B.ψ (incV F H'.y) y (pureA F f g)) =
        fun v => c * S (pureA F f g) (GlobalTheory.ThK.Adapt.glue ε (fun k => ∑ j, Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) (C k j) * y j)) v) := by
      funext v
      rw [Pi.smul_apply, smul_eq_mul, hTap]
      exact congrArg (c * ·) (htr y _ (hΦ f) v)
    rw [e1]
    unfold GlobalTheory.DiagSiegel.diagInt
    letI : MeasurableSpace ((Fin n × Fin d₁) → AF F) := borel _
    exact integral_const_mul c _
  refine ⟨c • U, fun f => ?_⟩
  letI : MeasurableSpace (Fin n → AE F E) := borel _
  have hk : (fun y => GlobalTheory.DiagSiegel.diagInt μ₁ (ed (GlobalTheory.SiegelAvg.starFam dd B.ψ (incV F H'.y) y (pureA F f g)))) =
      fun y => c * GlobalTheory.DiagSiegel.diagInt μ₁ (fun v => S (pureA F f g) (GlobalTheory.ThK.Adapt.glue ε (fun k => ∑ j, Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) (C k j) * y j)) v)) :=
    funext (key f)
  refine ⟨?_, ?_⟩
  · rw [hk]
    exact (hint _ (hS _ (hΦ f))).const_mul c
  · rw [hk, integral_const_mul, ← hΛeq _ (hS _ (hΦ f)), ← hl'eq _ (hΦ f), hU, ContinuousLinearMap.smul_apply, smul_eq_mul]

end GlobalTheory.SiegelAvgCore

end
