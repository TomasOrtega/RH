import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

/- English proof (translation)
The claim follows from `inferInstance`.
-/
private theorem sfinite_of_finite {X : Type} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] :
    SFinite ν := inferInstance

/- English proof (translation)
Introduce `hcc E _ _ _ n μ _ f hf ⟨C, hC⟩ hl a ha ⟨D, hD⟩ h0 β h`. Use `Reduction.isFiniteMeasure_quotientMeasure (K := E) (n := n) μ` as an intermediate fact. Generalize the expression as in `RightCosetSpace.quotientMeasure (Reduction.rationalGLOne E n) μ = ν at *`. Establish `: SFinite ν` using `sfinite_of_finite ν`. Establish `: (volume : Measure (Rinf E)).IsAddHaarMeasure` using `isAddHaarMeasure_volume_pi _`.

Establish `: (volume : Measure (Fin n → Rinf E)).IsAddHaarMeasure` using `Measure.pi.isAddHaarMeasure _`. Establish `: (volume : Measure (Lie E n)).IsAddHaarMeasure` using `Measure.pi.isAddHaarMeasure _`. Establish `hr : ∀ g : GA E n, IsLeftInvariant fun x => f (x * g)` using `fun g γ x => by show f (AdelicGLn.diagonal E n γ * x * g) = f (x * g)`. Rewrite using `[mul_assoc]`. Conclude with `hl γ _`.

Establish `hF : ∀ x : Lie E n, IsLeftInvariant fun g : GA E n => chart f g x` using `fun x γ g => by show chart f (AdelicGLn.diagonal E n γ * g) x = chart f g x`. Unfold `chart`. Use `split_ifs with hx`. Conclude with `hr _ γ g`. Both sides reduce to the same expression.

Set `F : RightCosetSpace (Reduction.rationalGLOne E n) × Lie E n → ℂ` to `fun z => CuspidalSpectrum.cuspQuot (hF z.2) z.1`. Establish `hFmk : ∀ (y : Reduction.normOneGL E n) x, F (RightCosetSpace.mk (Reduction.rationalGLOne E n) y, x) = chart f y.1 x` using `fun _ _ => rfl`. Establish `hC0 : 0 ≤ C` using `(norm_nonneg _).trans (hC 1)`. Establish `hFb : ∀ z, ‖F z‖ ≤ C`. Introduce and unpack `⟨q, x⟩`.

Take `⟨y, rfl⟩` from `RightCosetSpace.mk_surjective _ q`. Rewrite using `[hFmk]`. Unfold `chart`. Use `split_ifs`. Conclude with `hC _`.

Simplify using `using hC0`. Establish `hF0 : ∀ q x, x ∉ invSet E n → F (q, x) = 0`. Introduce `q x hx`. Take `⟨y, rfl⟩` from `RightCosetSpace.mk_surjective _ q`. Rewrite using `[hFmk]`.

Conclude with `dif_neg hx`. Establish `hopen : IsOpen ((Set.univ : Set (RightCosetSpace (Reduction.rationalGLOne E n))) ×ˢ invSet E n)` using `isOpen_univ.prod TR.isOpen_invSet`. Establish `hFc : ContinuousOn F (Set.univ ×ˢ invSet E n)`. Introduce and unpack `⟨q, x⟩ ⟨-, hx⟩`. Take `⟨y, rfl⟩` from `RightCosetSpace.mk_surjective _ q`.

Establish `hq` using `(RightCosetSpace.isOpenQuotientMap_mk (Reduction.rationalGLOne E n)).prodMap (IsOpenQuotientMap.id (X := Lie E n))`. Use `ContinuousAt.continuousWithinAt ?_` and prove the remaining obligations. Use `(hq.continuousAt_comp_iff (g := F) (x := (y, x))).1 ?_` and prove the remaining obligations. Establish `h1 : ContinuousAt (fun z : GA E n × Lie E n => chart f z.1 z.2) (y.1, x)` using `(hcc E n f hf).1.continuousAt ((isOpen_univ.prod TR.isOpen_invSet).mem_nhds ⟨trivial, hx⟩)`. Establish `h2 : Continuous fun z : Reduction.normOneGL E n × Lie E n => ((z.1.1, z.2) : GA E n × Lie E n)` using `(continuous_subtype_val.comp continuous_fst).prodMk continuous_snd`.

Conclude with `ContinuousAt.comp (f := fun z : Reduction.normOneGL E n × Lie E n => ((z.1.1, z.2) : GA E n × Lie E n)) (x := (y, x)) h1 h2.continuousAt`. Establish `hFm : Measurable F`. Establish `hc : ContinuousOn F (Set.univ ×ˢ invSet E n)ᶜ` using `(continuousOn_const (c := (0 : ℂ))).congr fun z hz => hF0 z.1 z.2 fun hx => hz ⟨trivial, hx⟩`. Use `hFc.measurable_piecewise hc hopen.measurableSet` as an intermediate fact. Rewrite `this` using `[Set.piecewise_same]`. Then use the resulting hypothesis.

Establish `hint : Integrable (fun z : RightCosetSpace (Reduction.rationalGLOne E n) × Lie E n => (a z.1 * F z) * β z.2) (ν.prod volume)`. Establish `hβ : Integrable (fun z : RightCosetSpace (Reduction.rationalGLOne E n) × Lie E n => β z.2) (ν.prod volume)` using `(β.integrable (μ := volume)).comp_snd _`. Use `hβ.bdd_mul (c := D * C) (((ha.measurable.comp measurable_fst).mul hFm).aestronglyMeasurable) (Filter.Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul (hD _) (hFb _) (norm_nonneg _) ((norm_nonneg _).trans (hD z.1))`.

Establish `e1 : ∀ q, a q * CuspidalSpectrum.cuspQuot h q = ∫ x, (a q * F (q, x)) * β x`. Introduce `q`. Take `⟨y, rfl⟩` from `RightCosetSpace.mk_surjective _ q`. Rewrite using `[CuspidalSpectrum.cuspQuot_mk, conv, ← integral_const_mul]`. Simplify using `only [hFmk, mul_assoc]`.

Establish `e2 : ∀ x, ∫ q, (a q * F (q, x)) * β x ∂ν = 0`. Introduce `x`. Rewrite using `[integral_mul_const]`. Distinguish the cases in `hx : x ∈ invSet E n`. Establish `hx' : IsUnit (Matrix.of x)` using `hx`.

Establish `e : ∀ q, F (q, x) = CuspidalSpectrum.cuspQuot (hr (infGL E n hx'.unit)) q`. Introduce `q`. Take `⟨y, rfl⟩` from `RightCosetSpace.mk_surjective _ q`. Rewrite using `[hFmk, CuspidalSpectrum.cuspQuot_mk]`. Conclude with `dif_pos hx'`.

Simplify using `only [e]`. Rewrite using `[h0, zero_mul]`. Simplify using `[hF0 _ x hx]`. Simplify using `only [e1]`. Rewrite using `[integral_integral_swap (f := fun q x => (a q * F (q, x)) * β x) hint]`.

Simplify using `only [e2, integral_zero]`.
-/
theorem UpperTheory.V.Af.Smo.orthStep :
    UpperTheory.V.Af.Smo.ChartCont → UpperTheory.V.Af.Smo.OrthStep := by
  classical
  intro hcc E _ _ _ n μ _ f hf ⟨C, hC⟩ hl a ha ⟨D, hD⟩ h0 β h
  have := Reduction.isFiniteMeasure_quotientMeasure (K := E) (n := n) μ
  generalize RightCosetSpace.quotientMeasure (Reduction.rationalGLOne E n) μ = ν at *
  have : SFinite ν := sfinite_of_finite ν
  have : (volume : Measure (Rinf E)).IsAddHaarMeasure := isAddHaarMeasure_volume_pi _
  have : (volume : Measure (Fin n → Rinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (Lie E n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hr : ∀ g : GA E n, IsLeftInvariant fun x => f (x * g) := fun g γ x => by
    show f (AdelicGLn.diagonal E n γ * x * g) = f (x * g)
    rw [mul_assoc]
    exact hl γ _
  have hF : ∀ x : Lie E n, IsLeftInvariant fun g : GA E n => chart f g x := fun x γ g => by
    show chart f (AdelicGLn.diagonal E n γ * g) x = chart f g x
    unfold chart
    split_ifs with hx
    · exact hr _ γ g
    · rfl
  let F : RightCosetSpace (Reduction.rationalGLOne E n) × Lie E n → ℂ := fun z =>
    CuspidalSpectrum.cuspQuot (hF z.2) z.1
  have hFmk : ∀ (y : Reduction.normOneGL E n) x,
      F (RightCosetSpace.mk (Reduction.rationalGLOne E n) y, x) = chart f y.1 x := fun _ _ => rfl
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)
  have hFb : ∀ z, ‖F z‖ ≤ C := by
    rintro ⟨q, x⟩
    obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
    rw [hFmk]
    unfold chart
    split_ifs
    · exact hC _
    · simpa using hC0
  have hF0 : ∀ q x, x ∉ invSet E n → F (q, x) = 0 := by
    intro q x hx
    obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
    rw [hFmk]
    exact dif_neg hx
  have hopen : IsOpen ((Set.univ : Set (RightCosetSpace (Reduction.rationalGLOne E n))) ×ˢ invSet E n) :=
    isOpen_univ.prod TR.isOpen_invSet
  have hFc : ContinuousOn F (Set.univ ×ˢ invSet E n) := by
    rintro ⟨q, x⟩ ⟨-, hx⟩
    obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
    have hq := (RightCosetSpace.isOpenQuotientMap_mk (Reduction.rationalGLOne E n)).prodMap
      (IsOpenQuotientMap.id (X := Lie E n))
    refine ContinuousAt.continuousWithinAt ?_
    refine (hq.continuousAt_comp_iff (g := F) (x := (y, x))).1 ?_
    have h1 : ContinuousAt (fun z : GA E n × Lie E n => chart f z.1 z.2) (y.1, x) :=
      (hcc E n f hf).1.continuousAt ((isOpen_univ.prod TR.isOpen_invSet).mem_nhds ⟨trivial, hx⟩)
    have h2 : Continuous fun z : Reduction.normOneGL E n × Lie E n => ((z.1.1, z.2) : GA E n × Lie E n) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    exact ContinuousAt.comp (f := fun z : Reduction.normOneGL E n × Lie E n => ((z.1.1, z.2) : GA E n × Lie E n))
      (x := (y, x)) h1 h2.continuousAt
  have hFm : Measurable F := by
    have hc : ContinuousOn F (Set.univ ×ˢ invSet E n)ᶜ :=
      (continuousOn_const (c := (0 : ℂ))).congr fun z hz => hF0 z.1 z.2 fun hx => hz ⟨trivial, hx⟩
    have := hFc.measurable_piecewise hc hopen.measurableSet
    rwa [Set.piecewise_same] at this
  have hint : Integrable (fun z : RightCosetSpace (Reduction.rationalGLOne E n) × Lie E n =>
      (a z.1 * F z) * β z.2)
      (ν.prod volume) := by
    have hβ : Integrable (fun z : RightCosetSpace (Reduction.rationalGLOne E n) × Lie E n => β z.2)
        (ν.prod volume) :=
      (β.integrable (μ := volume)).comp_snd _
    refine hβ.bdd_mul (c := D * C) (((ha.measurable.comp measurable_fst).mul hFm).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => ?_)
    rw [norm_mul]
    exact mul_le_mul (hD _) (hFb _) (norm_nonneg _) ((norm_nonneg _).trans (hD z.1))
  have e1 : ∀ q, a q * CuspidalSpectrum.cuspQuot h q = ∫ x, (a q * F (q, x)) * β x := by
    intro q
    obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
    rw [CuspidalSpectrum.cuspQuot_mk, conv, ← integral_const_mul]
    simp only [hFmk, mul_assoc]
  have e2 : ∀ x, ∫ q, (a q * F (q, x)) * β x ∂ν = 0 := by
    intro x
    rw [integral_mul_const]
    by_cases hx : x ∈ invSet E n
    · have hx' : IsUnit (Matrix.of x) := hx
      have e : ∀ q, F (q, x) = CuspidalSpectrum.cuspQuot (hr (infGL E n hx'.unit)) q := by
        intro q
        obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
        rw [hFmk, CuspidalSpectrum.cuspQuot_mk]
        exact dif_pos hx'
      simp only [e]
      rw [h0, zero_mul]
    · simp [hF0 _ x hx]
  simp only [e1]
  rw [integral_integral_swap (f := fun q x => (a q * F (q, x)) * β x) hint]
  simp only [e2, integral_zero]
