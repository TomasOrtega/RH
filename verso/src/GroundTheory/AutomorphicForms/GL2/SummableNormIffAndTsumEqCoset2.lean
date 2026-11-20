import Mathlib
import GroundTheory.GlobalFields.TateThesis.TraceLatticePoisson

namespace GroundTheory.Automorphic.Adele2

open GroundTheory.Global NumberField NumberField.mixedEmbedding MeasureTheory Module Filter
open scoped FourierTransform SchwartzMap RealInnerProductSpace nonZeroDivisors Classical

set_option synthInstance.maxSize 1000

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

def mixedPairing2 (x y : Fin 2 → mixedSpace K) : ℝ := ∑ i, mixedTraceForm K (x i) (y i)

/- English proof (translation)
The claim follows from `Finset.sum_congr rfl fun i _ => mixedTraceForm_comm K (x i) (y i)`.
-/
theorem mixedPairing2_comm (x y : Fin 2 → mixedSpace K) :
    mixedPairing2 K x y = mixedPairing2 K y x :=
  Finset.sum_congr rfl fun i _ => mixedTraceForm_comm K (x i) (y i)

/- English proof (translation)
Simplify using `only [mixedPairing2, Pi.neg_apply, map_neg, Finset.sum_neg_distrib]`.
-/
theorem mixedPairing2_neg_right (x y : Fin 2 → mixedSpace K) :
    mixedPairing2 K x (-y) = -mixedPairing2 K x y := by
  simp only [mixedPairing2, Pi.neg_apply, map_neg, Finset.sum_neg_distrib]

def mixedMeasure2 : Measure (Fin 2 → mixedSpace K) := Measure.pi fun _ => selfDualMeasure K

instance : (mixedMeasure2 K).IsAddHaarMeasure := by
  unfold mixedMeasure2
  infer_instance

def toEuclid2 : (Fin 2 → mixedSpace K) ≃L[ℝ]
    WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K) :=
  ((ContinuousLinearEquiv.finTwoArrow ℝ (mixedSpace K)).trans
    ((mixedToEuclidean K).prodCongr (mixedToEuclidean K))).trans
    (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm

def toEuclid2Conj : (Fin 2 → mixedSpace K) ≃L[ℝ]
    WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K) :=
  ((ContinuousLinearEquiv.finTwoArrow ℝ (mixedSpace K)).trans
    ((mixedToEuclideanConj K).prodCongr (mixedToEuclideanConj K))).trans
    (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toEuclid2_apply (x : Fin 2 → mixedSpace K) :
    toEuclid2 K x = WithLp.toLp 2 (mixedToEuclidean K (x 0), mixedToEuclidean K (x 1)) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toEuclid2Conj_apply (x : Fin 2 → mixedSpace K) :
    toEuclid2Conj K x =
      WithLp.toLp 2 (mixedToEuclideanConj K (x 0), mixedToEuclideanConj K (x 1)) := rfl

/- English proof (translation)
Rewrite using `[mixedPairing2, Fin.sum_univ_two, toEuclid2_apply, toEuclid2Conj_apply, WithLp.prod_inner_apply, mixedTraceForm_eq_inner, mixedTraceForm_eq_inner]`.
-/
theorem mixedPairing2_eq_inner (x y : Fin 2 → mixedSpace K) :
    mixedPairing2 K x y = ⟪toEuclid2 K x, toEuclid2Conj K y⟫ := by
  rw [mixedPairing2, Fin.sum_univ_two, toEuclid2_apply, toEuclid2Conj_apply,
    WithLp.prod_inner_apply, mixedTraceForm_eq_inner, mixedTraceForm_eq_inner]

/- English proof (translation)
Establish `h1` using `measurePreserving_finTwoArrow (selfDualMeasure K)`. Establish `h2` using `(measurePreserving_mixedToEuclidean K).prod (measurePreserving_mixedToEuclidean K)`. Establish `h3` using `WithLp.volume_preserving_toLp (euclidean.mixedSpace K) (euclidean.mixedSpace K)`. Establish `h : ⇑(toEuclid2 K) = WithLp.toLp 2 ∘ Prod.map (mixedToEuclidean K) (mixedToEuclidean K) ∘ MeasurableEquiv.finTwoArrow` using `rfl`. Rewrite using `[h]`.

Conclude with `h3.comp (h2.comp h1)`.
-/
theorem measurePreserving_toEuclid2 :
    MeasurePreserving (toEuclid2 K) (mixedMeasure2 K) volume := by
  have h1 := measurePreserving_finTwoArrow (selfDualMeasure K)
  have h2 := (measurePreserving_mixedToEuclidean K).prod (measurePreserving_mixedToEuclidean K)
  have h3 := WithLp.volume_preserving_toLp (euclidean.mixedSpace K) (euclidean.mixedSpace K)
  have h : ⇑(toEuclid2 K) = WithLp.toLp 2 ∘
      Prod.map (mixedToEuclidean K) (mixedToEuclidean K) ∘ MeasurableEquiv.finTwoArrow := rfl
  rw [h]
  exact h3.comp (h2.comp h1)

/- English proof (translation)
Establish `h1` using `measurePreserving_finTwoArrow (selfDualMeasure K)`. Establish `h2` using `(measurePreserving_mixedToEuclideanConj K).prod (measurePreserving_mixedToEuclideanConj K)`. Establish `h3` using `WithLp.volume_preserving_toLp (euclidean.mixedSpace K) (euclidean.mixedSpace K)`. Establish `h : ⇑(toEuclid2Conj K) = WithLp.toLp 2 ∘ Prod.map (mixedToEuclideanConj K) (mixedToEuclideanConj K) ∘ MeasurableEquiv.finTwoArrow`. Both sides reduce to the same expression.

Rewrite using `[h]`. Conclude with `h3.comp (h2.comp h1)`.
-/
theorem measurePreserving_toEuclid2Conj :
    MeasurePreserving (toEuclid2Conj K) (mixedMeasure2 K) volume := by
  have h1 := measurePreserving_finTwoArrow (selfDualMeasure K)
  have h2 := (measurePreserving_mixedToEuclideanConj K).prod
    (measurePreserving_mixedToEuclideanConj K)
  have h3 := WithLp.volume_preserving_toLp (euclidean.mixedSpace K) (euclidean.mixedSpace K)
  have h : ⇑(toEuclid2Conj K) = WithLp.toLp 2 ∘
      Prod.map (mixedToEuclideanConj K) (mixedToEuclideanConj K) ∘ MeasurableEquiv.finTwoArrow :=
    rfl
  rw [h]
  exact h3.comp (h2.comp h1)

/- English proof (translation)
Establish `: MeasurePreserving (toEuclid2 K).toHomeomorph.toMeasurableEquiv (mixedMeasure2 K) volume` using `measurePreserving_toEuclid2 K`. Conclude with `this.symm`.
-/
theorem measurePreserving_toEuclid2_symm :
    MeasurePreserving (toEuclid2 K).symm volume (mixedMeasure2 K) := by
  have : MeasurePreserving (toEuclid2 K).toHomeomorph.toMeasurableEquiv
      (mixedMeasure2 K) volume := measurePreserving_toEuclid2 K
  exact this.symm

def mixedFourier2 (f : (Fin 2 → mixedSpace K) → ℂ) (y : Fin 2 → mixedSpace K) : ℂ :=
  ∫ x, 𝐞 (-mixedPairing2 K x y) • f x ∂mixedMeasure2 K

def mixedFourierInv2 (f : (Fin 2 → mixedSpace K) → ℂ) (x : Fin 2 → mixedSpace K) : ℂ :=
  ∫ y, 𝐞 (mixedPairing2 K x y) • f y ∂mixedMeasure2 K

/- English proof (translation)
Rewrite using `[mixedFourier2, Real.fourier_eq, ← (measurePreserving_toEuclid2 K).integral_comp (toEuclid2 K).toHomeomorph.measurableEmbedding]`. Use `integral_congr_ae (Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `[mixedPairing2_eq_inner]`.
-/
theorem mixedFourier2_eq (f : (Fin 2 → mixedSpace K) → ℂ) (y : Fin 2 → mixedSpace K) :
    mixedFourier2 K f y = 𝓕 (f ∘ (toEuclid2 K).symm) (toEuclid2Conj K y) := by
  rw [mixedFourier2, Real.fourier_eq, ← (measurePreserving_toEuclid2 K).integral_comp
    (toEuclid2 K).toHomeomorph.measurableEmbedding]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [mixedPairing2_eq_inner]

/- English proof (translation)
Rewrite using `[mixedFourierInv2, Real.fourierInv_eq, ← (measurePreserving_toEuclid2Conj K).integral_comp (toEuclid2Conj K).toHomeomorph.measurableEmbedding]`. Use `integral_congr_ae (Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]`. Rewrite using `[mixedPairing2_eq_inner, real_inner_comm]`.
-/
theorem mixedFourierInv2_eq (f : (Fin 2 → mixedSpace K) → ℂ) (x : Fin 2 → mixedSpace K) :
    mixedFourierInv2 K f x = 𝓕⁻ (f ∘ (toEuclid2Conj K).symm) (toEuclid2 K x) := by
  rw [mixedFourierInv2, Real.fourierInv_eq, ← (measurePreserving_toEuclid2Conj K).integral_comp
    (toEuclid2Conj K).toHomeomorph.measurableEmbedding]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
  rw [mixedPairing2_eq_inner, real_inner_comm]

def mixedFourier2Schwartz : 𝓢(Fin 2 → mixedSpace K, ℂ) →L[ℂ] 𝓢(Fin 2 → mixedSpace K, ℂ) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (toEuclid2Conj K)).comp
    ((SchwartzMap.fourierTransformCLM ℂ).comp
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (toEuclid2 K).symm))

/- English proof (translation)
Use function extensionality and compare the values at `y`. Rewrite using `[mixedFourier2_eq]`. Both sides reduce to the same expression.
-/
theorem mixedFourier2Schwartz_apply (f : 𝓢(Fin 2 → mixedSpace K, ℂ)) :
    ⇑(mixedFourier2Schwartz K f) = mixedFourier2 K f := by
  funext y
  rw [mixedFourier2_eq]
  rfl

/- English proof (translation)
Use `set F : 𝓢(WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K), ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (toEuclid2 K).symm f with hFdef`. Establish `hF : (F : WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K) → ℂ) = f ∘ (toEuclid2 K).symm` using `rfl`. Establish `h1 : mixedFourier2 K f ∘ (toEuclid2Conj K).symm = 𝓕 (F : WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K) → ℂ)`. Use function extensionality and compare the values at `v`. Rewrite using `[Function.comp_apply, mixedFourier2_eq, ContinuousLinearEquiv.apply_symm_apply, hF]`.

Establish `h2 : Integrable (𝓕 (F : WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K) → ℂ))`. Rewrite using `[← SchwartzMap.fourier_coe]`. Conclude with `(𝓕 F).integrable`. Rewrite using `[mixedFourierInv2_eq, h1, F.continuous.fourierInv_fourier_eq F.integrable h2, hF, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]`.
-/
theorem mixedFourierInv2_mixedFourier2 (f : 𝓢(Fin 2 → mixedSpace K, ℂ))
    (x : Fin 2 → mixedSpace K) : mixedFourierInv2 K (mixedFourier2 K f) x = f x := by
  set F : 𝓢(WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K), ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (toEuclid2 K).symm f with hFdef
  have hF : (F : WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K) → ℂ) =
      f ∘ (toEuclid2 K).symm := rfl
  have h1 : mixedFourier2 K f ∘ (toEuclid2Conj K).symm =
      𝓕 (F : WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K) → ℂ) := by
    funext v
    rw [Function.comp_apply, mixedFourier2_eq, ContinuousLinearEquiv.apply_symm_apply, hF]
  have h2 : Integrable
      (𝓕 (F : WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K) → ℂ)) := by
    rw [← SchwartzMap.fourier_coe]
    exact (𝓕 F).integrable
  rw [mixedFourierInv2_eq, h1, F.continuous.fourierInv_fourier_eq F.integrable h2, hF,
    Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]

/- English proof (translation)
Rewrite using `[mixedFourier2, mixedFourierInv2]`. Use `integral_congr_ae (Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `only`. Rewrite using `[mixedPairing2_neg_right, neg_neg, mixedPairing2_comm]`.
-/
theorem mixedFourier2_neg (f : (Fin 2 → mixedSpace K) → ℂ) (x : Fin 2 → mixedSpace K) :
    mixedFourier2 K f (-x) = mixedFourierInv2 K f x := by
  rw [mixedFourier2, mixedFourierInv2]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  dsimp only
  rw [mixedPairing2_neg_right, neg_neg, mixedPairing2_comm]

/- English proof (translation)
Rewrite using `[← neg_neg x, mixedFourier2_neg, mixedFourierInv2_mixedFourier2, neg_neg]`.
-/
theorem mixedFourier2_mixedFourier2 (f : 𝓢(Fin 2 → mixedSpace K, ℂ))
    (x : Fin 2 → mixedSpace K) : mixedFourier2 K (mixedFourier2 K f) x = f (-x) := by
  rw [← neg_neg x, mixedFourier2_neg, mixedFourierInv2_mixedFourier2, neg_neg]

variable {K}

def idealLattice2 (I : Fin 2 → (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Submodule ℤ (Fin 2 → mixedSpace K) :=
  Submodule.pi Set.univ fun i => idealLattice K (I i)

/- English proof (translation)
Simplify using `[idealLattice2, Submodule.mem_pi]`.
-/
theorem mem_idealLattice2 {I : Fin 2 → (FractionalIdeal (𝓞 K)⁰ K)ˣ} {x : Fin 2 → mixedSpace K} :
    x ∈ idealLattice2 I ↔ ∀ i, x i ∈ idealLattice K (I i) := by
  simp [idealLattice2, Submodule.mem_pi]

instance (I : Fin 2 → (FractionalIdeal (𝓞 K)⁰ K)ˣ) : DiscreteTopology (idealLattice2 I) := by
  let f : idealLattice2 I → ∀ i, idealLattice K (I i) :=
    fun x i => ⟨x.1 i, mem_idealLattice2.mp x.2 i⟩
  have hc : Continuous f := continuous_pi fun i =>
    ((continuous_apply i).comp continuous_subtype_val).subtype_mk _
  have hi : Function.Injective f := fun x y h =>
    Subtype.ext (funext fun i => congrArg Subtype.val (congrFun h i))
  exact DiscreteTopology.of_continuous_injective hc hi

instance (I : Fin 2 → (FractionalIdeal (𝓞 K)⁰ K)ˣ) : IsZLattice ℝ (idealLattice2 I) where
  span_top := by
    classical
    rw [eq_top_iff]
    rintro x -
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hsp : x i ∈ Submodule.span ℝ (idealLattice K (I i) : Set (mixedSpace K)) := by
      rw [IsZLattice.span_top]
      trivial
    have hmap : Pi.single i (x i) ∈ (Submodule.span ℝ (idealLattice K (I i) : Set (mixedSpace K))).map
        (LinearMap.single ℝ (fun _ : Fin 2 => mixedSpace K) i) := ⟨x i, hsp, rfl⟩
    rw [← Submodule.span_image] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, mem_idealLattice2]
    intro j
    by_cases hj : j = i
    · subst hj
      simpa using hy
    · simp [Pi.single_eq_of_ne hj]

/- English proof (translation)
Use `set b := fun i => (Module.Free.chooseBasis ℤ (idealLattice K (I i))).ofZLatticeBasis ℝ (idealLattice K (I i))`. Establish `hspan : ∀ i, Submodule.span ℤ (Set.range (b i)) = idealLattice K (I i)` using `fun i => (Module.Free.chooseBasis ℤ (idealLattice K (I i))).ofZLatticeBasis_span ℝ _`. Use `IsAddFundamentalDomain.mk' (MeasurableSet.univ_pi fun i => ZSpan.fundamentalDomain_measurableSet _).nullMeasurableSet fun x => ?_` and prove the remaining obligations. Establish `h` using `fun i => ZSpan.exist_unique_vadd_mem_fundamentalDomain (b i) (x i)`. Use `choose v hv hvu using h`.

Establish `hvmem : ∀ i, (v i : mixedSpace K) ∈ idealLattice K (I i)` using `fun i => by`. Establish `key : ∀ z ∈ Submodule.span ℤ (Set.range (b i)), z ∈ idealLattice K (I i)` using `fun z hz => hspan i ▸ hz`. Conclude with `key _ (v i).2`. Use `⟨⟨fun i => (v i : mixedSpace K), mem_idealLattice2.mpr hvmem⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `i _`.

Conclude with `hv i`. Introduce and unpack `g hg`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Establish `hgi : (g : Fin 2 → mixedSpace K) i ∈ Submodule.span ℤ (Set.range (b i))`.

Rewrite using `[hspan i]`. Conclude with `mem_idealLattice2.mp g.2 i`. Use `hvu i ⟨_, hgi⟩ (hg i trivial)` as an intermediate fact. Conclude with `congrArg Subtype.val this`.
-/
theorem isAddFundamentalDomain_idealLattice2 (I : Fin 2 → (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    IsAddFundamentalDomain (idealLattice2 I)
      (Set.univ.pi fun i => ZSpan.fundamentalDomain
        ((Module.Free.chooseBasis ℤ (idealLattice K (I i))).ofZLatticeBasis ℝ
          (idealLattice K (I i)))) (mixedMeasure2 K) := by
  set b := fun i => (Module.Free.chooseBasis ℤ (idealLattice K (I i))).ofZLatticeBasis ℝ
    (idealLattice K (I i))
  have hspan : ∀ i, Submodule.span ℤ (Set.range (b i)) = idealLattice K (I i) := fun i =>
    (Module.Free.chooseBasis ℤ (idealLattice K (I i))).ofZLatticeBasis_span ℝ _
  refine IsAddFundamentalDomain.mk'
    (MeasurableSet.univ_pi fun i => ZSpan.fundamentalDomain_measurableSet _).nullMeasurableSet
    fun x => ?_
  have h := fun i => ZSpan.exist_unique_vadd_mem_fundamentalDomain (b i) (x i)
  choose v hv hvu using h
  have hvmem : ∀ i, (v i : mixedSpace K) ∈ idealLattice K (I i) := fun i => by
    have key : ∀ z ∈ Submodule.span ℤ (Set.range (b i)), z ∈ idealLattice K (I i) :=
      fun z hz => hspan i ▸ hz
    exact key _ (v i).2
  refine ⟨⟨fun i => (v i : mixedSpace K), mem_idealLattice2.mpr hvmem⟩, ?_, ?_⟩
  · intro i _
    exact hv i
  · rintro g hg
    apply Subtype.ext
    funext i
    have hgi : (g : Fin 2 → mixedSpace K) i ∈ Submodule.span ℤ (Set.range (b i)) := by
      rw [hspan i]
      exact mem_idealLattice2.mp g.2 i
    have := hvu i ⟨_, hgi⟩ (hg i trivial)
    exact congrArg Subtype.val this

/- English proof (translation)
Rewrite using `[ZLattice.covolume_eq_measure_fundamentalDomain _ _ (isAddFundamentalDomain_idealLattice2 I), measureReal_def, mixedMeasure2, Measure.pi_pi, ENNReal.toReal_prod]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← covolume_idealLattice_selfDualMeasure, ZLattice.covolume_eq_measure_fundamentalDomain _ _ (ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ (idealLattice K (I i))) _), measureReal_def]`.
-/
theorem covolume_idealLattice2 (I : Fin 2 → (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (idealLattice2 I) (mixedMeasure2 K) =
      ∏ i, ((FractionalIdeal.absNorm (I i : FractionalIdeal (𝓞 K)⁰ K) : ℝ) * √|(discr K : ℝ)|) := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ (isAddFundamentalDomain_idealLattice2 I),
    measureReal_def, mixedMeasure2, Measure.pi_pi, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← covolume_idealLattice_selfDualMeasure, ZLattice.covolume_eq_measure_fundamentalDomain _ _
    (ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ (idealLattice K (I i))) _),
    measureReal_def]

abbrev euclidLattice2 (I : Fin 2 → (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Submodule ℤ (WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K)) :=
  ZLattice.comap ℝ (idealLattice2 I) (toEuclid2 K).symm.toLinearMap

abbrev euclidConjLattice2 (I : Fin 2 → (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Submodule ℤ (WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K)) :=
  ZLattice.comap ℝ (idealLattice2 I) (toEuclid2Conj K).symm.toLinearMap

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_euclidLattice2 (I : Fin 2 → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (u : WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K)) :
    u ∈ euclidLattice2 I ↔ (toEuclid2 K).symm u ∈ idealLattice2 I := Iff.rfl

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_euclidConjLattice2 (I : Fin 2 → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (u : WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K)) :
    u ∈ euclidConjLattice2 I ↔ (toEuclid2Conj K).symm u ∈ idealLattice2 I := Iff.rfl

/- English proof (translation)
Rewrite using `[ZLattice.covolume_comap (idealLattice2 I) (mixedMeasure2 K) volume (measurePreserving_toEuclid2_symm K), covolume_idealLattice2]`.
-/
theorem covolume_euclidLattice2 (I : Fin 2 → (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (euclidLattice2 I) =
      ∏ i, ((FractionalIdeal.absNorm (I i : FractionalIdeal (𝓞 K)⁰ K) : ℝ) * √|(discr K : ℝ)|) := by
  rw [ZLattice.covolume_comap (idealLattice2 I) (mixedMeasure2 K) volume
    (measurePreserving_toEuclid2_symm K), covolume_idealLattice2]

/- English proof (translation)
Rewrite using `[mixedPairing2, Fin.sum_univ_two]`. Apply the tactic sequence `fin_cases i <;> simp`.
-/
theorem mixedPairing2_single_left (i : Fin 2) (x : mixedSpace K) (y : Fin 2 → mixedSpace K) :
    mixedPairing2 K (Pi.single i x) y = mixedTraceForm K x (y i) := by
  rw [mixedPairing2, Fin.sum_univ_two]
  fin_cases i <;> simp

/- English proof (translation)
Use extensionality with `μ`. Rewrite using `[mem_dualLattice, mem_euclidConjLattice2, mem_idealLattice2]`. Use `set y := (toEuclid2Conj K).symm μ with hy`. Establish `hμ : μ = toEuclid2Conj K y` using `by rw [hy, ContinuousLinearEquiv.apply_symm_apply]`. Prove the components needed by the constructor for the conclusion.

Introduce `h i`. Rewrite using `[mem_idealLattice_traceDualIdeal_iff]`. Introduce `x hx`. Establish `hmem : toEuclid2 K (Pi.single i x) ∈ euclidLattice2 I`. Rewrite using `[mem_euclidLattice2, ContinuousLinearEquiv.symm_apply_apply, mem_idealLattice2]`.

Introduce `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `using hx`. Simplify using `[Pi.single_eq_of_ne hj]`.

Take `⟨k, hk⟩` from `h _ hmem`. Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite `hk` using `[hμ, real_inner_comm, ← mixedPairing2_eq_inner, mixedPairing2_single_left]`. Rewrite using `[mixedTraceForm_comm]`. Conclude with `hk`.

Introduce `h ℓ hℓ`. Rewrite `hℓ` using `[mem_euclidLattice2, mem_idealLattice2]`. Establish `hk : ∀ i, ∃ n : ℤ, mixedTraceForm K (y i) (((toEuclid2 K).symm ℓ) i) = n` using `fun i => (mem_idealLattice_traceDualIdeal_iff K (I i) (y i)).mp (h i) _ (hℓ i)`. Use `choose n hn using hk`. Use `⟨∑ i, n i, ?_⟩` and prove the remaining obligations.

Establish `hℓ' : ℓ = toEuclid2 K ((toEuclid2 K).symm ℓ)`. Rewrite using `[ContinuousLinearEquiv.apply_symm_apply]`. Rewrite using `[hμ, hℓ', real_inner_comm, ← mixedPairing2_eq_inner, mixedPairing2]`. Use `push_cast`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[mixedTraceForm_comm, hn i]`.
-/
theorem dualLattice_euclidLattice2 (I : Fin 2 → (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    dualLattice (euclidLattice2 I) = euclidConjLattice2 (fun i => traceDualIdeal K (I i)) := by
  ext μ
  rw [mem_dualLattice, mem_euclidConjLattice2, mem_idealLattice2]
  set y := (toEuclid2Conj K).symm μ with hy
  have hμ : μ = toEuclid2Conj K y := by rw [hy, ContinuousLinearEquiv.apply_symm_apply]
  constructor
  · intro h i
    rw [mem_idealLattice_traceDualIdeal_iff]
    intro x hx
    have hmem : toEuclid2 K (Pi.single i x) ∈ euclidLattice2 I := by
      rw [mem_euclidLattice2, ContinuousLinearEquiv.symm_apply_apply, mem_idealLattice2]
      intro j
      by_cases hj : j = i
      · subst hj
        simpa using hx
      · simp [Pi.single_eq_of_ne hj]
    obtain ⟨k, hk⟩ := h _ hmem
    refine ⟨k, ?_⟩
    rw [hμ, real_inner_comm, ← mixedPairing2_eq_inner, mixedPairing2_single_left] at hk
    rw [mixedTraceForm_comm]
    exact hk
  · intro h ℓ hℓ
    rw [mem_euclidLattice2, mem_idealLattice2] at hℓ
    have hk : ∀ i, ∃ n : ℤ, mixedTraceForm K (y i) (((toEuclid2 K).symm ℓ) i) = n := fun i =>
      (mem_idealLattice_traceDualIdeal_iff K (I i) (y i)).mp (h i) _ (hℓ i)
    choose n hn using hk
    refine ⟨∑ i, n i, ?_⟩
    have hℓ' : ℓ = toEuclid2 K ((toEuclid2 K).symm ℓ) := by
      rw [ContinuousLinearEquiv.apply_symm_apply]
    rw [hμ, hℓ', real_inner_comm, ← mixedPairing2_eq_inner, mixedPairing2]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mixedTraceForm_comm, hn i]

/- English proof (translation)
Simplify `summable_norm_comp_add (idealLattice2 I) f a` using `[add_comm]`.
-/
theorem idealLattice2_summable_norm (I : Fin 2 → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (f : 𝓢(Fin 2 → mixedSpace K, ℂ)) (a : Fin 2 → mixedSpace K) :
    Summable fun α : idealLattice2 I => ‖f (α + a)‖ := by
  simpa [add_comm] using summable_norm_comp_add (idealLattice2 I) f a

/- English proof (translation)
Establish `h` using `summable_norm_comp_add (idealLattice2 (fun i => traceDualIdeal K (I i))) (mixedFourier2Schwartz K f) 0`. Simplify using `only [zero_add, mixedFourier2Schwartz_apply] at h`. Simplify `h` using `only [norm_mul, Circle.norm_coe, mul_one]`.
-/
theorem dualIdealLattice2_summable_norm (I : Fin 2 → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (f : 𝓢(Fin 2 → mixedSpace K, ℂ)) (a : Fin 2 → mixedSpace K) :
    Summable fun β : idealLattice2 (fun i => traceDualIdeal K (I i)) =>
      ‖mixedFourier2 K f β * 𝐞 (mixedPairing2 K β a)‖ := by
  have h := summable_norm_comp_add (idealLattice2 (fun i => traceDualIdeal K (I i)))
    (mixedFourier2Schwartz K f) 0
  simp only [zero_add, mixedFourier2Schwartz_apply] at h
  simpa only [norm_mul, Circle.norm_coe, mul_one] using h

/- English proof (translation)
Use `set L := euclidLattice2 I`. Use `set F : 𝓢(WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K), ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (toEuclid2 K).symm f`. Establish `hF : (F : WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K) → ℂ) = f ∘ (toEuclid2 K).symm` using `rfl`. Establish `h` using `lattice_poisson_summation L F (toEuclid2 K a)`. Set `eL : idealLattice2 I ≃ L` to `{ toFun := fun α => ⟨toEuclid2 K α, by`.

Rewrite using `[mem_euclidLattice2, ContinuousLinearEquiv.symm_apply_apply]`. Conclude with `α.2⟩`. Use `invFun := fun ℓ => ⟨(toEuclid2 K).symm ℓ, ℓ.2⟩`. Use `left_inv := fun α => Subtype.ext (ContinuousLinearEquiv.symm_apply_apply _ _)`. Use `right_inv := fun ℓ => Subtype.ext (ContinuousLinearEquiv.apply_symm_apply _ _) }`.

Set `eD : idealLattice2 (fun i => traceDualIdeal K (I i)) ≃ dualLattice L` to `{ toFun := fun β => ⟨toEuclid2Conj K β, by`. Rewrite using `[dualLattice_euclidLattice2, mem_euclidConjLattice2, ContinuousLinearEquiv.symm_apply_apply]`. Conclude with `β.2⟩`. Use `invFun := fun μ => ⟨(toEuclid2Conj K).symm μ, by`. Establish `hμ : (μ : WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K)) ∈ euclidConjLattice2 (fun i => traceDualIdeal K (I i))`.

Rewrite using `[← dualLattice_euclidLattice2]`. Conclude with `μ.2`. Conclude with `hμ⟩`. Use `left_inv := fun β => Subtype.ext (ContinuousLinearEquiv.symm_apply_apply _ _)`. Use `right_inv := fun μ => Subtype.ext (ContinuousLinearEquiv.apply_symm_apply _ _) }`.

Establish `hlhs : ∑' ℓ : L, F (ℓ + toEuclid2 K a) = ∑' α : idealLattice2 I, f (α + a)`. Rewrite using `[← Equiv.tsum_eq eL]`. Use `tsum_congr fun α => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `f ((toEuclid2 K).symm (toEuclid2 K α + toEuclid2 K a)) = _`. Rewrite using `[← map_add, ContinuousLinearEquiv.symm_apply_apply]`.

Establish `hrhs : ∑' μ : dualLattice L, 𝓕 (F : WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K) → ℂ) μ * 𝐞 ⟪(μ : WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K)), toEuclid2 K a⟫ = ∑' β : idealLattice2 (fun i => traceDualIdeal K (I i)), mixedFourier2 K f β * 𝐞 (mixedPair …`. Rewrite using `[← Equiv.tsum_eq eD]`. Use `tsum_congr fun β => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `𝓕 (F : WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K) → ℂ) (toEuclid2Conj K β) * 𝐞 ⟪toEuclid2Conj K β, toEuclid2 K a⟫ = _`. Rewrite using `[hF, ← mixedFourier2_eq, real_inner_comm, ← mixedPairing2_eq_inner, mixedPairing2_comm]`.

Rewrite `h` using `[hlhs, hrhs, covolume_euclidLattice2]`. Conclude with `h`.
-/
theorem idealLattice2_poisson_summation (I : Fin 2 → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (f : 𝓢(Fin 2 → mixedSpace K, ℂ)) (a : Fin 2 → mixedSpace K) :
    ∑' α : idealLattice2 I, f (α + a) =
      (∏ i, ((FractionalIdeal.absNorm (I i : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
        √|(discr K : ℝ)|))⁻¹ •
        ∑' β : idealLattice2 (fun i => traceDualIdeal K (I i)),
          mixedFourier2 K f β * 𝐞 (mixedPairing2 K β a) := by
  set L := euclidLattice2 I
  set F : 𝓢(WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K), ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (toEuclid2 K).symm f
  have hF : (F : WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K) → ℂ) =
      f ∘ (toEuclid2 K).symm := rfl
  have h := lattice_poisson_summation L F (toEuclid2 K a)
  let eL : idealLattice2 I ≃ L :=
    { toFun := fun α => ⟨toEuclid2 K α, by
        rw [mem_euclidLattice2, ContinuousLinearEquiv.symm_apply_apply]; exact α.2⟩
      invFun := fun ℓ => ⟨(toEuclid2 K).symm ℓ, ℓ.2⟩
      left_inv := fun α => Subtype.ext (ContinuousLinearEquiv.symm_apply_apply _ _)
      right_inv := fun ℓ => Subtype.ext (ContinuousLinearEquiv.apply_symm_apply _ _) }
  let eD : idealLattice2 (fun i => traceDualIdeal K (I i)) ≃ dualLattice L :=
    { toFun := fun β => ⟨toEuclid2Conj K β, by
        rw [dualLattice_euclidLattice2, mem_euclidConjLattice2,
          ContinuousLinearEquiv.symm_apply_apply]; exact β.2⟩
      invFun := fun μ => ⟨(toEuclid2Conj K).symm μ, by
        have hμ : (μ : WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K)) ∈
            euclidConjLattice2 (fun i => traceDualIdeal K (I i)) := by
          rw [← dualLattice_euclidLattice2]
          exact μ.2
        exact hμ⟩
      left_inv := fun β => Subtype.ext (ContinuousLinearEquiv.symm_apply_apply _ _)
      right_inv := fun μ => Subtype.ext (ContinuousLinearEquiv.apply_symm_apply _ _) }
  have hlhs : ∑' ℓ : L, F (ℓ + toEuclid2 K a) = ∑' α : idealLattice2 I, f (α + a) := by
    rw [← Equiv.tsum_eq eL]
    refine tsum_congr fun α => ?_
    change f ((toEuclid2 K).symm (toEuclid2 K α + toEuclid2 K a)) = _
    rw [← map_add, ContinuousLinearEquiv.symm_apply_apply]
  have hrhs : ∑' μ : dualLattice L,
      𝓕 (F : WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K) → ℂ) μ *
        𝐞 ⟪(μ : WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K)), toEuclid2 K a⟫ =
      ∑' β : idealLattice2 (fun i => traceDualIdeal K (I i)),
        mixedFourier2 K f β * 𝐞 (mixedPairing2 K β a) := by
    rw [← Equiv.tsum_eq eD]
    refine tsum_congr fun β => ?_
    change 𝓕 (F : WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K) → ℂ)
        (toEuclid2Conj K β) * 𝐞 ⟪toEuclid2Conj K β, toEuclid2 K a⟫ = _
    rw [hF, ← mixedFourier2_eq, real_inner_comm, ← mixedPairing2_eq_inner, mixedPairing2_comm]
  rw [hlhs, hrhs, covolume_euclidLattice2] at h
  exact h

variable (K) in

def emb2 (ξ : Fin 2 → K) : Fin 2 → mixedSpace K := fun i => mixedEmbedding K (ξ i)

variable (K) in

def coset2 (I : Fin 2 → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (c : Fin 2 → K) : Set (Fin 2 → K) :=
  {ξ | ∀ i, ξ i - c i ∈ (I i : FractionalIdeal (𝓞 K)⁰ K)}

omit [NumberField K] in
/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[emb2]`.
-/
theorem emb2_zero : emb2 K 0 = 0 := by
  funext i
  simp [emb2]

/- English proof (translation)
Establish `hpre : ∀ α : idealLattice2 I, ∀ i, ∃ y ∈ ((I i : FractionalIdeal (𝓞 K)⁰ K) : Set K), mixedEmbedding K y = (α : Fin 2 → mixedSpace K) i` using `fun α i => (mem_idealLattice K (I i)).mp (mem_idealLattice2.mp α.2 i)`. Use `choose y hyI hy using hpre`. Use `set h : idealLattice2 I → Fin 2 → K := fun α i => c i + y α i with hh`. Establish `hinj : Function.Injective h`. Introduce `α β hαβ`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Establish `h1 : y α i = y β i` using `add_left_cancel (congrFun hαβ i)`. Rewrite using `[← hy α i, ← hy β i, h1]`. Establish `hmem : ∀ α, h α ∈ coset2 K I c` using `fun α i => by`.

Simplify using `only [hh, add_sub_cancel_left]`. Conclude with `hyI α i`. Establish `hemb : ∀ α, emb2 K (h α) = (α : Fin 2 → mixedSpace K) + emb2 K c`. Introduce `α`. Use function extensionality and compare the values at `i`.

Simplify using `only [emb2, hh, Pi.add_apply, map_add, hy α i, add_comm]`. Use `set G : (Fin 2 → K) → ℂ := (coset2 K I c).indicator (fun ξ => g (emb2 K ξ))`. Establish `hsupp : ∀ ξ ∉ Set.range h, G ξ = 0`. Introduce `ξ hξ`. Use `Set.indicator_of_notMem (fun hm => hξ ?_) _` and prove the remaining obligations.

Establish `hα : emb2 K (fun i => ξ i - c i) ∈ idealLattice2 I`. Rewrite using `[mem_idealLattice2]`. Introduce `i`. Conclude with `(mem_idealLattice K (I i)).mpr ⟨ξ i - c i, hm i, rfl⟩`. Use `⟨⟨_, hα⟩, funext fun i => ?_⟩` and prove the remaining obligations.

Establish `h2 : mixedEmbedding K (y ⟨_, hα⟩ i) = mixedEmbedding K (ξ i - c i)` using `hy _ i`. Establish `h3` using `mixedEmbedding_injective K h2`. Simplify using `only [hh, h3]`. Expand and normalize the polynomial expressions, which then agree. Establish `hGh : ∀ α, G (h α) = g (α + emb2 K c)`.

Introduce `α`. Simplify using `only [G]`. Rewrite using `[Set.indicator_of_mem (hmem α), hemb]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hinj.summable_iff (f := fun ξ => ‖G ξ‖) (fun ξ hξ => by simp [hsupp ξ hξ])]`.

Simplify using `only [Function.comp_def, hGh]`. Rewrite using `[← hinj.tsum_eq (fun ξ hξ => by_contra fun hn => hξ (hsupp ξ hn))]`. Simplify using `only [hGh]`.
-/
theorem summable_norm_iff_and_tsum_eq_coset2 (I : Fin 2 → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (c : Fin 2 → K) (g : (Fin 2 → mixedSpace K) → ℂ) :
    (Summable (fun ξ => ‖(coset2 K I c).indicator (fun ξ => g (emb2 K ξ)) ξ‖) ↔
      Summable (fun α : idealLattice2 I => ‖g (α + emb2 K c)‖)) ∧
      ∑' ξ, (coset2 K I c).indicator (fun ξ => g (emb2 K ξ)) ξ =
        ∑' α : idealLattice2 I, g (α + emb2 K c) := by
  have hpre : ∀ α : idealLattice2 I, ∀ i, ∃ y ∈ ((I i : FractionalIdeal (𝓞 K)⁰ K) : Set K),
      mixedEmbedding K y = (α : Fin 2 → mixedSpace K) i := fun α i =>
    (mem_idealLattice K (I i)).mp (mem_idealLattice2.mp α.2 i)
  choose y hyI hy using hpre
  set h : idealLattice2 I → Fin 2 → K := fun α i => c i + y α i with hh
  have hinj : Function.Injective h := by
    intro α β hαβ
    apply Subtype.ext
    funext i
    have h1 : y α i = y β i := add_left_cancel (congrFun hαβ i)
    rw [← hy α i, ← hy β i, h1]
  have hmem : ∀ α, h α ∈ coset2 K I c := fun α i => by
    simp only [hh, add_sub_cancel_left]
    exact hyI α i
  have hemb : ∀ α, emb2 K (h α) = (α : Fin 2 → mixedSpace K) + emb2 K c := by
    intro α
    funext i
    simp only [emb2, hh, Pi.add_apply, map_add, hy α i, add_comm]
  set G : (Fin 2 → K) → ℂ := (coset2 K I c).indicator (fun ξ => g (emb2 K ξ))
  have hsupp : ∀ ξ ∉ Set.range h, G ξ = 0 := by
    intro ξ hξ
    refine Set.indicator_of_notMem (fun hm => hξ ?_) _
    have hα : emb2 K (fun i => ξ i - c i) ∈ idealLattice2 I := by
      rw [mem_idealLattice2]
      intro i
      exact (mem_idealLattice K (I i)).mpr ⟨ξ i - c i, hm i, rfl⟩
    refine ⟨⟨_, hα⟩, funext fun i => ?_⟩
    have h2 : mixedEmbedding K (y ⟨_, hα⟩ i) = mixedEmbedding K (ξ i - c i) := hy _ i
    have h3 := mixedEmbedding_injective K h2
    simp only [hh, h3]
    ring
  have hGh : ∀ α, G (h α) = g (α + emb2 K c) := by
    intro α
    simp only [G]
    rw [Set.indicator_of_mem (hmem α), hemb]
  refine ⟨?_, ?_⟩
  · rw [← hinj.summable_iff (f := fun ξ => ‖G ξ‖) (fun ξ hξ => by simp [hsupp ξ hξ])]
    simp only [Function.comp_def, hGh]
  · rw [← hinj.tsum_eq (fun ξ hξ => by_contra fun hn => hξ (hsupp ξ hn))]
    simp only [hGh]

/- English proof (translation)
Establish `hL` using `summable_norm_iff_and_tsum_eq_coset2 I c f`. Establish `hR` using `summable_norm_iff_and_tsum_eq_coset2 (fun i => traceDualIdeal K (I i)) 0 (fun v => mixedFourier2 K f v * (𝐞 (mixedPairing2 K v (emb2 K c)) : ℂ))`. Simplify using `only [emb2_zero, add_zero] at hR`. Use `⟨hL.1.mpr (idealLattice2_summable_norm I f (emb2 K c)), hR.1.mpr (dualIdealLattice2_summable_norm I f (emb2 K c)), ?_⟩` and prove the remaining obligations. Rewrite using `[hL.2, hR.2, idealLattice2_poisson_summation, Complex.real_smul]`.
-/
theorem poisson2_coset (I : Fin 2 → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (c : Fin 2 → K)
    (f : 𝓢(Fin 2 → mixedSpace K, ℂ)) :
    Summable (fun ξ : Fin 2 → K => ‖(coset2 K I c).indicator (fun ξ => f (emb2 K ξ)) ξ‖) ∧
    Summable (fun η : Fin 2 → K => ‖(coset2 K (fun i => traceDualIdeal K (I i)) 0).indicator
      (fun η => mixedFourier2 K f (emb2 K η) *
        (𝐞 (mixedPairing2 K (emb2 K η) (emb2 K c)) : ℂ)) η‖) ∧
    ∑' ξ : Fin 2 → K, (coset2 K I c).indicator (fun ξ => f (emb2 K ξ)) ξ =
      (((∏ i, ((FractionalIdeal.absNorm (I i : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
        √|(discr K : ℝ)|))⁻¹ : ℝ) : ℂ) *
        ∑' η : Fin 2 → K, (coset2 K (fun i => traceDualIdeal K (I i)) 0).indicator
          (fun η => mixedFourier2 K f (emb2 K η) *
            (𝐞 (mixedPairing2 K (emb2 K η) (emb2 K c)) : ℂ)) η := by
  have hL := summable_norm_iff_and_tsum_eq_coset2 I c f
  have hR := summable_norm_iff_and_tsum_eq_coset2 (fun i => traceDualIdeal K (I i)) 0
    (fun v => mixedFourier2 K f v * (𝐞 (mixedPairing2 K v (emb2 K c)) : ℂ))
  simp only [emb2_zero, add_zero] at hR
  refine ⟨hL.1.mpr (idealLattice2_summable_norm I f (emb2 K c)),
    hR.1.mpr (dualIdealLattice2_summable_norm I f (emb2 K c)), ?_⟩
  rw [hL.2, hR.2, idealLattice2_poisson_summation, Complex.real_smul]

end

end GroundTheory.Automorphic.Adele2
