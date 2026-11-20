import Mathlib
import GroundTheory.GlobalFields.TateThesis.TraceLatticePoisson

namespace GroundTheory.Automorphic.GJMatrix

open GroundTheory.Global NumberField NumberField.mixedEmbedding MeasureTheory Module Filter
open scoped FourierTransform SchwartzMap RealInnerProductSpace nonZeroDivisors Classical

set_option synthInstance.maxSize 1000

noncomputable section

/- English proof (translation)
Use `⟨(MeasurableEquiv.curry α κ X).symm.measurable, ?_⟩` and prove the remaining obligations. Use `(Measure.pi_eq (μ := fun _ : α × κ ↦ μ) fun s hs ↦ ?_).symm` and prove the remaining obligations. Rewrite using `[MeasurableEquiv.map_apply]`. Establish `h : (MeasurableEquiv.curry α κ X).symm ⁻¹' Set.univ.pi s = Set.univ.pi fun a ↦ Set.univ.pi fun k ↦ s (a, k)`. Use extensionality with `x`.

Simplify using `only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Prod.forall]`. Both sides reduce to the same expression. Rewrite using `[h, Measure.pi_pi]`. Repeatedly rewrite using `[Measure.pi_pi]`. Rewrite using `[← Fintype.prod_prod_type']`.
-/
theorem measurePreserving_curry_symm {α κ X : Type*} [Fintype α] [Fintype κ] [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] :
    MeasurePreserving (MeasurableEquiv.curry α κ X).symm
      (Measure.pi fun _ : α ↦ Measure.pi fun _ : κ ↦ μ) (Measure.pi fun _ : α × κ ↦ μ) := by
  refine ⟨(MeasurableEquiv.curry α κ X).symm.measurable, ?_⟩
  refine (Measure.pi_eq (μ := fun _ : α × κ ↦ μ) fun s hs ↦ ?_).symm
  rw [MeasurableEquiv.map_apply]
  have h : (MeasurableEquiv.curry α κ X).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi fun a ↦ Set.univ.pi fun k ↦ s (a, k) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Prod.forall]
    rfl
  rw [h, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [← Fintype.prod_prod_type']

variable (K : Type*) [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι]

def mixedPairingPi (x y : ι → mixedSpace K) : ℝ := ∑ i, mixedTraceForm K (x i) (y i)

/- English proof (translation)
The claim follows from `Finset.sum_congr rfl fun i _ ↦ mixedTraceForm_comm K (x i) (y i)`.
-/
theorem mixedPairingPi_comm (x y : ι → mixedSpace K) :
    mixedPairingPi K x y = mixedPairingPi K y x :=
  Finset.sum_congr rfl fun i _ ↦ mixedTraceForm_comm K (x i) (y i)

/- English proof (translation)
Simplify using `only [mixedPairingPi, Pi.neg_apply, map_neg, Finset.sum_neg_distrib]`.
-/
theorem mixedPairingPi_neg_right (x y : ι → mixedSpace K) :
    mixedPairingPi K x (-y) = -mixedPairingPi K x y := by
  simp only [mixedPairingPi, Pi.neg_apply, map_neg, Finset.sum_neg_distrib]

def mixedMeasurePi : Measure (ι → mixedSpace K) := Measure.pi fun _ ↦ selfDualMeasure K

instance : (mixedMeasurePi K : Measure (ι → mixedSpace K)).IsAddHaarMeasure := by
  unfold mixedMeasurePi
  infer_instance

variable (ι) in

abbrev EuclidPi : Type _ := EuclideanSpace ℝ (ι × Fin (finrank ℝ (euclidean.mixedSpace K)))

def euclidPiEquiv : (ι → euclidean.mixedSpace K) ≃L[ℝ] EuclidPi K ι :=
  (((LinearEquiv.piCongrRight fun _ : ι ↦
      ((stdOrthonormalBasis ℝ (euclidean.mixedSpace K)).repr.toLinearEquiv.trans
        (WithLp.linearEquiv 2 ℝ (Fin (finrank ℝ (euclidean.mixedSpace K)) → ℝ)))).trans
    (LinearEquiv.curry ℝ ℝ ι (Fin (finrank ℝ (euclidean.mixedSpace K)))).symm).trans
    (WithLp.linearEquiv 2 ℝ _).symm).toContinuousLinearEquiv

/- English proof (translation)
Rewrite using `[PiLp.inner_apply, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun i _ ↦ ?_` and prove the remaining obligations. Rewrite using `[← (stdOrthonormalBasis ℝ (euclidean.mixedSpace K)).repr.inner_map_map (u i) (v i), PiLp.inner_apply]`. Both sides reduce to the same expression.
-/
theorem inner_euclidPiEquiv (u v : ι → euclidean.mixedSpace K) :
    ⟪euclidPiEquiv K u, euclidPiEquiv K v⟫ = ∑ i, ⟪u i, v i⟫ := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← (stdOrthonormalBasis ℝ (euclidean.mixedSpace K)).repr.inner_map_map (u i) (v i),
    PiLp.inner_apply]
  rfl

/- English proof (translation)
Use `set b := stdOrthonormalBasis ℝ (euclidean.mixedSpace K)`. Establish `h1 : MeasurePreserving (fun (u : ι → euclidean.mixedSpace K) (i : ι) ↦ WithLp.ofLp (b.repr (u i))) (Measure.pi fun _ : ι ↦ (volume : Measure (euclidean.mixedSpace K))) (Measure.pi fun _ : ι ↦ (volume : Measure (Fin (finrank ℝ (euclidean.mixedSpace K)) → ℝ)))` using `measurePreserving_pi _ _ fun _ ↦ (PiLp.volume_preserving_ofLp _).comp b.measurePreserving_repr`. Establish `h2` using `measurePreserving_curry_symm (α := ι) (κ := Fin (finrank ℝ (euclidean.mixedSpace K))) (volume : Measure ℝ)`. Establish `h3` using `PiLp.volume_preserving_toLp (ι × Fin (finrank ℝ (euclidean.mixedSpace K)))`. Establish `h : ⇑(euclidPiEquiv K (ι` using `ι)) = WithLp.toLp 2 ∘ (MeasurableEquiv.curry ι (Fin (finrank ℝ (euclidean.mixedSpace K))) ℝ).symm ∘ fun (u : ι → euclidean.mixedSpace K) (i : ι) ↦ WithLp.ofLp (b.repr (u i)) := rfl`.

Rewrite using `[h]`. Conclude with `h3.comp (h2.comp h1)`.
-/
theorem measurePreserving_euclidPiEquiv :
    MeasurePreserving (euclidPiEquiv K (ι := ι))
      (Measure.pi fun _ : ι ↦ (volume : Measure (euclidean.mixedSpace K))) volume := by
  set b := stdOrthonormalBasis ℝ (euclidean.mixedSpace K)
  have h1 : MeasurePreserving
      (fun (u : ι → euclidean.mixedSpace K) (i : ι) ↦ WithLp.ofLp (b.repr (u i)))
      (Measure.pi fun _ : ι ↦ (volume : Measure (euclidean.mixedSpace K)))
      (Measure.pi fun _ : ι ↦
        (volume : Measure (Fin (finrank ℝ (euclidean.mixedSpace K)) → ℝ))) :=
    measurePreserving_pi _ _ fun _ ↦ (PiLp.volume_preserving_ofLp _).comp b.measurePreserving_repr
  have h2 := measurePreserving_curry_symm (α := ι) (κ := Fin (finrank ℝ (euclidean.mixedSpace K)))
    (volume : Measure ℝ)
  have h3 := PiLp.volume_preserving_toLp (ι × Fin (finrank ℝ (euclidean.mixedSpace K)))
  have h : ⇑(euclidPiEquiv K (ι := ι)) =
      WithLp.toLp 2 ∘ (MeasurableEquiv.curry ι (Fin (finrank ℝ (euclidean.mixedSpace K))) ℝ).symm ∘
        fun (u : ι → euclidean.mixedSpace K) (i : ι) ↦ WithLp.ofLp (b.repr (u i)) := rfl
  rw [h]
  exact h3.comp (h2.comp h1)

def toEuclidPi : (ι → mixedSpace K) ≃L[ℝ] EuclidPi K ι :=
  (ContinuousLinearEquiv.piCongrRight fun _ : ι ↦ mixedToEuclidean K).trans (euclidPiEquiv K)

def toEuclidPiConj : (ι → mixedSpace K) ≃L[ℝ] EuclidPi K ι :=
  (ContinuousLinearEquiv.piCongrRight fun _ : ι ↦ mixedToEuclideanConj K).trans (euclidPiEquiv K)

/- English proof (translation)
Rewrite using `[toEuclidPi, toEuclidPiConj, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply, inner_euclidPiEquiv, mixedPairingPi]`. Use `Finset.sum_congr rfl fun i _ ↦ ?_` and prove the remaining obligations. Rewrite using `[mixedTraceForm_eq_inner]`. Both sides reduce to the same expression.
-/
theorem mixedPairingPi_eq_inner (x y : ι → mixedSpace K) :
    mixedPairingPi K x y = ⟪toEuclidPi K x, toEuclidPiConj K y⟫ := by
  rw [toEuclidPi, toEuclidPiConj, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.trans_apply, inner_euclidPiEquiv, mixedPairingPi]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [mixedTraceForm_eq_inner]
  rfl

/- English proof (translation)
The claim follows from `(measurePreserving_euclidPiEquiv K).comp (measurePreserving_pi _ _ fun _ ↦ measurePreserving_mixedToEuclidean K)`.
-/
theorem measurePreserving_toEuclidPi :
    MeasurePreserving (toEuclidPi K (ι := ι)) (mixedMeasurePi K) volume :=
  (measurePreserving_euclidPiEquiv K).comp
    (measurePreserving_pi _ _ fun _ ↦ measurePreserving_mixedToEuclidean K)

/- English proof (translation)
The claim follows from `(measurePreserving_euclidPiEquiv K).comp (measurePreserving_pi _ _ fun _ ↦ measurePreserving_mixedToEuclideanConj K)`.
-/
theorem measurePreserving_toEuclidPiConj :
    MeasurePreserving (toEuclidPiConj K (ι := ι)) (mixedMeasurePi K) volume :=
  (measurePreserving_euclidPiEquiv K).comp
    (measurePreserving_pi _ _ fun _ ↦ measurePreserving_mixedToEuclideanConj K)

/- English proof (translation)
Establish `: MeasurePreserving (toEuclidPi K (ι` using `ι)).toHomeomorph.toMeasurableEquiv (mixedMeasurePi K) volume := measurePreserving_toEuclidPi K`. Conclude with `this.symm`.
-/
theorem measurePreserving_toEuclidPi_symm :
    MeasurePreserving (toEuclidPi K (ι := ι)).symm volume (mixedMeasurePi K) := by
  have : MeasurePreserving (toEuclidPi K (ι := ι)).toHomeomorph.toMeasurableEquiv
      (mixedMeasurePi K) volume := measurePreserving_toEuclidPi K
  exact this.symm

def mixedFourierPi (f : (ι → mixedSpace K) → ℂ) (y : ι → mixedSpace K) : ℂ :=
  ∫ x, 𝐞 (-mixedPairingPi K x y) • f x ∂mixedMeasurePi K

def mixedFourierInvPi (f : (ι → mixedSpace K) → ℂ) (x : ι → mixedSpace K) : ℂ :=
  ∫ y, 𝐞 (mixedPairingPi K x y) • f y ∂mixedMeasurePi K

/- English proof (translation)
Rewrite using `[mixedFourierPi, Real.fourier_eq, ← (measurePreserving_toEuclidPi K).integral_comp (toEuclidPi K).toHomeomorph.measurableEmbedding]`. Use `integral_congr_ae (Eventually.of_forall fun x ↦ ?_)` and prove the remaining obligations. Simplify using `[mixedPairingPi_eq_inner]`.
-/
theorem mixedFourierPi_eq (f : (ι → mixedSpace K) → ℂ) (y : ι → mixedSpace K) :
    mixedFourierPi K f y = 𝓕 (f ∘ (toEuclidPi K).symm) (toEuclidPiConj K y) := by
  rw [mixedFourierPi, Real.fourier_eq, ← (measurePreserving_toEuclidPi K).integral_comp
    (toEuclidPi K).toHomeomorph.measurableEmbedding]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp [mixedPairingPi_eq_inner]

/- English proof (translation)
Rewrite using `[mixedFourierInvPi, Real.fourierInv_eq, ← (measurePreserving_toEuclidPiConj K).integral_comp (toEuclidPiConj K).toHomeomorph.measurableEmbedding]`. Use `integral_congr_ae (Eventually.of_forall fun y ↦ ?_)` and prove the remaining obligations. Simplify using `only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]`. Rewrite using `[mixedPairingPi_eq_inner, real_inner_comm]`.
-/
theorem mixedFourierInvPi_eq (f : (ι → mixedSpace K) → ℂ) (x : ι → mixedSpace K) :
    mixedFourierInvPi K f x = 𝓕⁻ (f ∘ (toEuclidPiConj K).symm) (toEuclidPi K x) := by
  rw [mixedFourierInvPi, Real.fourierInv_eq, ← (measurePreserving_toEuclidPiConj K).integral_comp
    (toEuclidPiConj K).toHomeomorph.measurableEmbedding]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
  rw [mixedPairingPi_eq_inner, real_inner_comm]

def mixedFourierPiSchwartz : 𝓢(ι → mixedSpace K, ℂ) →L[ℂ] 𝓢(ι → mixedSpace K, ℂ) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (toEuclidPiConj K)).comp
    ((SchwartzMap.fourierTransformCLM ℂ).comp
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (toEuclidPi K).symm))

/- English proof (translation)
Use function extensionality and compare the values at `y`. Rewrite using `[mixedFourierPi_eq]`. Both sides reduce to the same expression.
-/
theorem mixedFourierPiSchwartz_apply (f : 𝓢(ι → mixedSpace K, ℂ)) :
    ⇑(mixedFourierPiSchwartz K f) = mixedFourierPi K f := by
  funext y
  rw [mixedFourierPi_eq]
  rfl

/- English proof (translation)
Use `set F : 𝓢(EuclidPi K ι, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (toEuclidPi K).symm f with hFdef`. Establish `hF : (F : EuclidPi K ι → ℂ) = f ∘ (toEuclidPi K).symm` using `rfl`. Establish `h1 : mixedFourierPi K f ∘ (toEuclidPiConj K).symm = 𝓕 (F : EuclidPi K ι → ℂ)`. Use function extensionality and compare the values at `v`. Rewrite using `[Function.comp_apply, mixedFourierPi_eq, ContinuousLinearEquiv.apply_symm_apply, hF]`.

Establish `h2 : Integrable (𝓕 (F : EuclidPi K ι → ℂ))`. Rewrite using `[← SchwartzMap.fourier_coe]`. Conclude with `(𝓕 F).integrable`. Rewrite using `[mixedFourierInvPi_eq, h1, F.continuous.fourierInv_fourier_eq F.integrable h2, hF, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]`.
-/
theorem mixedFourierInvPi_mixedFourierPi (f : 𝓢(ι → mixedSpace K, ℂ))
    (x : ι → mixedSpace K) : mixedFourierInvPi K (mixedFourierPi K f) x = f x := by
  set F : 𝓢(EuclidPi K ι, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (toEuclidPi K).symm f
    with hFdef
  have hF : (F : EuclidPi K ι → ℂ) = f ∘ (toEuclidPi K).symm := rfl
  have h1 : mixedFourierPi K f ∘ (toEuclidPiConj K).symm = 𝓕 (F : EuclidPi K ι → ℂ) := by
    funext v
    rw [Function.comp_apply, mixedFourierPi_eq, ContinuousLinearEquiv.apply_symm_apply, hF]
  have h2 : Integrable (𝓕 (F : EuclidPi K ι → ℂ)) := by
    rw [← SchwartzMap.fourier_coe]
    exact (𝓕 F).integrable
  rw [mixedFourierInvPi_eq, h1, F.continuous.fourierInv_fourier_eq F.integrable h2, hF,
    Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]

/- English proof (translation)
Rewrite using `[mixedFourierPi, mixedFourierInvPi]`. Use `integral_congr_ae (Eventually.of_forall fun y ↦ ?_)` and prove the remaining obligations. Simplify using `only`. Rewrite using `[mixedPairingPi_neg_right, neg_neg, mixedPairingPi_comm]`.
-/
theorem mixedFourierPi_neg (f : (ι → mixedSpace K) → ℂ) (x : ι → mixedSpace K) :
    mixedFourierPi K f (-x) = mixedFourierInvPi K f x := by
  rw [mixedFourierPi, mixedFourierInvPi]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  dsimp only
  rw [mixedPairingPi_neg_right, neg_neg, mixedPairingPi_comm]

/- English proof (translation)
Rewrite using `[← neg_neg x, mixedFourierPi_neg, mixedFourierInvPi_mixedFourierPi, neg_neg]`.
-/
theorem mixedFourierPi_mixedFourierPi (f : 𝓢(ι → mixedSpace K, ℂ))
    (x : ι → mixedSpace K) : mixedFourierPi K (mixedFourierPi K f) x = f (-x) := by
  rw [← neg_neg x, mixedFourierPi_neg, mixedFourierInvPi_mixedFourierPi, neg_neg]

variable {K}

def idealLatticePi (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Submodule ℤ (ι → mixedSpace K) :=
  Submodule.pi Set.univ fun i ↦ idealLattice K (I i)

omit [Fintype ι] in
/- English proof (translation)
Simplify using `[idealLatticePi, Submodule.mem_pi]`.
-/
theorem mem_idealLatticePi {I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ} {x : ι → mixedSpace K} :
    x ∈ idealLatticePi I ↔ ∀ i, x i ∈ idealLattice K (I i) := by
  simp [idealLatticePi, Submodule.mem_pi]

instance (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) : DiscreteTopology (idealLatticePi I) := by
  let f : idealLatticePi I → ∀ i, idealLattice K (I i) :=
    fun x i ↦ ⟨x.1 i, mem_idealLatticePi.mp x.2 i⟩
  have hc : Continuous f := continuous_pi fun i ↦
    ((continuous_apply i).comp continuous_subtype_val).subtype_mk _
  have hi : Function.Injective f := fun x y h ↦
    Subtype.ext (funext fun i ↦ congrArg Subtype.val (congrFun h i))
  exact DiscreteTopology.of_continuous_injective hc hi

instance (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) : IsZLattice ℝ (idealLatticePi I) where
  span_top := by
    rw [eq_top_iff]
    rintro x -
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    have hsp : x i ∈ Submodule.span ℝ (idealLattice K (I i) : Set (mixedSpace K)) := by
      rw [IsZLattice.span_top]
      trivial
    have hmap : Pi.single i (x i) ∈
        (Submodule.span ℝ (idealLattice K (I i) : Set (mixedSpace K))).map
          (LinearMap.single ℝ (fun _ : ι ↦ mixedSpace K) i) := ⟨x i, hsp, rfl⟩
    rw [← Submodule.span_image] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, mem_idealLatticePi]
    intro j
    by_cases hj : j = i
    · subst hj
      simpa using hy
    · simp [Pi.single_eq_of_ne hj]

/- English proof (translation)
Use `set b := fun i ↦ (Module.Free.chooseBasis ℤ (idealLattice K (I i))).ofZLatticeBasis ℝ (idealLattice K (I i))`. Establish `hspan : ∀ i, Submodule.span ℤ (Set.range (b i)) = idealLattice K (I i)` using `fun i ↦ (Module.Free.chooseBasis ℤ (idealLattice K (I i))).ofZLatticeBasis_span ℝ _`. Use `IsAddFundamentalDomain.mk' (MeasurableSet.univ_pi fun i ↦ ZSpan.fundamentalDomain_measurableSet _).nullMeasurableSet fun x ↦ ?_` and prove the remaining obligations. Establish `h` using `fun i ↦ ZSpan.exist_unique_vadd_mem_fundamentalDomain (b i) (x i)`. Use `choose v hv hvu using h`.

Establish `hvmem : ∀ i, (v i : mixedSpace K) ∈ idealLattice K (I i)` using `fun i ↦ by`. Establish `key : ∀ z ∈ Submodule.span ℤ (Set.range (b i)), z ∈ idealLattice K (I i)` using `fun z hz ↦ hspan i ▸ hz`. Conclude with `key _ (v i).2`. Use `⟨⟨fun i ↦ (v i : mixedSpace K), mem_idealLatticePi.mpr hvmem⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `i _`.

Conclude with `hv i`. Introduce and unpack `g hg`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Establish `hgi : (g : ι → mixedSpace K) i ∈ Submodule.span ℤ (Set.range (b i))`.

Rewrite using `[hspan i]`. Conclude with `mem_idealLatticePi.mp g.2 i`. Use `hvu i ⟨_, hgi⟩ (hg i trivial)` as an intermediate fact. Conclude with `congrArg Subtype.val this`.
-/
theorem isAddFundamentalDomain_idealLatticePi (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    IsAddFundamentalDomain (idealLatticePi I)
      (Set.univ.pi fun i ↦ ZSpan.fundamentalDomain
        ((Module.Free.chooseBasis ℤ (idealLattice K (I i))).ofZLatticeBasis ℝ
          (idealLattice K (I i)))) (mixedMeasurePi K) := by
  set b := fun i ↦ (Module.Free.chooseBasis ℤ (idealLattice K (I i))).ofZLatticeBasis ℝ
    (idealLattice K (I i))
  have hspan : ∀ i, Submodule.span ℤ (Set.range (b i)) = idealLattice K (I i) := fun i ↦
    (Module.Free.chooseBasis ℤ (idealLattice K (I i))).ofZLatticeBasis_span ℝ _
  refine IsAddFundamentalDomain.mk'
    (MeasurableSet.univ_pi fun i ↦ ZSpan.fundamentalDomain_measurableSet _).nullMeasurableSet
    fun x ↦ ?_
  have h := fun i ↦ ZSpan.exist_unique_vadd_mem_fundamentalDomain (b i) (x i)
  choose v hv hvu using h
  have hvmem : ∀ i, (v i : mixedSpace K) ∈ idealLattice K (I i) := fun i ↦ by
    have key : ∀ z ∈ Submodule.span ℤ (Set.range (b i)), z ∈ idealLattice K (I i) :=
      fun z hz ↦ hspan i ▸ hz
    exact key _ (v i).2
  refine ⟨⟨fun i ↦ (v i : mixedSpace K), mem_idealLatticePi.mpr hvmem⟩, ?_, ?_⟩
  · intro i _
    exact hv i
  · rintro g hg
    apply Subtype.ext
    funext i
    have hgi : (g : ι → mixedSpace K) i ∈ Submodule.span ℤ (Set.range (b i)) := by
      rw [hspan i]
      exact mem_idealLatticePi.mp g.2 i
    have := hvu i ⟨_, hgi⟩ (hg i trivial)
    exact congrArg Subtype.val this

/- English proof (translation)
Rewrite using `[ZLattice.covolume_eq_measure_fundamentalDomain _ _ (isAddFundamentalDomain_idealLatticePi I), measureReal_def, mixedMeasurePi, Measure.pi_pi, ENNReal.toReal_prod]`. Use `Finset.prod_congr rfl fun i _ ↦ ?_` and prove the remaining obligations. Rewrite using `[← covolume_idealLattice_selfDualMeasure, ZLattice.covolume_eq_measure_fundamentalDomain _ _ (ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ (idealLattice K (I i))) _), measureReal_def]`.
-/
theorem covolume_idealLatticePi (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (idealLatticePi I) (mixedMeasurePi K) =
      ∏ i, ((FractionalIdeal.absNorm (I i : FractionalIdeal (𝓞 K)⁰ K) : ℝ) * √|(discr K : ℝ)|) := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ (isAddFundamentalDomain_idealLatticePi I),
    measureReal_def, mixedMeasurePi, Measure.pi_pi, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [← covolume_idealLattice_selfDualMeasure, ZLattice.covolume_eq_measure_fundamentalDomain _ _
    (ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ (idealLattice K (I i))) _),
    measureReal_def]

abbrev euclidLatticePi (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Submodule ℤ (EuclidPi K ι) :=
  ZLattice.comap ℝ (idealLatticePi I) (toEuclidPi K).symm.toLinearMap

abbrev euclidConjLatticePi (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Submodule ℤ (EuclidPi K ι) :=
  ZLattice.comap ℝ (idealLatticePi I) (toEuclidPiConj K).symm.toLinearMap

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_euclidLatticePi (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (u : EuclidPi K ι) :
    u ∈ euclidLatticePi I ↔ (toEuclidPi K).symm u ∈ idealLatticePi I := Iff.rfl

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_euclidConjLatticePi (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (u : EuclidPi K ι) :
    u ∈ euclidConjLatticePi I ↔ (toEuclidPiConj K).symm u ∈ idealLatticePi I := Iff.rfl

/- English proof (translation)
Rewrite using `[ZLattice.covolume_comap (idealLatticePi I) (mixedMeasurePi K) volume (measurePreserving_toEuclidPi_symm K), covolume_idealLatticePi]`.
-/
theorem covolume_euclidLatticePi (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (euclidLatticePi I) =
      ∏ i, ((FractionalIdeal.absNorm (I i : FractionalIdeal (𝓞 K)⁰ K) : ℝ) * √|(discr K : ℝ)|) := by
  rw [ZLattice.covolume_comap (idealLatticePi I) (mixedMeasurePi K) volume
    (measurePreserving_toEuclidPi_symm K), covolume_idealLatticePi]

/- English proof (translation)
Rewrite using `[mixedPairingPi, Finset.sum_eq_single i (fun j _ hj ↦ by simp [Pi.single_eq_of_ne hj]) (by simp), Pi.single_eq_same]`.
-/
theorem mixedPairingPi_single_left (i : ι) (x : mixedSpace K) (y : ι → mixedSpace K) :
    mixedPairingPi K (Pi.single i x) y = mixedTraceForm K x (y i) := by
  rw [mixedPairingPi, Finset.sum_eq_single i (fun j _ hj ↦ by simp [Pi.single_eq_of_ne hj])
    (by simp), Pi.single_eq_same]

/- English proof (translation)
Use extensionality with `μ`. Rewrite using `[mem_dualLattice, mem_euclidConjLatticePi, mem_idealLatticePi]`. Use `set y := (toEuclidPiConj K).symm μ with hy`. Establish `hμ : μ = toEuclidPiConj K y` using `by rw [hy, ContinuousLinearEquiv.apply_symm_apply]`. Prove the components needed by the constructor for the conclusion.

Introduce `h i`. Rewrite using `[mem_idealLattice_traceDualIdeal_iff]`. Introduce `x hx`. Establish `hmem : toEuclidPi K (Pi.single i x) ∈ euclidLatticePi I`. Rewrite using `[mem_euclidLatticePi, ContinuousLinearEquiv.symm_apply_apply, mem_idealLatticePi]`.

Introduce `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `using hx`. Simplify using `[Pi.single_eq_of_ne hj]`.

Take `⟨k, hk⟩` from `h _ hmem`. Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite `hk` using `[hμ, real_inner_comm, ← mixedPairingPi_eq_inner, mixedPairingPi_single_left]`. Rewrite using `[mixedTraceForm_comm]`. Conclude with `hk`.

Introduce `h ℓ hℓ`. Rewrite `hℓ` using `[mem_euclidLatticePi, mem_idealLatticePi]`. Establish `hk : ∀ i, ∃ n : ℤ, mixedTraceForm K (y i) (((toEuclidPi K).symm ℓ) i) = n` using `fun i ↦ (mem_idealLattice_traceDualIdeal_iff K (I i) (y i)).mp (h i) _ (hℓ i)`. Use `choose n hn using hk`. Use `⟨∑ i, n i, ?_⟩` and prove the remaining obligations.

Establish `hℓ' : ℓ = toEuclidPi K ((toEuclidPi K).symm ℓ)`. Rewrite using `[ContinuousLinearEquiv.apply_symm_apply]`. Rewrite using `[hμ, hℓ', real_inner_comm, ← mixedPairingPi_eq_inner, mixedPairingPi]`. Use `push_cast`. Use `Finset.sum_congr rfl fun i _ ↦ ?_` and prove the remaining obligations.

Rewrite using `[mixedTraceForm_comm, hn i]`.
-/
theorem dualLattice_euclidLatticePi (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    dualLattice (euclidLatticePi I) = euclidConjLatticePi (fun i ↦ traceDualIdeal K (I i)) := by
  ext μ
  rw [mem_dualLattice, mem_euclidConjLatticePi, mem_idealLatticePi]
  set y := (toEuclidPiConj K).symm μ with hy
  have hμ : μ = toEuclidPiConj K y := by rw [hy, ContinuousLinearEquiv.apply_symm_apply]
  constructor
  · intro h i
    rw [mem_idealLattice_traceDualIdeal_iff]
    intro x hx
    have hmem : toEuclidPi K (Pi.single i x) ∈ euclidLatticePi I := by
      rw [mem_euclidLatticePi, ContinuousLinearEquiv.symm_apply_apply, mem_idealLatticePi]
      intro j
      by_cases hj : j = i
      · subst hj
        simpa using hx
      · simp [Pi.single_eq_of_ne hj]
    obtain ⟨k, hk⟩ := h _ hmem
    refine ⟨k, ?_⟩
    rw [hμ, real_inner_comm, ← mixedPairingPi_eq_inner, mixedPairingPi_single_left] at hk
    rw [mixedTraceForm_comm]
    exact hk
  · intro h ℓ hℓ
    rw [mem_euclidLatticePi, mem_idealLatticePi] at hℓ
    have hk : ∀ i, ∃ n : ℤ, mixedTraceForm K (y i) (((toEuclidPi K).symm ℓ) i) = n := fun i ↦
      (mem_idealLattice_traceDualIdeal_iff K (I i) (y i)).mp (h i) _ (hℓ i)
    choose n hn using hk
    refine ⟨∑ i, n i, ?_⟩
    have hℓ' : ℓ = toEuclidPi K ((toEuclidPi K).symm ℓ) := by
      rw [ContinuousLinearEquiv.apply_symm_apply]
    rw [hμ, hℓ', real_inner_comm, ← mixedPairingPi_eq_inner, mixedPairingPi]
    push_cast
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [mixedTraceForm_comm, hn i]

/- English proof (translation)
Simplify `summable_norm_comp_add (idealLatticePi I) f a` using `[add_comm]`.
-/
theorem idealLatticePi_summable_norm (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (f : 𝓢(ι → mixedSpace K, ℂ)) (a : ι → mixedSpace K) :
    Summable fun α : idealLatticePi I ↦ ‖f (α + a)‖ := by
  simpa [add_comm] using summable_norm_comp_add (idealLatticePi I) f a

/- English proof (translation)
Establish `h` using `summable_norm_comp_add (idealLatticePi (fun i ↦ traceDualIdeal K (I i))) (mixedFourierPiSchwartz K f) 0`. Simplify using `only [zero_add, mixedFourierPiSchwartz_apply] at h`. Simplify `h` using `only [norm_mul, Circle.norm_coe, mul_one]`.
-/
theorem dualIdealLatticePi_summable_norm (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (f : 𝓢(ι → mixedSpace K, ℂ)) (a : ι → mixedSpace K) :
    Summable fun β : idealLatticePi (fun i ↦ traceDualIdeal K (I i)) ↦
      ‖mixedFourierPi K f β * 𝐞 (mixedPairingPi K β a)‖ := by
  have h := summable_norm_comp_add (idealLatticePi (fun i ↦ traceDualIdeal K (I i)))
    (mixedFourierPiSchwartz K f) 0
  simp only [zero_add, mixedFourierPiSchwartz_apply] at h
  simpa only [norm_mul, Circle.norm_coe, mul_one] using h

/- English proof (translation)
Use `set L := euclidLatticePi I`. Use `set F : 𝓢(EuclidPi K ι, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (toEuclidPi K).symm f`. Establish `hF : (F : EuclidPi K ι → ℂ) = f ∘ (toEuclidPi K).symm` using `rfl`. Establish `hFx : ∀ x, F x = f ((toEuclidPi K).symm x)` using `fun x ↦ congrFun hF x`. Establish `h` using `lattice_poisson_summation L F (toEuclidPi K a)`.

Set `eL : idealLatticePi I ≃ L` to `{ toFun := fun α ↦ ⟨toEuclidPi K α, by`. Rewrite using `[mem_euclidLatticePi, ContinuousLinearEquiv.symm_apply_apply]`. Conclude with `α.2⟩`. Use `invFun := fun ℓ ↦ ⟨(toEuclidPi K).symm ℓ, ℓ.2⟩`. Use `left_inv := fun α ↦ Subtype.ext (ContinuousLinearEquiv.symm_apply_apply _ _)`.

Use `right_inv := fun ℓ ↦ Subtype.ext (ContinuousLinearEquiv.apply_symm_apply _ _) }`. Set `eD : idealLatticePi (fun i ↦ traceDualIdeal K (I i)) ≃ dualLattice L` to `{ toFun := fun β ↦ ⟨toEuclidPiConj K β, by`. Rewrite using `[dualLattice_euclidLatticePi, mem_euclidConjLatticePi, ContinuousLinearEquiv.symm_apply_apply]`. Conclude with `β.2⟩`. Use `invFun := fun μ ↦ ⟨(toEuclidPiConj K).symm μ, by`.

Establish `hμ : (μ : EuclidPi K ι) ∈ euclidConjLatticePi (fun i ↦ traceDualIdeal K (I i))`. Rewrite using `[← dualLattice_euclidLatticePi]`. Conclude with `μ.2`. Conclude with `hμ⟩`. Use `left_inv := fun β ↦ Subtype.ext (ContinuousLinearEquiv.symm_apply_apply _ _)`.

Use `right_inv := fun μ ↦ Subtype.ext (ContinuousLinearEquiv.apply_symm_apply _ _) }`. Establish `hlhs : ∑' ℓ : L, F (ℓ + toEuclidPi K a) = ∑' α : idealLatticePi I, f (α + a)`. Rewrite using `[← Equiv.tsum_eq eL]`. Use `tsum_congr fun α ↦ ?_` and prove the remaining obligations. Establish `heL : (eL α : EuclidPi K ι) = toEuclidPi K α` using `rfl`.

Rewrite using `[heL, hFx, ← map_add, ContinuousLinearEquiv.symm_apply_apply]`. Establish `hrhs : ∑' μ : dualLattice L, 𝓕 (F : EuclidPi K ι → ℂ) μ * 𝐞 ⟪(μ : EuclidPi K ι), toEuclidPi K a⟫ = ∑' β : idealLatticePi (fun i ↦ traceDualIdeal K (I i)), mixedFourierPi K f β * 𝐞 (mixedPairingPi K β a)`. Rewrite using `[← Equiv.tsum_eq eD]`. Use `tsum_congr fun β ↦ ?_` and prove the remaining obligations. Establish `heD : (eD β : EuclidPi K ι) = toEuclidPiConj K β` using `rfl`.

Rewrite using `[heD, hF, ← mixedFourierPi_eq, real_inner_comm, ← mixedPairingPi_eq_inner, mixedPairingPi_comm]`. Rewrite `h` using `[hlhs, hrhs, covolume_euclidLatticePi]`. Conclude with `h`.
-/
theorem idealLatticePi_poisson_summation (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (f : 𝓢(ι → mixedSpace K, ℂ)) (a : ι → mixedSpace K) :
    ∑' α : idealLatticePi I, f (α + a) =
      (∏ i, ((FractionalIdeal.absNorm (I i : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
        √|(discr K : ℝ)|))⁻¹ •
        ∑' β : idealLatticePi (fun i ↦ traceDualIdeal K (I i)),
          mixedFourierPi K f β * 𝐞 (mixedPairingPi K β a) := by
  set L := euclidLatticePi I
  set F : 𝓢(EuclidPi K ι, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (toEuclidPi K).symm f
  have hF : (F : EuclidPi K ι → ℂ) = f ∘ (toEuclidPi K).symm := rfl
  have hFx : ∀ x, F x = f ((toEuclidPi K).symm x) := fun x ↦ congrFun hF x
  have h := lattice_poisson_summation L F (toEuclidPi K a)
  let eL : idealLatticePi I ≃ L :=
    { toFun := fun α ↦ ⟨toEuclidPi K α, by
        rw [mem_euclidLatticePi, ContinuousLinearEquiv.symm_apply_apply]; exact α.2⟩
      invFun := fun ℓ ↦ ⟨(toEuclidPi K).symm ℓ, ℓ.2⟩
      left_inv := fun α ↦ Subtype.ext (ContinuousLinearEquiv.symm_apply_apply _ _)
      right_inv := fun ℓ ↦ Subtype.ext (ContinuousLinearEquiv.apply_symm_apply _ _) }
  let eD : idealLatticePi (fun i ↦ traceDualIdeal K (I i)) ≃ dualLattice L :=
    { toFun := fun β ↦ ⟨toEuclidPiConj K β, by
        rw [dualLattice_euclidLatticePi, mem_euclidConjLatticePi,
          ContinuousLinearEquiv.symm_apply_apply]; exact β.2⟩
      invFun := fun μ ↦ ⟨(toEuclidPiConj K).symm μ, by
        have hμ : (μ : EuclidPi K ι) ∈ euclidConjLatticePi (fun i ↦ traceDualIdeal K (I i)) := by
          rw [← dualLattice_euclidLatticePi]
          exact μ.2
        exact hμ⟩
      left_inv := fun β ↦ Subtype.ext (ContinuousLinearEquiv.symm_apply_apply _ _)
      right_inv := fun μ ↦ Subtype.ext (ContinuousLinearEquiv.apply_symm_apply _ _) }
  have hlhs : ∑' ℓ : L, F (ℓ + toEuclidPi K a) = ∑' α : idealLatticePi I, f (α + a) := by
    rw [← Equiv.tsum_eq eL]
    refine tsum_congr fun α ↦ ?_
    have heL : (eL α : EuclidPi K ι) = toEuclidPi K α := rfl
    rw [heL, hFx, ← map_add, ContinuousLinearEquiv.symm_apply_apply]
  have hrhs : ∑' μ : dualLattice L,
      𝓕 (F : EuclidPi K ι → ℂ) μ * 𝐞 ⟪(μ : EuclidPi K ι), toEuclidPi K a⟫ =
      ∑' β : idealLatticePi (fun i ↦ traceDualIdeal K (I i)),
        mixedFourierPi K f β * 𝐞 (mixedPairingPi K β a) := by
    rw [← Equiv.tsum_eq eD]
    refine tsum_congr fun β ↦ ?_
    have heD : (eD β : EuclidPi K ι) = toEuclidPiConj K β := rfl
    rw [heD, hF, ← mixedFourierPi_eq, real_inner_comm, ← mixedPairingPi_eq_inner, mixedPairingPi_comm]
  rw [hlhs, hrhs, covolume_euclidLatticePi] at h
  exact h

variable (K) in

def embPi (ξ : ι → K) : ι → mixedSpace K := fun i ↦ mixedEmbedding K (ξ i)

variable (K) in

def cosetPi (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (c : ι → K) : Set (ι → K) :=
  {ξ | ∀ i, ξ i - c i ∈ (I i : FractionalIdeal (𝓞 K)⁰ K)}

omit [NumberField K] [Fintype ι] in
/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[embPi]`.
-/
theorem embPi_zero : embPi K (0 : ι → K) = 0 := by
  funext i
  simp [embPi]

omit [Fintype ι] in

/- English proof (translation)
Establish `hpre : ∀ α : idealLatticePi I, ∀ i, ∃ y ∈ ((I i : FractionalIdeal (𝓞 K)⁰ K) : Set K), mixedEmbedding K y = (α : ι → mixedSpace K) i` using `fun α i ↦ (mem_idealLattice K (I i)).mp (mem_idealLatticePi.mp α.2 i)`. Use `choose y hyI hy using hpre`. Use `set h : idealLatticePi I → ι → K := fun α i ↦ c i + y α i with hh`. Establish `hinj : Function.Injective h`. Introduce `α β hαβ`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Establish `h1 : y α i = y β i` using `add_left_cancel (congrFun hαβ i)`. Rewrite using `[← hy α i, ← hy β i, h1]`. Establish `hmem : ∀ α, h α ∈ cosetPi K I c` using `fun α i ↦ by`.

Simplify using `only [hh, add_sub_cancel_left]`. Conclude with `hyI α i`. Establish `hemb : ∀ α, embPi K (h α) = (α : ι → mixedSpace K) + embPi K c`. Introduce `α`. Use function extensionality and compare the values at `i`.

Simplify using `only [embPi, hh, Pi.add_apply, map_add, hy α i, add_comm]`. Use `set G : (ι → K) → ℂ := (cosetPi K I c).indicator (fun ξ ↦ g (embPi K ξ))`. Establish `hsupp : ∀ ξ ∉ Set.range h, G ξ = 0`. Introduce `ξ hξ`. Use `Set.indicator_of_notMem (fun hm ↦ hξ ?_) _` and prove the remaining obligations.

Establish `hα : embPi K (fun i ↦ ξ i - c i) ∈ idealLatticePi I`. Rewrite using `[mem_idealLatticePi]`. Introduce `i`. Conclude with `(mem_idealLattice K (I i)).mpr ⟨ξ i - c i, hm i, rfl⟩`. Use `⟨⟨_, hα⟩, funext fun i ↦ ?_⟩` and prove the remaining obligations.

Establish `h2 : mixedEmbedding K (y ⟨_, hα⟩ i) = mixedEmbedding K (ξ i - c i)` using `hy _ i`. Establish `h3` using `mixedEmbedding_injective K h2`. Simplify using `only [hh, h3]`. Expand and normalize the polynomial expressions, which then agree. Establish `hGh : ∀ α, G (h α) = g (α + embPi K c)`.

Introduce `α`. Simplify using `only [G]`. Rewrite using `[Set.indicator_of_mem (hmem α), hemb]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hinj.summable_iff (f := fun ξ ↦ ‖G ξ‖) (fun ξ hξ ↦ by simp [hsupp ξ hξ])]`.

Simplify using `only [Function.comp_def, hGh]`. Rewrite using `[← hinj.tsum_eq (fun ξ hξ ↦ by_contra fun hn ↦ hξ (hsupp ξ hn))]`. Simplify using `only [hGh]`.
-/
theorem summable_norm_iff_and_tsum_eq_cosetPi (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (c : ι → K) (g : (ι → mixedSpace K) → ℂ) :
    (Summable (fun ξ ↦ ‖(cosetPi K I c).indicator (fun ξ ↦ g (embPi K ξ)) ξ‖) ↔
      Summable (fun α : idealLatticePi I ↦ ‖g (α + embPi K c)‖)) ∧
      ∑' ξ, (cosetPi K I c).indicator (fun ξ ↦ g (embPi K ξ)) ξ =
        ∑' α : idealLatticePi I, g (α + embPi K c) := by
  have hpre : ∀ α : idealLatticePi I, ∀ i, ∃ y ∈ ((I i : FractionalIdeal (𝓞 K)⁰ K) : Set K),
      mixedEmbedding K y = (α : ι → mixedSpace K) i := fun α i ↦
    (mem_idealLattice K (I i)).mp (mem_idealLatticePi.mp α.2 i)
  choose y hyI hy using hpre
  set h : idealLatticePi I → ι → K := fun α i ↦ c i + y α i with hh
  have hinj : Function.Injective h := by
    intro α β hαβ
    apply Subtype.ext
    funext i
    have h1 : y α i = y β i := add_left_cancel (congrFun hαβ i)
    rw [← hy α i, ← hy β i, h1]
  have hmem : ∀ α, h α ∈ cosetPi K I c := fun α i ↦ by
    simp only [hh, add_sub_cancel_left]
    exact hyI α i
  have hemb : ∀ α, embPi K (h α) = (α : ι → mixedSpace K) + embPi K c := by
    intro α
    funext i
    simp only [embPi, hh, Pi.add_apply, map_add, hy α i, add_comm]
  set G : (ι → K) → ℂ := (cosetPi K I c).indicator (fun ξ ↦ g (embPi K ξ))
  have hsupp : ∀ ξ ∉ Set.range h, G ξ = 0 := by
    intro ξ hξ
    refine Set.indicator_of_notMem (fun hm ↦ hξ ?_) _
    have hα : embPi K (fun i ↦ ξ i - c i) ∈ idealLatticePi I := by
      rw [mem_idealLatticePi]
      intro i
      exact (mem_idealLattice K (I i)).mpr ⟨ξ i - c i, hm i, rfl⟩
    refine ⟨⟨_, hα⟩, funext fun i ↦ ?_⟩
    have h2 : mixedEmbedding K (y ⟨_, hα⟩ i) = mixedEmbedding K (ξ i - c i) := hy _ i
    have h3 := mixedEmbedding_injective K h2
    simp only [hh, h3]
    ring
  have hGh : ∀ α, G (h α) = g (α + embPi K c) := by
    intro α
    simp only [G]
    rw [Set.indicator_of_mem (hmem α), hemb]
  refine ⟨?_, ?_⟩
  · rw [← hinj.summable_iff (f := fun ξ ↦ ‖G ξ‖) (fun ξ hξ ↦ by simp [hsupp ξ hξ])]
    simp only [Function.comp_def, hGh]
  · rw [← hinj.tsum_eq (fun ξ hξ ↦ by_contra fun hn ↦ hξ (hsupp ξ hn))]
    simp only [hGh]

/- English proof (translation)
Establish `hL` using `summable_norm_iff_and_tsum_eq_cosetPi I c f`. Establish `hR` using `summable_norm_iff_and_tsum_eq_cosetPi (fun i ↦ traceDualIdeal K (I i)) 0 (fun v ↦ mixedFourierPi K f v * (𝐞 (mixedPairingPi K v (embPi K c)) : ℂ))`. Simplify using `only [embPi_zero, add_zero] at hR`. Use `⟨hL.1.mpr (idealLatticePi_summable_norm I f (embPi K c)), hR.1.mpr (dualIdealLatticePi_summable_norm I f (embPi K c)), ?_⟩` and prove the remaining obligations. Rewrite using `[hL.2, hR.2, idealLatticePi_poisson_summation, Complex.real_smul]`.
-/
theorem poissonPi_coset (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (c : ι → K)
    (f : 𝓢(ι → mixedSpace K, ℂ)) :
    Summable (fun ξ : ι → K ↦ ‖(cosetPi K I c).indicator (fun ξ ↦ f (embPi K ξ)) ξ‖) ∧
    Summable (fun η : ι → K ↦ ‖(cosetPi K (fun i ↦ traceDualIdeal K (I i)) 0).indicator
      (fun η ↦ mixedFourierPi K f (embPi K η) *
        (𝐞 (mixedPairingPi K (embPi K η) (embPi K c)) : ℂ)) η‖) ∧
    ∑' ξ : ι → K, (cosetPi K I c).indicator (fun ξ ↦ f (embPi K ξ)) ξ =
      (((∏ i, ((FractionalIdeal.absNorm (I i : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
        √|(discr K : ℝ)|))⁻¹ : ℝ) : ℂ) *
        ∑' η : ι → K, (cosetPi K (fun i ↦ traceDualIdeal K (I i)) 0).indicator
          (fun η ↦ mixedFourierPi K f (embPi K η) *
            (𝐞 (mixedPairingPi K (embPi K η) (embPi K c)) : ℂ)) η := by
  have hL := summable_norm_iff_and_tsum_eq_cosetPi I c f
  have hR := summable_norm_iff_and_tsum_eq_cosetPi (fun i ↦ traceDualIdeal K (I i)) 0
    (fun v ↦ mixedFourierPi K f v * (𝐞 (mixedPairingPi K v (embPi K c)) : ℂ))
  simp only [embPi_zero, add_zero] at hR
  refine ⟨hL.1.mpr (idealLatticePi_summable_norm I f (embPi K c)),
    hR.1.mpr (dualIdealLatticePi_summable_norm I f (embPi K c)), ?_⟩
  rw [hL.2, hR.2, idealLatticePi_poisson_summation, Complex.real_smul]

end

end GroundTheory.Automorphic.GJMatrix
