import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.LocFv

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology

/- English proof (translation)
Use `⟨Units.isEmbedding_val₀, ?_⟩` and prove the remaining obligations. Establish `: Set.range (Units.val : Kˣ → K) = {0}ᶜ`. Use extensionality with `x`. Simplify using `only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]`. Conclude with `⟨fun ⟨u, hu⟩ => hu ▸ u.ne_zero, fun h => ⟨Units.mk0 x h, rfl⟩⟩`.

Rewrite using `[this]`. Conclude with `isOpen_compl_singleton`.
-/
theorem isOpenEmbedding_units_val (K : Type) [Field K] [TopologicalSpace K] [ContinuousInv₀ K]
    [ContinuousMul K] [T1Space K] : IsOpenEmbedding (Units.val : Kˣ → K) := by
  refine ⟨Units.isEmbedding_val₀, ?_⟩
  have : Set.range (Units.val : Kˣ → K) = {0}ᶜ := by
    ext x
    simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ⟨fun ⟨u, hu⟩ => hu ▸ u.ne_zero, fun h => ⟨Units.mk0 x h, rfl⟩⟩
  rw [this]
  exact isOpen_compl_singleton

/- English proof (translation)
Establish `hd : HasStrictDerivAt (fun x : K => x ^ 2) (2 : K) 1`. Simplify using `using hasStrictDerivAt_pow 2 (1 : K)`. Establish `hf` using `hd.hasStrictFDerivAt_equiv h2`. Set `e` to `hf.toOpenPartialHomeomorph _`. Establish `he : (e : K → K) = fun x => x ^ 2` using `hf.toOpenPartialHomeomorph_coe`.

Establish `h1 : (1 : K) ∈ e.source` using `hf.mem_toOpenPartialHomeomorph_source`. Take `⟨ε, hε, hball⟩` from `Metric.isOpen_iff.1 e.open_source 1 h1`. Take `⟨r, hr0, hrε, hr1⟩ : ∃ r : ℝ, 0 < r ∧ r < ε ∧ r < 1` from `⟨min (ε / 2) (1 / 2), lt_min (by linarith) (by norm_num), lt_of_le_of_lt (min_le_left _ _) (by linarith), lt_of_le_of_lt (min_le_right _ _) (by norm_num)⟩`. Establish `hsub : Metric.closedBall (1 : K) r ⊆ e.source` using `(Metric.closedBall_subset_ball hrε).trans hball`. Establish `hopen : IsOpen (Metric.closedBall (1 : K) r)` using `IsUltrametricDist.isOpen_closedBall _ hr0.ne'`.

Establish `hnorm : ∀ a ∈ Metric.closedBall (1 : K) r, ‖a‖ = 1`. Introduce `a ha`. Rewrite `ha` using `[mem_closedBall_iff_norm]`. Establish `hlt : ‖a - 1‖ < ‖(1 : K)‖` using `by rw [norm_one]; linarith`. Use `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne` as an intermediate fact.

Rewrite `this` using `[sub_add_cancel, max_eq_right hlt.le, norm_one]`. Conclude with `this`. Set `U : Subgroup Kˣ` to `{ carrier := Units.val ⁻¹' Metric.closedBall (1 : K) r one_mem' := by simp [hr0.le] mul_mem' := by`. Introduce `a b ha hb`. Establish `hna` using `hnorm _ ha`.

Simplify using `only [Set.mem_preimage, mem_closedBall_iff_norm, Units.val_mul] at ha hb ⊢`. Establish `: (a : K) * b - 1 = a * (b - 1) + (a - 1)` using `by ring`. Rewrite using `[this]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ha)` and prove the remaining obligations. Rewrite using `[norm_mul, hna, one_mul]` and apply the resulting hypothesis.

Use the proof step `inv_mem' := by`. Introduce `a ha`. Establish `hna` using `hnorm _ ha`. Simplify using `only [Set.mem_preimage, mem_closedBall_iff_norm] at ha ⊢`. Establish `h0 : (a : K) ≠ 0` using `a.ne_zero`.

Establish `: (((a⁻¹ : Kˣ)) : K) - 1 = -((a : K)⁻¹ * (a - 1))`. Rewrite using `[Units.val_inv_eq_inv_val]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, norm_neg, norm_mul, norm_inv, hna, inv_one, one_mul] }` and apply the resulting hypothesis.

Establish `hval` using `isOpenEmbedding_units_val K`. Establish `hU : IsOpen (U : Set Kˣ)` using `hopen.preimage Units.continuous_val`. Establish `e1 : IsOpenEmbedding (fun u : U => ((u : Kˣ) : K))` using `hval.comp hU.isOpenEmbedding_subtypeVal`. Establish `hmem : ∀ u : U, ((u : Kˣ) : K) ∈ e.source` using `fun u => hsub u.2`. Use `⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hval, U, hU, ?_⟩` and prove the remaining obligations.

Use `IsOpenEmbedding.of_comp _ hval ?_` and prove the remaining obligations. Use `IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_` and prove the remaining obligations. Conclude with `Units.continuous_val.comp (continuous_subtype_val.pow 2)`. Introduce `u w h`. Simplify using `only [Function.comp, Units.val_pow_eq_pow_val] at h`.

Use `e1.injective (e.injOn (hmem u) (hmem w) ?_)` and prove the remaining obligations. Rewrite using `[he]`. Conclude with `h`. Introduce `s hs`. Establish `himg : (Units.val ∘ fun u : U => ((u : Kˣ) ^ 2 : Kˣ)) '' s = e '' ((fun u : U => ((u : Kˣ) : K)) '' s)`.

Rewrite using `[he, Set.image_image]`. Simplify using `[Function.comp, Units.val_pow_eq_pow_val]`. Rewrite using `[himg]`. Use `e.isOpen_image_of_subset_source (e1.isOpenMap s hs) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨u, -, rfl⟩`.

Conclude with `hmem u`.
-/
theorem isLocR_of_ultrametric (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
    (h2 : (2 : K) ≠ 0) : IsLocR K := by
  have hd : HasStrictDerivAt (fun x : K => x ^ 2) (2 : K) 1 := by
    simpa using hasStrictDerivAt_pow 2 (1 : K)
  have hf := hd.hasStrictFDerivAt_equiv h2
  let e := hf.toOpenPartialHomeomorph _
  have he : (e : K → K) = fun x => x ^ 2 := hf.toOpenPartialHomeomorph_coe
  have h1 : (1 : K) ∈ e.source := hf.mem_toOpenPartialHomeomorph_source
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 e.open_source 1 h1
  obtain ⟨r, hr0, hrε, hr1⟩ : ∃ r : ℝ, 0 < r ∧ r < ε ∧ r < 1 :=
    ⟨min (ε / 2) (1 / 2), lt_min (by linarith) (by norm_num),
      lt_of_le_of_lt (min_le_left _ _) (by linarith), lt_of_le_of_lt (min_le_right _ _) (by norm_num)⟩
  have hsub : Metric.closedBall (1 : K) r ⊆ e.source :=
    (Metric.closedBall_subset_ball hrε).trans hball
  have hopen : IsOpen (Metric.closedBall (1 : K) r) :=
    IsUltrametricDist.isOpen_closedBall _ hr0.ne'
  have hnorm : ∀ a ∈ Metric.closedBall (1 : K) r, ‖a‖ = 1 := by
    intro a ha
    rw [mem_closedBall_iff_norm] at ha
    have hlt : ‖a - 1‖ < ‖(1 : K)‖ := by rw [norm_one]; linarith
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne
    rw [sub_add_cancel, max_eq_right hlt.le, norm_one] at this
    exact this
  let U : Subgroup Kˣ :=
    { carrier := Units.val ⁻¹' Metric.closedBall (1 : K) r
      one_mem' := by simp [hr0.le]
      mul_mem' := by
        intro a b ha hb
        have hna := hnorm _ ha
        simp only [Set.mem_preimage, mem_closedBall_iff_norm, Units.val_mul] at ha hb ⊢
        have : (a : K) * b - 1 = a * (b - 1) + (a - 1) := by ring
        rw [this]
        refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ha)
        rwa [norm_mul, hna, one_mul]
      inv_mem' := by
        intro a ha
        have hna := hnorm _ ha
        simp only [Set.mem_preimage, mem_closedBall_iff_norm] at ha ⊢
        have h0 : (a : K) ≠ 0 := a.ne_zero
        have : (((a⁻¹ : Kˣ)) : K) - 1 = -((a : K)⁻¹ * (a - 1)) := by
          rw [Units.val_inv_eq_inv_val]; field_simp; ring
        rwa [this, norm_neg, norm_mul, norm_inv, hna, inv_one, one_mul] }
  have hval := isOpenEmbedding_units_val K
  have hU : IsOpen (U : Set Kˣ) := hopen.preimage Units.continuous_val
  have e1 : IsOpenEmbedding (fun u : U => ((u : Kˣ) : K)) := hval.comp hU.isOpenEmbedding_subtypeVal
  have hmem : ∀ u : U, ((u : Kˣ) : K) ∈ e.source := fun u => hsub u.2
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    hval, U, hU, ?_⟩
  refine IsOpenEmbedding.of_comp _ hval ?_
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_
  · exact Units.continuous_val.comp (continuous_subtype_val.pow 2)
  · intro u w h
    simp only [Function.comp, Units.val_pow_eq_pow_val] at h
    refine e1.injective (e.injOn (hmem u) (hmem w) ?_)
    rw [he]; exact h
  · intro s hs
    have himg : (Units.val ∘ fun u : U => ((u : Kˣ) ^ 2 : Kˣ)) '' s =
        e '' ((fun u : U => ((u : Kˣ) : K)) '' s) := by
      rw [he, Set.image_image]
      simp [Function.comp, Units.val_pow_eq_pow_val]
    rw [himg]
    refine e.isOpen_image_of_subset_source (e1.isOpenMap s hs) ?_
    rintro _ ⟨u, -, rfl⟩
    exact hmem u

/- English proof (translation)
Introduce `F _ _ v`. Use `letI : NontriviallyNormedField (v.adicCompletion F) := Valued.toNontriviallyNormedField (v.adicCompletion F) (WithZero (Multiplicative ℤ))`. Use `haveI : IsUltrametricDist (v.adicCompletion F) := inferInstanceAs (@IsUltrametricDist (v.adicCompletion F) (Valued.toNormedField (v.adicCompletion F) (WithZero (Multiplicative ℤ))).toDist)`. Use `haveI : ProperSpace (v.adicCompletion F) := Formalism.BasicNotions.Examples₂.LocF.proper v`. Establish `h2 : (2 : v.adicCompletion F) ≠ 0` using `two_ne_zero`.

Conclude with `isLocR_of_ultrametric (v.adicCompletion F) h2`.
-/
theorem isLocR_Fv : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), IsLocR (Fv F v) := by
  intro F _ _ v
  letI : NontriviallyNormedField (v.adicCompletion F) :=
    Valued.toNontriviallyNormedField (v.adicCompletion F) (WithZero (Multiplicative ℤ))
  haveI : IsUltrametricDist (v.adicCompletion F) :=
    inferInstanceAs (@IsUltrametricDist (v.adicCompletion F)
      (Valued.toNormedField (v.adicCompletion F) (WithZero (Multiplicative ℤ))).toDist)
  haveI : ProperSpace (v.adicCompletion F) := Formalism.BasicNotions.Examples₂.LocF.proper v
  have h2 : (2 : v.adicCompletion F) ≠ 0 := two_ne_zero
  exact isLocR_of_ultrametric (v.adicCompletion F) h2

end GlobalTheory.CompanionTheory.SW.LocFv
