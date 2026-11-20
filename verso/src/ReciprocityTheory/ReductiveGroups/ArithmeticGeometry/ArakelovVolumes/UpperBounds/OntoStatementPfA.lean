import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import ReciprocityTheory.L2DbarEstimates.NormFibrations.Hormander
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.MeasurableSetImageOfIsLocalHomeomorph
import ReciprocityTheory.L2DbarEstimates.LeviForms.EventuallyDifferentiableAtOfContDiffAt

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoA

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Set
open scoped ContDiff ENNReal ComplexConjugate

noncomputable section

variable {n : ℕ} {U : Set (V n)}

def gch (hU : IsOpen U) [Nonempty U] : OpenPartialHomeomorph U (V n) :=
  hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val

/- English proof (translation)
Simplify using `[gch]`.
-/
theorem gch_apply (hU : IsOpen U) [Nonempty U] (x : U) : gch hU x = x.1 := by
  simp [gch]

/- English proof (translation)
Simplify using `[gch]`.
-/
theorem gch_source (hU : IsOpen U) [Nonempty U] : (gch hU).source = univ := by
  simp [gch]

/- English proof (translation)
Simplify using `[gch, Subtype.range_coe]`.
-/
theorem gch_target (hU : IsOpen U) [Nonempty U] : (gch hU).target = U := by
  simp [gch, Subtype.range_coe]

/- English proof (translation)
Introduce `x _` and use `(gch_apply hU x).symm`.
-/
theorem gch_isChart (hU : IsOpen U) [Nonempty U] : IsChart n (Subtype.val : U → V n) (gch hU) :=
  fun x _ => (gch_apply hU x).symm

/- English proof (translation)
Establish `h` using `(gch hU).right_inv (by rw [gch_target]; exact hy)`. Rewrite `h` using `[gch_apply]`. Then use the resulting hypothesis.
-/
theorem gch_symm (hU : IsOpen U) [Nonempty U] {y : V n} (hy : y ∈ U) :
    ((gch hU).symm y : V n) = y := by
  have h := (gch hU).right_inv (by rw [gch_target]; exact hy)
  rwa [gch_apply] at h

/- English proof (translation)
The claim follows from `hU.isOpenEmbedding_subtypeVal.isLocalHomeomorph`.
-/
theorem val_lh (hU : IsOpen U) : IsLocalHomeomorph (Subtype.val : U → V n) :=
  hU.isOpenEmbedding_subtypeVal.isLocalHomeomorph

/- English proof (translation)
Rewrite using `[he (e.map_target hy)]`. Conclude with `e.right_inv hy`.
-/
private theorem coe_symm_apply_of_isChart_val {e : OpenPartialHomeomorph U (V n)}
    (he : IsChart n (Subtype.val : U → V n) e) {y : V n} (hy : y ∈ e.target) :
    ((e.symm y : U) : V n) = y := by
  rw [he (e.map_target hy)]
  exact e.right_inv hy

/- English proof (translation)
Introduce `e he`. Use `(hf.mono ?_).congr ?_` and prove the remaining obligations. Introduce `y hy`. Rewrite using `[← coe_symm_apply_of_isChart_val he hy]`. Conclude with `(e.symm y).2`.

Introduce `y hy`. Simplify using `only [Function.comp_apply]`. Rewrite using `[coe_symm_apply_of_isChart_val he hy]`.
-/
theorem smooth_of (hU : IsOpen U) [Nonempty U] {f : V n → ℂ} (hf : ContDiffOn ℝ ∞ f U) :
    Smooth n (Subtype.val : U → V n) (fun x => f x.1) := by
  intro e he
  refine (hf.mono ?_).congr ?_
  · intro y hy
    rw [← coe_symm_apply_of_isChart_val he hy]
    exact (e.symm y).2
  · intro y hy
    simp only [Function.comp_apply]
    rw [coe_symm_apply_of_isChart_val he hy]

/- English proof (translation)
Establish `h2 : ContDiffOn ℝ ∞ (fun y => (f y : ℂ)) U` using `Complex.ofRealCLM.contDiff.comp_contDiffOn hf`. Conclude with `smooth_of hU h2`.
-/
theorem smoothR_of (hU : IsOpen U) [Nonempty U] {f : V n → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
    SmoothR n (Subtype.val : U → V n) (fun x => f x.1) := by
  have h2 : ContDiffOn ℝ ∞ (fun y => (f y : ℂ)) U := Complex.ofRealCLM.contDiff.comp_contDiffOn hf
  exact smooth_of hU h2

/- English proof (translation)
Establish `hxt : (x : V n) ∈ e.target`. Rewrite using `[he hx]`. Conclude with `e.map_source hx`. Use `filter_upwards [e.open_target.mem_nhds hxt] with y hy`. Simplify using `only [Function.comp_apply, coe_symm_apply_of_isChart_val he hy]`.
-/
private theorem comp_chart_symm_eventuallyEq_of_mem_source {e : OpenPartialHomeomorph U (V n)}
    (he : IsChart n (Subtype.val : U → V n) e) {x : U} (hx : x ∈ e.source) (g : V n → ℂ) :
    ((fun y : U => g y.1) ∘ e.symm) =ᶠ[𝓝 x.1] g := by
  have hxt : (x : V n) ∈ e.target := by
    rw [he hx]
    exact e.map_source hx
  filter_upwards [e.open_target.mem_nhds hxt] with y hy
  simp only [Function.comp_apply, coe_symm_apply_of_isChart_val he hy]

/- English proof (translation)
Establish `h : ∃ e : OpenPartialHomeomorph U (V n), IsChart n (Subtype.val : U → V n) e ∧ x ∈ e.source` using `⟨gch hU, gch_isChart hU, by rw [gch_source]; trivial⟩`. Unfold `db`. Rewrite using `[dif_pos h]`. Conclude with `wdb_congr (comp_chart_symm_eventuallyEq_of_mem_source (Classical.choose_spec h).1 (Classical.choose_spec h).2 G)`.
-/
private theorem db_val_eq_wdb_of_isOpen (hU : IsOpen U) [Nonempty U] (j : Fin n) (G : V n → ℂ) (x : U) :
    db n (Subtype.val : U → V n) j (fun y => G y.1) x = wdb n j G x.1 := by
  have h : ∃ e : OpenPartialHomeomorph U (V n), IsChart n (Subtype.val : U → V n) e ∧
      x ∈ e.source := ⟨gch hU, gch_isChart hU, by rw [gch_source]; trivial⟩
  unfold db
  rw [dif_pos h]
  exact wdb_congr (comp_chart_symm_eventuallyEq_of_mem_source (Classical.choose_spec h).1 (Classical.choose_spec h).2 G)

/- English proof (translation)
Unfold `dbarDot`. Simplify using `only [db_val_eq_wdb_of_isOpen hU]`.
-/
theorem dbarDot_eq (hU : IsOpen U) [Nonempty U] (F0 : V n → ℂ) (x : U) (ξ : Fin n → ℂ) :
    dbarDot n (Subtype.val : U → V n) (fun y => F0 y.1) x ξ = ∑ j, wdb n j F0 x.1 * conj (ξ j) := by
  unfold dbarDot
  simp only [db_val_eq_wdb_of_isOpen hU]

/- English proof (translation)
Establish `h : ∃ e : OpenPartialHomeomorph U (V n), IsChart n (Subtype.val : U → V n) e ∧ x ∈ e.source` using `⟨gch hU, gch_isChart hU, by rw [gch_source]; trivial⟩`. Unfold `d`. Rewrite using `[dif_pos h]`. Conclude with `wd_congr (comp_chart_symm_eventuallyEq_of_mem_source (Classical.choose_spec h).1 (Classical.choose_spec h).2 G)`.
-/
private theorem d_val_eq_wd_of_isOpen (hU : IsOpen U) [Nonempty U] (j : Fin n) (G : V n → ℂ) (x : U) :
    d n (Subtype.val : U → V n) j (fun y => G y.1) x = wd n j G x.1 := by
  have h : ∃ e : OpenPartialHomeomorph U (V n), IsChart n (Subtype.val : U → V n) e ∧
      x ∈ e.source := ⟨gch hU, gch_isChart hU, by rw [gch_source]; trivial⟩
  unfold d
  rw [dif_pos h]
  exact wd_congr (comp_chart_symm_eventuallyEq_of_mem_source (Classical.choose_spec h).1 (Classical.choose_spec h).2 G)

/- English proof (translation)
Establish `hin : ∀ k, db n (Subtype.val : U → V n) k (fun y => ((ph y.1 : ℝ) : ℂ)) = fun y => wdb n k (fun w => (ph w : ℂ)) y.1` using `fun k => funext fun y => db_val_eq_wdb_of_isOpen hU k (fun w => (ph w : ℂ)) y`. Unfold `Levi leviV`. Simplify using `only [hin, d_val_eq_wd_of_isOpen hU]`.
-/
theorem levi_eq (hU : IsOpen U) [Nonempty U] (ph : V n → ℝ) (x : U) (ξ : Fin n → ℂ) :
    Levi n (Subtype.val : U → V n) (fun y => ph y.1) x ξ =
      leviV n (fun w => (ph w : ℂ)) x.1 ξ := by
  have hin : ∀ k, db n (Subtype.val : U → V n) k (fun y => ((ph y.1 : ℝ) : ℂ)) =
      fun y => wdb n k (fun w => (ph w : ℂ)) y.1 :=
    fun k => funext fun y => db_val_eq_wdb_of_isOpen hU k (fun w => (ph w : ℂ)) y
  unfold Levi leviV
  simp only [hin, d_val_eq_wd_of_isOpen hU]

/- English proof (translation)
Establish `hmeas : MeasurableSet U` using `hU.measurableSet`. Use extensionality with `A hA`. Rewrite using `[vol_apply n _ (val_lh hU) A hA, Measure.comap_apply _ Subtype.val_injective (fun s hs => MeasurableSet.subtype_image hmeas hs) _ hA]`. Unfold `volFun`. Establish `hind : ∀ y, (((A ∩ Subtype.val ⁻¹' {y}).encard : ℕ∞) : ℝ≥0∞) = (Subtype.val '' A).indicator 1 y`.

Introduce `y`. Distinguish the cases in `hy : y ∈ Subtype.val '' A`. Take `⟨a, ha, rfl⟩` from `hy`. Establish `h1 : A ∩ Subtype.val ⁻¹' {(a : V n)} = {a}`. Use extensionality with `b`.

Simplify using `only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, hb⟩`. Conclude with `Subtype.ext hb`. Introduce and unpack `rfl`.

Conclude with `⟨ha, rfl⟩`. Rewrite using `[h1, Set.encard_singleton]`. Simplify using `[Set.indicator_apply, Set.mem_image_of_mem _ ha]`. Establish `h1 : A ∩ Subtype.val ⁻¹' {y} = ∅`. Use extensionality with `b`.

Simplify using `only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]`. Introduce `hb hby`. Conclude with `hy ⟨b, hb, hby⟩`. Rewrite using `[h1, Set.encard_empty]`. Simplify using `[Set.indicator_apply, hy]`.

Repeatedly rewrite using `[hind]`. Conclude with `lintegral_indicator_one (MeasurableSet.subtype_image hmeas hA)`.
-/
private theorem vol_val_eq_comap_volume (hU : IsOpen U) :
    vol n (Subtype.val : U → V n) = Measure.comap Subtype.val (volume : Measure (V n)) := by
  have hmeas : MeasurableSet U := hU.measurableSet
  ext A hA
  rw [vol_apply n _ (val_lh hU) A hA,
    Measure.comap_apply _ Subtype.val_injective (fun s hs => MeasurableSet.subtype_image hmeas hs) _ hA]
  unfold volFun
  have hind : ∀ y, (((A ∩ Subtype.val ⁻¹' {y}).encard : ℕ∞) : ℝ≥0∞) =
      (Subtype.val '' A).indicator 1 y := by
    intro y
    by_cases hy : y ∈ Subtype.val '' A
    · obtain ⟨a, ha, rfl⟩ := hy
      have h1 : A ∩ Subtype.val ⁻¹' {(a : V n)} = {a} := by
        ext b
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
        constructor
        · rintro ⟨_, hb⟩
          exact Subtype.ext hb
        · rintro rfl
          exact ⟨ha, rfl⟩
      rw [h1, Set.encard_singleton]
      simp [Set.indicator_apply, Set.mem_image_of_mem _ ha]
    · have h1 : A ∩ Subtype.val ⁻¹' {y} = ∅ := by
        ext b
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
          Set.mem_empty_iff_false, iff_false, not_and]
        intro hb hby
        exact hy ⟨b, hb, hby⟩
      rw [h1, Set.encard_empty]
      simp [Set.indicator_apply, hy]
  simp_rw [hind]
  exact lintegral_indicator_one (MeasurableSet.subtype_image hmeas hA)

/- English proof (translation)
Break down `isEmpty_or_nonempty U with hE | hne` into its components or cases. Establish `hU0 : U = ∅` using `Set.isEmpty_coe_sort.mp hE`. Substitute `hU0` using the available equality. Conclude with `⟨0, differentiableOn_empty, by simp⟩`. Establish `hmeas : MeasurableSet U` using `hU.measurableSet`.

Establish `hs1 : SmoothR n S.z (fun y => ph y.1)`. Rewrite using `[hSz]`. Conclude with `smoothR_of hU hph`. Establish `hs2 : LeviNonneg n S.z (fun y => ph y.1)`. Rewrite using `[hSz]`.

Introduce `x ξ`. Rewrite using `[levi_eq hU ph x ξ]`. Conclude with `hpsh x.1 x.2 ξ`. Establish `hs3 : Smooth n S.z (fun y => F0 y.1)`. Rewrite using `[hSz]`.

Conclude with `smooth_of hU hF0`. Establish `hs4 : Measurable (fun y : U => ENNReal.ofReal (hr y.1))` using `(hrc.restrict.measurable).ennreal_ofReal`. Establish `hs5 : ∀ (x : U) (ξ : Fin n → ℂ), ENNReal.ofReal (‖dbarDot n S.z (fun y => F0 y.1) x ξ‖ ^ 2) ≤ ENNReal.ofReal (hr x.1) * ENNReal.ofReal (Levi n S.z (fun y => ph y.1) x ξ).re`. Rewrite using `[hSz]`. Introduce `x ξ`.

Rewrite using `[dbarDot_eq hU, levi_eq hU, ← ENNReal.ofReal_mul (hr0 x.1 x.2)]`. Conclude with `ENNReal.ofReal_le_ofReal (hineq x.1 x.2 ξ)`. Take `⟨F, hHolo, hint⟩` from `ReciprocityTheory.L2DbarEstimates.hormander n U S (fun y => ph y.1) (fun y => F0 y.1) (fun y => ENNReal.ofReal (hr y.1)) hs1 hs2 hs3 hs4 hs5`. Take `⟨F', hF'⟩ : ∃ F' : V n → ℂ, ∀ x : U, F' x.1 = F x` from `⟨fun y => if h : y ∈ U then F ⟨y, h⟩ else 0, fun x => by simp [x.2]⟩`. Establish `hdiff : DifferentiableOn ℂ F' U`.

Establish `h1` using `hHolo (gch hU) (hSz ▸ gch_isChart hU)`. Rewrite `h1` using `[gch_target]`. Use `h1.congr ?_` and prove the remaining obligations. Introduce `y hy`. Establish `h2 : (gch hU).symm y = ⟨y, hy⟩` using `Subtype.ext (gch_symm hU hy)`.

Simplify using `only [Function.comp_apply, h2]`. Conclude with `hF' ⟨y, hy⟩`. Use `⟨F', hdiff, ?_⟩` and prove the remaining obligations. Establish `L1` using `lintegral_subtype_comap (μ := (volume : Measure (V n))) hmeas (fun y => ENNReal.ofReal (‖F0 y - F' y‖ ^ 2 * Real.exp (-ph y)))`. Establish `L2` using `lintegral_subtype_comap (μ := (volume : Measure (V n))) hmeas (fun y => ENNReal.ofReal (hr y) * ENNReal.ofReal (Real.exp (-ph y)))`.

Rewrite using `[← L1, ← L2, ← vol_val_eq_comap_volume hU]`. Simplify `hint` using `only [wint, hF', hSz]`.
-/
theorem horm_open (hU : IsOpen U) (S : EtaleStein n U) (hSz : S.z = Subtype.val)
    (ph : V n → ℝ) (F0 : V n → ℂ) (hr : V n → ℝ)
    (hph : ContDiffOn ℝ ∞ ph U) (hpsh : ∀ y ∈ U, ∀ ξ, 0 ≤ (leviV n (fun w => (ph w : ℂ)) y ξ).re)
    (hF0 : ContDiffOn ℝ ∞ F0 U) (hrc : ContinuousOn hr U) (hr0 : ∀ y ∈ U, 0 ≤ hr y)
    (hineq : ∀ y ∈ U, ∀ ξ : Fin n → ℂ,
      ‖∑ j, wdb n j F0 y * conj (ξ j)‖ ^ 2 ≤ hr y * (leviV n (fun w => (ph w : ℂ)) y ξ).re) :
    ∃ F : V n → ℂ, DifferentiableOn ℂ F U ∧
      ∫⁻ y in U, ENNReal.ofReal (‖F0 y - F y‖ ^ 2 * Real.exp (-ph y)) ≤
        ∫⁻ y in U, ENNReal.ofReal (hr y) * ENNReal.ofReal (Real.exp (-ph y)) := by
  rcases isEmpty_or_nonempty U with hE | hne
  · have hU0 : U = ∅ := Set.isEmpty_coe_sort.mp hE
    subst hU0
    exact ⟨0, differentiableOn_empty, by simp⟩
  have hmeas : MeasurableSet U := hU.measurableSet
  have hs1 : SmoothR n S.z (fun y => ph y.1) := by
    rw [hSz]
    exact smoothR_of hU hph
  have hs2 : LeviNonneg n S.z (fun y => ph y.1) := by
    rw [hSz]
    intro x ξ
    rw [levi_eq hU ph x ξ]
    exact hpsh x.1 x.2 ξ
  have hs3 : Smooth n S.z (fun y => F0 y.1) := by
    rw [hSz]
    exact smooth_of hU hF0
  have hs4 : Measurable (fun y : U => ENNReal.ofReal (hr y.1)) :=
    (hrc.restrict.measurable).ennreal_ofReal
  have hs5 : ∀ (x : U) (ξ : Fin n → ℂ),
      ENNReal.ofReal (‖dbarDot n S.z (fun y => F0 y.1) x ξ‖ ^ 2) ≤
        ENNReal.ofReal (hr x.1) * ENNReal.ofReal (Levi n S.z (fun y => ph y.1) x ξ).re := by
    rw [hSz]
    intro x ξ
    rw [dbarDot_eq hU, levi_eq hU, ← ENNReal.ofReal_mul (hr0 x.1 x.2)]
    exact ENNReal.ofReal_le_ofReal (hineq x.1 x.2 ξ)
  obtain ⟨F, hHolo, hint⟩ := ReciprocityTheory.L2DbarEstimates.hormander n U S (fun y => ph y.1) (fun y => F0 y.1)
    (fun y => ENNReal.ofReal (hr y.1)) hs1 hs2 hs3 hs4 hs5

  classical
  obtain ⟨F', hF'⟩ : ∃ F' : V n → ℂ, ∀ x : U, F' x.1 = F x :=
    ⟨fun y => if h : y ∈ U then F ⟨y, h⟩ else 0, fun x => by simp [x.2]⟩
  have hdiff : DifferentiableOn ℂ F' U := by
    have h1 := hHolo (gch hU) (hSz ▸ gch_isChart hU)
    rw [gch_target] at h1
    refine h1.congr ?_
    intro y hy
    have h2 : (gch hU).symm y = ⟨y, hy⟩ := Subtype.ext (gch_symm hU hy)
    simp only [Function.comp_apply, h2]
    exact hF' ⟨y, hy⟩
  refine ⟨F', hdiff, ?_⟩
  have L1 := lintegral_subtype_comap (μ := (volume : Measure (V n))) hmeas
    (fun y => ENNReal.ofReal (‖F0 y - F' y‖ ^ 2 * Real.exp (-ph y)))
  have L2 := lintegral_subtype_comap (μ := (volume : Measure (V n))) hmeas
    (fun y => ENNReal.ofReal (hr y) * ENNReal.ofReal (Real.exp (-ph y)))
  rw [← L1, ← L2, ← vol_val_eq_comap_volume hU]
  simpa only [wint, hF', hSz] using hint

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoA
