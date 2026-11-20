import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBumpB
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeBumpB
open scoped GlobalTheory.VacAny

open scoped Pointwise ENNReal in
open GlobalTheory.LocTateInt in
/- English proof (translation)
Introduce `F E _ _ _ _ _ v _ _ lam _ μ hμ`. Use `haveI := finite_FE (F := F) (E := E)`. Use `haveI := isTopologicalRing_Ev (E := E) v`. Use `haveI := t2Space_Fv_tensor (E := E) v`. Use `haveI := locallyCompactSpace_Ev (E := E) v`.

Use `haveI := secondCountable_Ev (E := E) v`. Use `haveI := isOpenUnits_Ev (E := E) v`. Take `⟨_, _, _, _, _⟩` from `idelesAt_facts E (evFin F v)`. Use `haveI := hμ.1`. Use `set φ := idelesAtEquiv E v with hφ`.

Set `j : idelesAt E (evFin F v) → Fv F v ⊗[F] E` to `fun l => ((φ l : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E)`. Establish `hoe : Topology.IsOpenEmbedding j` using `(IsOpenUnits.isOpenEmbedding_unitsVal (M := Fv F v ⊗[F] E)).comp φ.toHomeomorph.isOpenEmbedding`. Establish `hme : MeasurableEmbedding j` using `hoe.measurableEmbedding`. Use `set ν : Measure (idelesAt E (evFin F v)) := lam.comap j with hν`. Establish `hνa : ∀ s, ν s = lam (j '' s)` using `fun s => hme.comap_apply lam s`.

Establish `hne : ∀ x : (Fv F v ⊗[F] E)ˣ, GlobalTheory.Doubling.absEv F E v x ≠ 0` using `fun x h => by`. Establish `e` using `congrArg (GlobalTheory.Doubling.absEv F E v) (mul_inv_cancel x)`. Rewrite `e` using `[map_mul, map_one, h, zero_mul]`. Conclude with `zero_ne_one e`. Use `set f : idelesAt E (evFin F v) → ℝ≥0 := fun l => (GlobalTheory.Doubling.absEv F E v (φ l))⁻¹ with hf`.

Establish `hfc : Continuous f` using `((GlobalTheory.Doubling.continuous_absEv v).comp φ.continuous).inv₀ fun l => hne _`. Establish `hfm : ∀ x y, f (x * y) = f x * f y` using `fun x y => by`. Simplify using `only [hf, map_mul, mul_inv]`. Establish `hf1 : ∀ a, f a⁻¹ * f a = 1` using `fun a => by`. Rewrite using `[← hfm, inv_mul_cancel]`.

Simplify using `[hf]`. Use `haveI : IsLocallyFiniteMeasure ν := by`. Use `⟨fun x => ?_⟩` and prove the remaining obligations. Take `⟨s, hs, hs'⟩` from `lam.finiteAt_nhds (j x)`. Use `⟨j ⁻¹' s, hoe.continuous.continuousAt.preimage_mem_nhds hs, ?_⟩` and prove the remaining obligations.

Rewrite using `[hνa]`. Conclude with `(measure_mono (Set.image_preimage_subset _ _)).trans_lt hs'`. Use `haveI : ν.IsOpenPosMeasure := by`. Use `⟨fun U hU hn => ?_⟩` and prove the remaining obligations. Rewrite using `[hνa]`.

Conclude with `(hoe.isOpenMap U hU).measure_ne_zero lam (hn.image _)`. Use `haveI := IsLocallyFiniteMeasure.withDensity_coe (μ := ν) hfc`. Establish `hpos : (ν.withDensity fun x => (f x : ℝ≥0∞)).IsOpenPosMeasure`. Use `(withDensity_absolutelyContinuous' (μ := ν) (hfc.measurable.coe_nnreal_ennreal.aemeasurable) ?_).isOpenPosMeasure` and prove the remaining obligations. Conclude with `Eventually.of_forall fun x => ENNReal.coe_ne_zero.2 (inv_ne_zero (hne _))`.

Establish `hinv : (ν.withDensity fun x => (f x : ℝ≥0∞)).IsMulLeftInvariant`. Use `⟨fun a => ?_⟩` and prove the remaining obligations. Establish `hma : MeasurableEmbedding (fun x : idelesAt E (evFin F v) => a * x)` using `(Homeomorph.mulLeft a).measurableEmbedding`. Establish `hmap : Measure.map (fun x : idelesAt E (evFin F v) => a * x) ν = (f a : ℝ≥0∞) • ν`. Use extensionality with `s hs`.

Rewrite using `[hma.map_apply, Measure.smul_apply, hνa, hνa, smul_eq_mul]`. Establish `e : j '' ((fun x => a * x) ⁻¹' s) = (φ a)⁻¹ • (j '' s)`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`.

Use `⟨j (a * x), ⟨a * x, hx, rfl⟩, ?_⟩` and prove the remaining obligations. Simplify using `[j, Units.smul_def, map_mul]`. Introduce and unpack `⟨_, ⟨x, hx, rfl⟩, rfl⟩`. Use `⟨a⁻¹ * x, by simpa using hx, ?_⟩` and prove the remaining obligations. Simplify using `[j, Units.smul_def, map_mul, map_inv]`.

Rewrite using `[e, ← distribHaarChar_mul lam (φ a)⁻¹ (j '' s), map_inv, distribHaarChar_Ev]`. Both sides reduce to the same expression. Use extensionality with `s hs`. Rewrite using `[hma.map_apply, withDensity_apply _ (hma.measurable hs), withDensity_apply _ hs]`. Establish `h1 : ∀ x, (f x : ℝ≥0∞) = (f a⁻¹ : ℝ≥0∞) * (f (a * x) : ℝ≥0∞)` using `fun x => by`.

Rewrite using `[← ENNReal.coe_mul, hfm, ← mul_assoc, hf1, one_mul]`. Establish `h2 : (f a⁻¹ : ℝ≥0∞) * (f a : ℝ≥0∞) = 1`. Rewrite using `[← ENNReal.coe_mul, hf1, ENNReal.coe_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hma.restrict_map, hma.lintegral_map]`.

Use `_ = _ := by`. Rewrite using `[hmap, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul, ← mul_assoc, h2, one_mul]`. Use `set ρ := ν.withDensity fun x => (f x : ℝ≥0∞) with hρ`. Use `haveI : ρ.IsHaarMeasure := ⟨⟩`. Take `⟨c, hc0, hc⟩` from `haar_idelesAt_eq_smul μ ρ`.

Use `⟨c, by exact_mod_cast pos_iff_ne_zero.2 hc0, fun g hg => ?_⟩` and prove the remaining obligations. Rewrite using `[hc, integral_smul_nnreal_measure, hρ, integral_withDensity_eq_integral_smul hfc.measurable]`. Establish `h1 : ∀ l : idelesAt E (evFin F v), f l • (g (compFin F E v (l.1 : AE F E)) * ((absE F E l.1 : ℝ) : ℂ)) = g (j l)`. Introduce `l`. Establish `e : absE F E l.1 = GlobalTheory.Doubling.absEv F E v (φ l)`.

Rewrite using `[absE_of_mem l.2]`. Both sides reduce to the same expression. Establish `e2 : ((GlobalTheory.Doubling.absEv F E v (φ l) : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hne (φ l)`. Rewrite using `[e, NNReal.smul_def, Complex.real_smul, show compFin F E v (l.1 : AE F E) = j l from rfl]`. Simplify using `only [hf, NNReal.coe_inv, Complex.ofReal_inv]`.

Clear the denominators using the available nonvanishing facts. Repeatedly rewrite using `[h1]`. Establish `h2 : ∫ l, g (j l) ∂ν = ∫ s, g s ∂lam`. Rewrite using `[← hme.integral_map, hν, hme.map_comap]`. Use `setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_` and prove the remaining obligations.

Assume the negation of the conclusion as `h`. Take `⟨u, rfl⟩` from `hg t h`. Conclude with `ht ⟨φ.symm u, by simp [j]⟩`. Rewrite using `[h2, NNReal.smul_def, Complex.real_smul]`.
-/
theorem UpperTheory.local_units_haar_comparison :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F), ∀ [MeasurableSpace (Fv F v ⊗[F] E)] [BorelSpace (Fv F v ⊗[F] E)] (m : Measure (Fv F v ⊗[F] E)) [m.IsAddHaarMeasure],
        ∀ (μ : Measure (idelesAt E (evFin F v))), IsNormE E v μ → ∃ c : ℝ, 0 < c ∧ ∀ f : Fv F v ⊗[F] E → ℂ, (∀ t, f t ≠ 0 → IsUnit t) →
          ∫ l : idelesAt E (evFin F v), f (compFin F E v (l.1 : AE F E)) * ((absE F E l.1 : ℝ) : ℂ) ∂μ = (c : ℂ) * ∫ s, f s ∂m := by
  intro F E _ _ _ _ _ v _ _ lam _ μ hμ
  haveI := finite_FE (F := F) (E := E)
  haveI := isTopologicalRing_Ev (E := E) v
  haveI := t2Space_Fv_tensor (E := E) v
  haveI := locallyCompactSpace_Ev (E := E) v
  haveI := secondCountable_Ev (E := E) v
  haveI := isOpenUnits_Ev (E := E) v
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evFin F v)
  haveI := hμ.1
  set φ := idelesAtEquiv E v with hφ
  let j : idelesAt E (evFin F v) → Fv F v ⊗[F] E := fun l => ((φ l : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E)
  have hoe : Topology.IsOpenEmbedding j :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := Fv F v ⊗[F] E)).comp φ.toHomeomorph.isOpenEmbedding
  have hme : MeasurableEmbedding j := hoe.measurableEmbedding
  set ν : Measure (idelesAt E (evFin F v)) := lam.comap j with hν
  have hνa : ∀ s, ν s = lam (j '' s) := fun s => hme.comap_apply lam s
  have hne : ∀ x : (Fv F v ⊗[F] E)ˣ, GlobalTheory.Doubling.absEv F E v x ≠ 0 := fun x h => by
    have e := congrArg (GlobalTheory.Doubling.absEv F E v) (mul_inv_cancel x)
    rw [map_mul, map_one, h, zero_mul] at e
    exact zero_ne_one e
  set f : idelesAt E (evFin F v) → ℝ≥0 := fun l => (GlobalTheory.Doubling.absEv F E v (φ l))⁻¹ with hf
  have hfc : Continuous f :=
    ((GlobalTheory.Doubling.continuous_absEv v).comp φ.continuous).inv₀ fun l => hne _
  have hfm : ∀ x y, f (x * y) = f x * f y := fun x y => by
    simp only [hf, map_mul, mul_inv]
  have hf1 : ∀ a, f a⁻¹ * f a = 1 := fun a => by
    rw [← hfm, inv_mul_cancel]
    simp [hf]
  haveI : IsLocallyFiniteMeasure ν := by
    refine ⟨fun x => ?_⟩
    obtain ⟨s, hs, hs'⟩ := lam.finiteAt_nhds (j x)
    refine ⟨j ⁻¹' s, hoe.continuous.continuousAt.preimage_mem_nhds hs, ?_⟩
    rw [hνa]
    exact (measure_mono (Set.image_preimage_subset _ _)).trans_lt hs'
  haveI : ν.IsOpenPosMeasure := by
    refine ⟨fun U hU hn => ?_⟩
    rw [hνa]
    exact (hoe.isOpenMap U hU).measure_ne_zero lam (hn.image _)
  haveI := IsLocallyFiniteMeasure.withDensity_coe (μ := ν) hfc
  have hpos : (ν.withDensity fun x => (f x : ℝ≥0∞)).IsOpenPosMeasure := by
    refine (withDensity_absolutelyContinuous' (μ := ν)
      (hfc.measurable.coe_nnreal_ennreal.aemeasurable) ?_).isOpenPosMeasure
    exact Eventually.of_forall fun x => ENNReal.coe_ne_zero.2 (inv_ne_zero (hne _))
  have hinv : (ν.withDensity fun x => (f x : ℝ≥0∞)).IsMulLeftInvariant := by
    refine ⟨fun a => ?_⟩
    have hma : MeasurableEmbedding (fun x : idelesAt E (evFin F v) => a * x) :=
      (Homeomorph.mulLeft a).measurableEmbedding
    have hmap : Measure.map (fun x : idelesAt E (evFin F v) => a * x) ν = (f a : ℝ≥0∞) • ν := by
      ext s hs
      rw [hma.map_apply, Measure.smul_apply, hνa, hνa, smul_eq_mul]
      have e : j '' ((fun x => a * x) ⁻¹' s) = (φ a)⁻¹ • (j '' s) := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          refine ⟨j (a * x), ⟨a * x, hx, rfl⟩, ?_⟩
          simp [j, Units.smul_def, map_mul]
        · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
          refine ⟨a⁻¹ * x, by simpa using hx, ?_⟩
          simp [j, Units.smul_def, map_mul, map_inv]
      rw [e, ← distribHaarChar_mul lam (φ a)⁻¹ (j '' s), map_inv, distribHaarChar_Ev]
      rfl
    ext s hs
    rw [hma.map_apply, withDensity_apply _ (hma.measurable hs), withDensity_apply _ hs]
    have h1 : ∀ x, (f x : ℝ≥0∞) = (f a⁻¹ : ℝ≥0∞) * (f (a * x) : ℝ≥0∞) := fun x => by
      rw [← ENNReal.coe_mul, hfm, ← mul_assoc, hf1, one_mul]
    have h2 : (f a⁻¹ : ℝ≥0∞) * (f a : ℝ≥0∞) = 1 := by
      rw [← ENNReal.coe_mul, hf1, ENNReal.coe_one]
    calc ∫⁻ x in (fun x => a * x) ⁻¹' s, (f x : ℝ≥0∞) ∂ν
        = ∫⁻ x in (fun x => a * x) ⁻¹' s, (f a⁻¹ : ℝ≥0∞) * (f (a * x) : ℝ≥0∞) ∂ν := lintegral_congr h1
      _ = (f a⁻¹ : ℝ≥0∞) * ∫⁻ x in (fun x => a * x) ⁻¹' s, (f (a * x) : ℝ≥0∞) ∂ν :=
          lintegral_const_mul' _ _ ENNReal.coe_ne_top
      _ = (f a⁻¹ : ℝ≥0∞) * ∫⁻ x in s, (f x : ℝ≥0∞) ∂(Measure.map (fun x => a * x) ν) := by
          rw [hma.restrict_map, hma.lintegral_map]
      _ = _ := by
          rw [hmap, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul, ← mul_assoc, h2, one_mul]
  set ρ := ν.withDensity fun x => (f x : ℝ≥0∞) with hρ
  haveI : ρ.IsHaarMeasure := ⟨⟩
  obtain ⟨c, hc0, hc⟩ := haar_idelesAt_eq_smul μ ρ
  refine ⟨c, by exact_mod_cast pos_iff_ne_zero.2 hc0, fun g hg => ?_⟩
  rw [hc, integral_smul_nnreal_measure, hρ, integral_withDensity_eq_integral_smul hfc.measurable]
  have h1 : ∀ l : idelesAt E (evFin F v),
      f l • (g (compFin F E v (l.1 : AE F E)) * ((absE F E l.1 : ℝ) : ℂ)) = g (j l) := by
    intro l
    have e : absE F E l.1 = GlobalTheory.Doubling.absEv F E v (φ l) := by
      rw [absE_of_mem l.2]
      rfl
    have e2 : ((GlobalTheory.Doubling.absEv F E v (φ l) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hne (φ l)
    rw [e, NNReal.smul_def, Complex.real_smul, show compFin F E v (l.1 : AE F E) = j l from rfl]
    simp only [hf, NNReal.coe_inv, Complex.ofReal_inv]
    field_simp
  simp_rw [h1]
  have h2 : ∫ l, g (j l) ∂ν = ∫ s, g s ∂lam := by
    rw [← hme.integral_map, hν, hme.map_comap]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_
    by_contra h
    obtain ⟨u, rfl⟩ := hg t h
    exact ht ⟨φ.symm u, by simp [j]⟩
  rw [h2, NNReal.smul_def, Complex.real_smul]
