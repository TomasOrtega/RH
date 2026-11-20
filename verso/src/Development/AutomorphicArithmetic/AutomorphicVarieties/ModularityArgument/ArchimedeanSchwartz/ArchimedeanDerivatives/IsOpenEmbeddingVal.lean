import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ShiftOf
import GroundTheory.AutomorphicForms.RealGroupsHaar

noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GroundTheory.Automorphic

namespace UpperTheory.V.Z.Inf

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private def lm (y : Lie K n) : Lie K n →ₗ[ℝ] Lie K n :=
  LinearMap.mulLeft ℝ (A := Matrix (Fin n) (Fin n) (InfinitePlace K → ℂ)) (Matrix.of y)

private def placeOut (K : Type) [Field K] [NumberField K] (n : ℕ) :
    Lie K n ≃ₗ[ℝ] (InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) where
  toFun x v := Matrix.of fun i j => x i j v
  invFun y i j v := y v i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/- English proof (translation)
Use `set e := placeOut K n`. Establish `hc : e.toLinearMap ∘ₗ lm y ∘ₗ e.symm.toLinearMap = LinearMap.pi (fun v => ((LinearMap.mulLeft ℂ (e y v)).restrictScalars ℝ) ∘ₗ LinearMap.proj v)`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`. Use function extensionality and compare the values at `v i j`.

Use `show (Matrix.of y * Matrix.of (fun i j v => x v i j)) i j v = ∑ k, y i k v * x v k j`. Rewrite using `[Matrix.mul_apply, Finset.sum_apply]`. Both sides reduce to the same expression. Rewrite using `[← LinearMap.det_conj _ e, hc, LinearMap.det_pi, nrm, ← Finset.prod_pow]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations.

Rewrite using `[det_restrictScalars_mulLeft, Fintype.card_fin]`. Use `congr 3`. Rewrite using `[show (Matrix.of y).det v = Pi.evalRingHom _ v (Matrix.of y).det from rfl, RingHom.map_det]`. Both sides reduce to the same expression.
-/
private theorem det_lm (y : Lie K n) : LinearMap.det (lm y) = nrm y ^ n := by
  classical
  set e := placeOut K n
  have hc : e.toLinearMap ∘ₗ lm y ∘ₗ e.symm.toLinearMap =
      LinearMap.pi (fun v => ((LinearMap.mulLeft ℂ (e y v)).restrictScalars ℝ) ∘ₗ LinearMap.proj v) := by
    apply LinearMap.ext; intro x
    funext v i j
    show (Matrix.of y * Matrix.of (fun i j v => x v i j)) i j v = ∑ k, y i k v * x v k j
    rw [Matrix.mul_apply, Finset.sum_apply]
    rfl
  rw [← LinearMap.det_conj _ e, hc, LinearMap.det_pi, nrm, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [det_restrictScalars_mulLeft, Fintype.card_fin]
  congr 3
  rw [show (Matrix.of y).det v = Pi.evalRingHom _ v (Matrix.of y).det from rfl, RingHom.map_det]
  rfl

/- English proof (translation)
Use `show ∏ w, ‖(Matrix.of y * Matrix.of x).det w‖ ^ 2 = _`. Simplify using `only [nrm, Matrix.det_mul, Pi.mul_apply, norm_mul, mul_pow, Finset.prod_mul_distrib]`.
-/
private theorem nrm_lm (y x : Lie K n) : nrm (lm y x) = nrm y * nrm x := by
  show ∏ w, ‖(Matrix.of y * Matrix.of x).det w‖ ^ 2 = _
  simp only [nrm, Matrix.det_mul, Pi.mul_apply, norm_mul, mul_pow, Finset.prod_mul_distrib]

/- English proof (translation)
The claim follows from `Finset.prod_nonneg fun _ _ => by positivity`.
-/
private theorem nrm_nonneg (x : Lie K n) : 0 ≤ nrm x :=
  Finset.prod_nonneg fun _ _ => by positivity

/- English proof (translation)
Establish `h : x ∈ invSet K n ↔ IsUnit (Matrix.of x).det` using `Matrix.isUnit_iff_isUnit_det (Matrix.of x)`. Rewrite using `[h, Pi.isUnit_iff, (nrm_nonneg x).lt_iff_ne, ne_comm, nrm, Finset.prod_ne_zero_iff]`. Simplify using the standard rewrite rules.
-/
private theorem nrm_pos_iff (x : Lie K n) : 0 < nrm x ↔ x ∈ invSet K n := by
  have h : x ∈ invSet K n ↔ IsUnit (Matrix.of x).det := Matrix.isUnit_iff_isUnit_det (Matrix.of x)
  rw [h, Pi.isUnit_iff, (nrm_nonneg x).lt_iff_ne, ne_comm, nrm, Finset.prod_ne_zero_iff]
  simp

/- English proof (translation)
Use `continuous_finset_prod _ fun w _ => (Continuous.norm ?_).pow 2` and prove the remaining obligations. Conclude with `(continuous_apply w).comp (continuous_id (X := Matrix (Fin n) (Fin n) (InfinitePlace K → ℂ))).matrix_det`.
-/
private theorem continuous_nrm : Continuous (nrm : Lie K n → ℝ) := by
  refine continuous_finset_prod _ fun w _ => (Continuous.norm ?_).pow 2
  exact (continuous_apply w).comp
    (continuous_id (X := Matrix (Fin n) (Fin n) (InfinitePlace K → ℂ))).matrix_det

/- English proof (translation)
Use `⟨Units.isEmbedding_val_mk' (f := fun x => Ring.inverse x.det • x.adjugate) ?_ ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Establish `hd : IsUnit x.det` using `(Matrix.isUnit_iff_isUnit_det x).1 hx`. Use `ContinuousAt.continuousWithinAt ?_` and prove the remaining obligations. Use `ContinuousAt.smul (M := Cinf K) (f := fun x : Matrix (Fin n) (Fin n) (Cinf K) => Ring.inverse x.det) ?_ ((continuous_id (X := Matrix (Fin n) (Fin n) (Cinf K))).matrix_adjugate).continuousAt` and prove the remaining obligations.

Conclude with `ContinuousAt.comp_of_eq (NormedRing.inverse_continuousAt hd.unit) ((continuous_id (X := Matrix (Fin n) (Fin n) (Cinf K))).matrix_det).continuousAt hd.unit_spec.symm`. Introduce `u`. Rewrite using `[Matrix.coe_units_inv, Matrix.inv_def]`. Establish `: Set.range (Units.val : GL (Fin n) (Cinf K) → Matrix (Fin n) (Fin n) (Cinf K)) = {x | IsUnit x}`. Use extensionality with `x`.

Conclude with `⟨fun ⟨u, hu⟩ => hu ▸ u.isUnit, fun h => ⟨h.unit, h.unit_spec⟩⟩`. Rewrite using `[this]`. Conclude with `isOpen_invSet (E := K) (a := n)`.
-/
private theorem isOpenEmbedding_val :
    Topology.IsOpenEmbedding (Units.val : GL (Fin n) (Cinf K) → Matrix (Fin n) (Fin n) (Cinf K)) := by
  refine ⟨Units.isEmbedding_val_mk' (f := fun x => Ring.inverse x.det • x.adjugate) ?_ ?_, ?_⟩
  · intro x hx
    have hd : IsUnit x.det := (Matrix.isUnit_iff_isUnit_det x).1 hx
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.smul (M := Cinf K) (f := fun x : Matrix (Fin n) (Fin n) (Cinf K) => Ring.inverse x.det) ?_
      ((continuous_id (X := Matrix (Fin n) (Fin n) (Cinf K))).matrix_adjugate).continuousAt
    exact ContinuousAt.comp_of_eq (NormedRing.inverse_continuousAt hd.unit)
      ((continuous_id (X := Matrix (Fin n) (Fin n) (Cinf K))).matrix_det).continuousAt hd.unit_spec.symm
  · intro u
    rw [Matrix.coe_units_inv, Matrix.inv_def]
  · have : Set.range (Units.val : GL (Fin n) (Cinf K) → Matrix (Fin n) (Fin n) (Cinf K)) = {x | IsUnit x} := by
      ext x; exact ⟨fun ⟨u, hu⟩ => hu ▸ u.isUnit, fun h => ⟨h.unit, h.unit_spec⟩⟩
    rw [this]
    exact isOpen_invSet (E := K) (a := n)

/- English proof (translation)
Use `haveI : (volume : Measure (Cinf K)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _`. Use `haveI : (volume : Measure (Fin n → Cinf K)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _`. Conclude with `Measure.pi.isAddHaarMeasure _`.
-/
private theorem addHaar_vol : (volume : Measure (Lie K n)).IsAddHaarMeasure := by
  haveI : (volume : Measure (Cinf K)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (Fin n → Cinf K)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  exact Measure.pi.isAddHaarMeasure _

/- English proof (translation)
The claim follows from `ENNReal.measurable_ofReal.comp (continuous_nrm.measurable.inv.pow_const _)`.
-/
private theorem measurable_dens : Measurable fun x : Lie K n => ENNReal.ofReal ((nrm x)⁻¹ ^ n) :=
  ENNReal.measurable_ofReal.comp (continuous_nrm.measurable.inv.pow_const _)

/- English proof (translation)
Use `haveI := addHaar_vol (K := K) (n := n)`. Establish `hp` using `(nrm_pos_iff y).2 hy`. Establish `hdet : LinearMap.det (lm y) ≠ 0` using `by rw [det_lm]; positivity`. Establish `hmap` using `Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Lie K n)) hdet`. Use `map_withDensity_eq_of_scale (volume : Measure (Lie K n)) measurable_dens (lm y) (ENNReal.ofReal_pos.2 (abs_pos.2 (inv_ne_zero hdet))).ne' ENNReal.ofReal_ne_top hmap fun x => ?_` and prove the remaining obligations.

Rewrite using `[det_lm, nrm_lm, abs_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity), mul_inv, mul_pow, inv_pow (nrm y)]`.
-/
private theorem map_lm (y : Lie K n) (hy : y ∈ invSet K n) :
    Measure.map (lm y) ((volume : Measure (Lie K n)).withDensity fun x => ENNReal.ofReal ((nrm x)⁻¹ ^ n)) =
      (volume : Measure (Lie K n)).withDensity fun x => ENNReal.ofReal ((nrm x)⁻¹ ^ n) := by
  haveI := addHaar_vol (K := K) (n := n)
  have hp := (nrm_pos_iff y).2 hy
  have hdet : LinearMap.det (lm y) ≠ 0 := by rw [det_lm]; positivity
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Lie K n)) hdet
  refine map_withDensity_eq_of_scale (volume : Measure (Lie K n)) measurable_dens (lm y)
    (ENNReal.ofReal_pos.2 (abs_pos.2 (inv_ne_zero hdet))).ne' ENNReal.ofReal_ne_top hmap fun x => ?_
  rw [det_lm, nrm_lm, abs_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity), mul_inv, mul_pow,
    inv_pow (nrm y)]

end UpperTheory.V.Z.Inf

open UpperTheory.V.Z.Inf in
/- English proof (translation)
Introduce `K _ _ _ n _ _`. Use `haveI := addHaar_vol (K := K) (n := n)`. Use `set w : Lie K n → ENNReal := fun x => ENNReal.ofReal ((nrm x)⁻¹ ^ n) with hw`. Use `set μL : Measure (Lie K n) := (volume : Measure (Lie K n)).withDensity w with hμL`. Use `set e : GL (Fin n) (Cinf K) → Lie K n := fun g => toL g.val with he`.

Establish `hOE : Topology.IsOpenEmbedding e` using `isOpenEmbedding_val`. Establish `hE : MeasurableEmbedding e` using `hOE.measurableEmbedding`. Establish `hwm : Measurable w` using `measurable_dens`. Establish `happ : ∀ s, Measure.comap e μL s = μL (e '' s)` using `fun s => hE.comap_apply _ s`. Establish `hmem : ∀ g, e g ∈ invSet K n` using `fun g => g.isUnit`.

Establish `hpos : ∀ g, 0 < nrm (e g)` using `fun g => (nrm_pos_iff _).2 (hmem g)`. Use `⟨Measure.comap e μL, ?_, ?_⟩` and prove the remaining obligations. Use `{ lt_top_of_isCompact := ?_, map_mul_left_eq_self := ?_, open_pos := ?_ }` and prove the remaining obligations. Introduce `C hC`. Rewrite using `[happ]`.

Establish `hC' : IsCompact (e '' C)` using `hC.image hOE.continuous`. Establish `hmeas : MeasurableSet (e '' C)` using `hC'.isClosed.measurableSet`. Establish `hcont : Continuous (fun g : GL (Fin n) (Cinf K) => (nrm (e g))⁻¹ ^ n)` using `((continuous_nrm.comp hOE.continuous).inv₀ fun g => (hpos g).ne').pow _`. Take `⟨B, hB⟩` from `hC.exists_bound_of_continuousOn hcont.continuousOn`. Rewrite using `[hμL, withDensity_apply _ hmeas]`.

Combine the equalities or inequalities in the displayed calculation. Use `setLIntegral_mono' hmeas fun x hx => ?_` and prove the remaining obligations. Take `⟨g, hg, rfl⟩` from `hx`. Conclude with `ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hB g hg))`. Use `_ = ENNReal.ofReal B * volume (e '' C) := setLIntegral_const _ _`.

Use `_ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC'.measure_lt_top`. Introduce `g`. Use extensionality with `s hs`. Establish `hm : Measurable (fun h : GL (Fin n) (Cinf K) => g * h)` using `(continuous_const.mul continuous_id).measurable`. Rewrite using `[Measure.map_apply hm hs, happ, happ]`.

Establish `hmeas : MeasurableSet (e '' s)` using `hE.measurableSet_image.2 hs`. Establish `h1 : e '' ((fun h => g * h) ⁻¹' s) = (lm (e g)) ⁻¹' (e '' s)` using `image_val_preimage_mul_left g s`. Rewrite using `[h1, ← Measure.map_apply (lm (e g)).continuous_of_finiteDimensional.measurable hmeas, map_lm _ (hmem g)]`. Introduce `U hU hne`. Rewrite using `[happ, ne_eq, hμL, withDensity_apply_eq_zero' hwm.aemeasurable]`.

Establish `hsub : {x | w x ≠ 0} ∩ e '' U = e '' U`. Use `Set.inter_eq_right.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g, _, rfl⟩`. Conclude with `(ENNReal.ofReal_pos.2 (pow_pos (inv_pos.2 (hpos g)) _)).ne'`. Rewrite using `[hsub]`.

Conclude with `(hOE.isOpenMap U hU).measure_ne_zero volume (hne.image _)`. Establish `hr : Set.range e = invSet K n`. Use extensionality with `x`. Conclude with `⟨fun ⟨g, hg⟩ => hg ▸ hmem g, fun h => ⟨IsUnit.unit h, rfl⟩⟩`. Rewrite using `[hE.map_comap, hr, hμL, restrict_withDensity isOpen_invSet.measurableSet]`.
-/
theorem UpperTheory.V.Z.Inf.haarL :
    UpperTheory.V.Z.Inf.HaarL := by
  intro K _ _ _ n _ _
  haveI := addHaar_vol (K := K) (n := n)
  set w : Lie K n → ENNReal := fun x => ENNReal.ofReal ((nrm x)⁻¹ ^ n) with hw
  set μL : Measure (Lie K n) := (volume : Measure (Lie K n)).withDensity w with hμL
  set e : GL (Fin n) (Cinf K) → Lie K n := fun g => toL g.val with he
  have hOE : Topology.IsOpenEmbedding e := isOpenEmbedding_val
  have hE : MeasurableEmbedding e := hOE.measurableEmbedding
  have hwm : Measurable w := measurable_dens
  have happ : ∀ s, Measure.comap e μL s = μL (e '' s) := fun s => hE.comap_apply _ s
  have hmem : ∀ g, e g ∈ invSet K n := fun g => g.isUnit
  have hpos : ∀ g, 0 < nrm (e g) := fun g => (nrm_pos_iff _).2 (hmem g)
  refine ⟨Measure.comap e μL, ?_, ?_⟩
  · refine { lt_top_of_isCompact := ?_, map_mul_left_eq_self := ?_, open_pos := ?_ }
    · intro C hC
      rw [happ]
      have hC' : IsCompact (e '' C) := hC.image hOE.continuous
      have hmeas : MeasurableSet (e '' C) := hC'.isClosed.measurableSet
      have hcont : Continuous (fun g : GL (Fin n) (Cinf K) => (nrm (e g))⁻¹ ^ n) :=
        ((continuous_nrm.comp hOE.continuous).inv₀ fun g => (hpos g).ne').pow _
      obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hcont.continuousOn
      rw [hμL, withDensity_apply _ hmeas]
      calc ∫⁻ x in e '' C, w x ∂volume
          ≤ ∫⁻ _ in e '' C, ENNReal.ofReal B ∂volume := by
            refine setLIntegral_mono' hmeas fun x hx => ?_
            obtain ⟨g, hg, rfl⟩ := hx
            exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hB g hg))
        _ = ENNReal.ofReal B * volume (e '' C) := setLIntegral_const _ _
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC'.measure_lt_top
    · intro g
      ext s hs
      have hm : Measurable (fun h : GL (Fin n) (Cinf K) => g * h) :=
        (continuous_const.mul continuous_id).measurable
      rw [Measure.map_apply hm hs, happ, happ]
      have hmeas : MeasurableSet (e '' s) := hE.measurableSet_image.2 hs
      have h1 : e '' ((fun h => g * h) ⁻¹' s) = (lm (e g)) ⁻¹' (e '' s) :=
        image_val_preimage_mul_left g s
      rw [h1, ← Measure.map_apply (lm (e g)).continuous_of_finiteDimensional.measurable hmeas,
        map_lm _ (hmem g)]
    · intro U hU hne
      rw [happ, ne_eq, hμL, withDensity_apply_eq_zero' hwm.aemeasurable]
      have hsub : {x | w x ≠ 0} ∩ e '' U = e '' U := by
        refine Set.inter_eq_right.2 ?_
        rintro _ ⟨g, _, rfl⟩
        exact (ENNReal.ofReal_pos.2 (pow_pos (inv_pos.2 (hpos g)) _)).ne'
      rw [hsub]
      exact (hOE.isOpenMap U hU).measure_ne_zero volume (hne.image _)
  · have hr : Set.range e = invSet K n := by
      ext x
      exact ⟨fun ⟨g, hg⟩ => hg ▸ hmem g, fun h => ⟨IsUnit.unit h, rfl⟩⟩
    rw [hE.map_comap, hr, hμL, restrict_withDensity isOpen_invSet.measurableSet]
