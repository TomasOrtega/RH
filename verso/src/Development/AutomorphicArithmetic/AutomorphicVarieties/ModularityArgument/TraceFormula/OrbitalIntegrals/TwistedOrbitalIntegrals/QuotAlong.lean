import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.GeoTransport

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

/- English proof (translation)
Introduce `_ _ G _ _ _ _ _ _ _ _ H _ _ _ _ _ _ _ _ j hj μG hμ T S hT hc hS ν hν`. Substitute `hS` using the available equality. Set `e₀ : T ≃* T.map j` to `T.equivMapOfInjective j hj.injective`. Establish `c1 : Continuous e₀` using `(hj.continuous.comp continuous_subtype_val).subtype_mk _`. Establish `c2 : Continuous e₀.symm`.

Rewrite using `[(hj.isInducing.comp IsInducing.subtypeVal).continuous_iff]`. Establish `: (j ∘ Subtype.val) ∘ e₀.symm = Subtype.val` using `funext fun x => congrArg Subtype.val (e₀.apply_symm_apply x)`. Conclude with `continuous_subtype_val.congr fun x => (congrFun this x).symm`. Set `e : T ≃ₜ* T.map j` to `⟨e₀, c1, c2⟩`. Establish `he : Measurable (e : T → T.map j)` using `c1.measurable`.

Use `⟨ν.map e, e.isHaarMeasure_map ν, Measure.map_map (g := fun x : T.map j => (x : G)) measurable_subtype_coe he, fun F _ _ => ?_⟩` and prove the remaining obligations. Establish `hp : PositivityTheory.Rg.Tf.Geo.IsNormAlong id (fun t : T => j t) ν = IsQuotNormaliser (T.map j) (ν.map e)`. Use function extensionality and compare the values at `ρ`. Use `propext (and_congr_right fun hρ => forall_congr' fun g => ?_)` and prove the remaining obligations. Rewrite using `[lintegral_map (f := fun h : T.map j => ρ (h * g)) (hρ.comp (measurable_subtype_coe.mul_const g)) he]`.

Both sides reduce to the same expression. Establish `gen : ∀ p q : (G → ℝ≥0∞) → Prop, p = q → ∀ [Decidable (∃ ρ, p ρ)] [Decidable (∃ ρ, q ρ)], (if h : ∃ ρ, p ρ then ∫ x, F x * ((h.choose x).toReal : ℂ) ∂μG else 0) = (if h : ∃ ρ, q ρ then ∫ x, F x * ((h.choose x).toReal : ℂ) ∂μG else 0)`. Introduce and unpack `p _ rfl _ _`. Reduce the equality to equality of the corresponding arguments. Conclude with `@gen _ _ hp (Classical.propDecidable _) (Classical.propDecidable _)`.
-/
theorem UpperTheory.V.Z.Tf.Orb.quotAlong :
    UpperTheory.V.Z.Tf.Orb.HaarComm → UpperTheory.V.Z.Tf.Orb.QuotIndep → UpperTheory.V.Z.Tf.Orb.QuotAlong := by
  intro _ _ G _ _ _ _ _ _ _ _ H _ _ _ _ _ _ _ _ j hj μG hμ T S hT hc hS ν hν
  subst hS
  let e₀ : T ≃* T.map j := T.equivMapOfInjective j hj.injective
  have c1 : Continuous e₀ := (hj.continuous.comp continuous_subtype_val).subtype_mk _
  have c2 : Continuous e₀.symm := by
    rw [(hj.isInducing.comp IsInducing.subtypeVal).continuous_iff]
    have : (j ∘ Subtype.val) ∘ e₀.symm = Subtype.val := funext fun x => congrArg Subtype.val (e₀.apply_symm_apply x)
    exact continuous_subtype_val.congr fun x => (congrFun this x).symm
  let e : T ≃ₜ* T.map j := ⟨e₀, c1, c2⟩
  have he : Measurable (e : T → T.map j) := c1.measurable
  refine ⟨ν.map e, e.isHaarMeasure_map ν, Measure.map_map (g := fun x : T.map j => (x : G)) measurable_subtype_coe he, fun F _ _ => ?_⟩
  have hp : PositivityTheory.Rg.Tf.Geo.IsNormAlong id (fun t : T => j t) ν = IsQuotNormaliser (T.map j) (ν.map e) := by
    funext ρ
    refine propext (and_congr_right fun hρ => forall_congr' fun g => ?_)
    rw [lintegral_map (f := fun h : T.map j => ρ (h * g)) (hρ.comp (measurable_subtype_coe.mul_const g)) he]
    rfl
  have gen : ∀ p q : (G → ℝ≥0∞) → Prop, p = q → ∀ [Decidable (∃ ρ, p ρ)] [Decidable (∃ ρ, q ρ)],
      (if h : ∃ ρ, p ρ then ∫ x, F x * ((h.choose x).toReal : ℂ) ∂μG else 0) =
      (if h : ∃ ρ, q ρ then ∫ x, F x * ((h.choose x).toReal : ℂ) ∂μG else 0) := by
    rintro p _ rfl _ _
    congr
  exact @gen _ _ hp (Classical.propDecidable _) (Classical.propDecidable _)
