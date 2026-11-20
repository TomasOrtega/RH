import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatEqLowMat
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.ExhaustionFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall

noncomputable section

/- English proof (translation)
Establish `h : (volume : Measure (ι × κ → ℂ)) = (volume : Measure (ι → κ → ℂ)).map (MeasurableEquiv.curry ι κ ℂ).symm`. Use `Measure.pi_eq fun s hs => ?_` and prove the remaining obligations. Rewrite using `[Measure.map_apply (MeasurableEquiv.measurable _) (MeasurableSet.univ_pi hs)]`. Establish `e : (MeasurableEquiv.curry ι κ ℂ).symm ⁻¹' Set.univ.pi s = Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j)))`. Use extensionality with `f`.

Simplify using `[MeasurableEquiv.coe_curry_symm, Function.uncurry]`. Rewrite using `[e, volume_pi, Measure.pi_pi]`. Repeatedly rewrite using `[volume_pi, Measure.pi_pi]`. Rewrite using `[Fintype.prod_prod_type]`. Use `⟨(MeasurableEquiv.curry ι κ ℂ).measurable, ?_⟩` and prove the remaining obligations.

Rewrite using `[h, Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _)]`. Simplify using the standard rewrite rules.
-/
theorem measurePreserving_curry_lowCoord (ι κ : Type) [Fintype ι] [Fintype κ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ ℂ) volume volume := by
  have h : (volume : Measure (ι × κ → ℂ)) =
      (volume : Measure (ι → κ → ℂ)).map (MeasurableEquiv.curry ι κ ℂ).symm := by
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply (MeasurableEquiv.measurable _) (MeasurableSet.univ_pi hs)]
    have e : (MeasurableEquiv.curry ι κ ℂ).symm ⁻¹' Set.univ.pi s =
        Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
      ext f; simp [MeasurableEquiv.coe_curry_symm, Function.uncurry]
    rw [e, volume_pi, Measure.pi_pi]
    simp_rw [volume_pi, Measure.pi_pi]
    rw [Fintype.prod_prod_type]
  refine ⟨(MeasurableEquiv.curry ι κ ℂ).measurable, ?_⟩
  rw [h, Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _)]
  simp

/- English proof (translation)
Introduce `E _ _ _ r X h hh`. Use `set e := Fintype.equivFin (Ent X) with he`. Use `set G : (Fin (nd X) → ℂ) → ℝ≥0∞ := fun y => ∏ τ, h (fun p => y (e ⟨τ, p⟩)) with hG`. Establish `hGm : Measurable G` using `Finset.measurable_prod _ fun τ _ => hh.comp (measurable_pi_lambda _ fun p => measurable_pi_apply _)`. Establish `s1 : ∫⁻ z : V (nd X), ∏ τ, h (zOf X z τ) = ∫⁻ y, G y` using `(GlobalTheory.volume_preserving_ofLp_complex (Fin (nd X))).lintegral_comp hGm`.

Use `set K : (X.Ψ → Low r → ℂ) → ℝ≥0∞ := fun g => ∏ τ, h (g τ) with hK`. Establish `hKm : Measurable K` using `Finset.measurable_prod _ fun τ _ => hh.comp (measurable_pi_apply τ)`. Establish `s2 : ∫⁻ y, G y = ∫⁻ f : Ent X → ℂ, K (MeasurableEquiv.curry X.Ψ (Low r) ℂ f)`. Use `((volume_measurePreserving_piCongrLeft (fun _ => ℂ) e).lintegral_comp hGm).symm.trans (lintegral_congr fun f => ?_)` and prove the remaining obligations. Simplify using `only [hG, hK, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]`.

Both sides reduce to the same expression. Establish `s3 : ∫⁻ f : Ent X → ℂ, K (MeasurableEquiv.curry X.Ψ (Low r) ℂ f) = ∫⁻ g, K g` using `(measurePreserving_curry_lowCoord X.Ψ (Low r)).lintegral_comp hKm`. Rewrite using `[s1, s2, s3, hK, volume_pi]`. Conclude with `GlobalTheory.RestrMeas.lintegral_fintype_prod_eq_prod fun _ => hh.aemeasurable`.
-/
theorem lintegral_prod_zOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (h : (Low r → ℂ) → ℝ≥0∞), Measurable h → ∫⁻ z, ∏ τ, h (zOf X z τ) = ∏ _τ : X.Ψ, ∫⁻ w, h w := by
  intro E _ _ _ r X h hh
  set e := Fintype.equivFin (Ent X) with he
  set G : (Fin (nd X) → ℂ) → ℝ≥0∞ := fun y => ∏ τ, h (fun p => y (e ⟨τ, p⟩)) with hG
  have hGm : Measurable G :=
    Finset.measurable_prod _ fun τ _ => hh.comp (measurable_pi_lambda _ fun p => measurable_pi_apply _)
  have s1 : ∫⁻ z : V (nd X), ∏ τ, h (zOf X z τ) = ∫⁻ y, G y :=
    (GlobalTheory.volume_preserving_ofLp_complex (Fin (nd X))).lintegral_comp hGm
  set K : (X.Ψ → Low r → ℂ) → ℝ≥0∞ := fun g => ∏ τ, h (g τ) with hK
  have hKm : Measurable K := Finset.measurable_prod _ fun τ _ => hh.comp (measurable_pi_apply τ)
  have s2 : ∫⁻ y, G y = ∫⁻ f : Ent X → ℂ, K (MeasurableEquiv.curry X.Ψ (Low r) ℂ f) := by
    refine ((volume_measurePreserving_piCongrLeft (fun _ => ℂ) e).lintegral_comp hGm).symm.trans
      (lintegral_congr fun f => ?_)
    simp only [hG, hK, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
    rfl
  have s3 : ∫⁻ f : Ent X → ℂ, K (MeasurableEquiv.curry X.Ψ (Low r) ℂ f) = ∫⁻ g, K g :=
    (measurePreserving_curry_lowCoord X.Ψ (Low r)).lintegral_comp hKm
  rw [s1, s2, s3, hK, volume_pi]
  exact GlobalTheory.RestrMeas.lintegral_fintype_prod_eq_prod fun _ => hh.aemeasurable

end

end GlobalTheory.IntBall
