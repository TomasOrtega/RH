import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDensityPushforwardIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubsetPartitionNull
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.ArchLim

/- English proof (translation)
Establish `h1 : MeasurePreserving (fun z : V n => z.ofLp) volume volume` using `GlobalTheory.volume_preserving_ofLp_complex (Fin n)`. Establish `h2` using `h1.prod (MeasurePreserving.id (volume : Measure (Low r → ℂ)))`. Establish `h3` using `(volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin n ⊕ Low r => ℂ)).comp h2`. Establish `h4` using `(volume_preserving_arrowCongr' ε.symm (MeasurableEquiv.refl ℂ) (MeasurePreserving.id volume)).comp h3`. Establish `h5 : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin D → ℂ)) volume volume` using `MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin D → ℂ)).symm (GlobalTheory.volume_preserving_ofLp_complex (Fin D))`.

Establish `h6` using `h5.comp h4`. Establish `e : (fun x : V n × (Low r → ℂ) => pt ε x.1 x.2) = (⇑(MeasurableEquiv.toLp 2 (Fin D → ℂ)) ∘ ⇑(MeasurableEquiv.arrowCongr' ε.symm (MeasurableEquiv.refl ℂ)) ∘ ⇑(MeasurableEquiv.sumPiEquivProdPi fun _ : Fin n ⊕ Low r => ℂ).symm ∘ Prod.map (fun z : V n => z.ofLp) id)`. Use function extensionality and compare the values at `x`. Use extensionality with `i`. Express the relevant statement in the definitionally equal form `Sum.elim (fun a => x.1.ofLp a) x.2 (ε i) = (Equiv.sumPiEquivProdPi fun _ : Fin n ⊕ Low r => ℂ).symm (x.1.ofLp, x.2) (ε i)`.

Apply the tactic sequence `cases ε i <;> rfl`. Rewrite using `[e]`. Conclude with `h6`.
-/
theorem measurePreserving_pt_sum {n r D : ℕ} (ε : Fin D ≃ Fin n ⊕ Low r) :
    MeasurePreserving (fun x : V n × (Low r → ℂ) => pt ε x.1 x.2) volume volume := by
  have h1 : MeasurePreserving (fun z : V n => z.ofLp) volume volume :=
    GlobalTheory.volume_preserving_ofLp_complex (Fin n)
  have h2 := h1.prod (MeasurePreserving.id (volume : Measure (Low r → ℂ)))
  have h3 := (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin n ⊕ Low r => ℂ)).comp h2
  have h4 := (volume_preserving_arrowCongr' ε.symm (MeasurableEquiv.refl ℂ) (MeasurePreserving.id volume)).comp h3
  have h5 : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin D → ℂ)) volume volume :=
    MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin D → ℂ)).symm
      (GlobalTheory.volume_preserving_ofLp_complex (Fin D))
  have h6 := h5.comp h4
  have e : (fun x : V n × (Low r → ℂ) => pt ε x.1 x.2) = (⇑(MeasurableEquiv.toLp 2 (Fin D → ℂ)) ∘
      ⇑(MeasurableEquiv.arrowCongr' ε.symm (MeasurableEquiv.refl ℂ)) ∘
        ⇑(MeasurableEquiv.sumPiEquivProdPi fun _ : Fin n ⊕ Low r => ℂ).symm ∘ Prod.map (fun z : V n => z.ofLp) id) := by
    funext x
    ext i
    change Sum.elim (fun a => x.1.ofLp a) x.2 (ε i) =
      (Equiv.sumPiEquivProdPi fun _ : Fin n ⊕ Low r => ℂ).symm (x.1.ofLp, x.2) (ε i)
    cases ε i <;> rfl
  rw [e]
  exact h6

/- English proof (translation)
Introduce `n r D ε K H hK hH`. Establish `hb : Measurable (base ε)`. Establish `: Continuous (base ε)`. Unfold `base`. Use `fun_prop`.

Conclude with `this.measurable`. Establish `hm` using `(measurePreserving_pt_sum ε).restrict_preimage (hb hK)`. Establish `hs : (fun x : V n × (Low r → ℂ) => pt ε x.1 x.2) ⁻¹' (base ε ⁻¹' K) = K ×ˢ Set.univ`. Use extensionality with `x`. Simplify using `[base_pt]`.

Rewrite `hm` using `[hs, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]`. Establish `hi : AEMeasurable (fun x : V n × (Low r → ℂ) => H (pt ε x.1 x.2)) ((volume.restrict K).prod volume)` using `hH.comp_quasiMeasurePreserving hm.quasiMeasurePreserving`. Use `⟨?_, hi.lintegral_prod_right'⟩` and prove the remaining obligations. Rewrite using `[← hm.map_eq, lintegral_map' (by rw [hm.map_eq]; exact hH) hm.measurable.aemeasurable, lintegral_prod _ hi]`.
-/
theorem setLIntegral_base_eq : ∀ (n r D : ℕ) (ε : Fin D ≃ Fin n ⊕ Low r) (K : Set (V n)) (H : V D → ℝ≥0∞), MeasurableSet K → AEMeasurable H (volume.restrict (base ε ⁻¹' K)) → (∫⁻ v in base ε ⁻¹' K, H v = ∫⁻ u in K, ∫⁻ x : Low r → ℂ, H (pt ε u x)) ∧ AEMeasurable (fun u => ∫⁻ x : Low r → ℂ, H (pt ε u x)) (volume.restrict K) := by
  intro n r D ε K H hK hH
  have hb : Measurable (base ε) := by
    have : Continuous (base ε) := by
      unfold base
      fun_prop
    exact this.measurable
  have hm := (measurePreserving_pt_sum ε).restrict_preimage (hb hK)
  have hs : (fun x : V n × (Low r → ℂ) => pt ε x.1 x.2) ⁻¹' (base ε ⁻¹' K) = K ×ˢ Set.univ := by
    ext x
    simp [base_pt]
  rw [hs, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ] at hm
  have hi : AEMeasurable (fun x : V n × (Low r → ℂ) => H (pt ε x.1 x.2)) ((volume.restrict K).prod volume) :=
    hH.comp_quasiMeasurePreserving hm.quasiMeasurePreserving
  refine ⟨?_, hi.lintegral_prod_right'⟩
  rw [← hm.map_eq, lintegral_map' (by rw [hm.map_eq]; exact hH) hm.measurable.aemeasurable, lintegral_prod _ hi]

end GlobalTheory.ArchLim
