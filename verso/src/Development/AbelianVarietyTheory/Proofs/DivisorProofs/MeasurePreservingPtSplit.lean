import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2

noncomputable def ptEquiv (n d : ℕ) (J : Type) [Fintype J] (ε : Fin n ≃ Fin d ⊕ J) : V d × (J → ℂ) ≃ᵐ V n :=
  ((MeasurableEquiv.prodCongr (MeasurableEquiv.toLp 2 (Fin d → ℂ)).symm (MeasurableEquiv.refl (J → ℂ))).trans
    (MeasurableEquiv.sumPiEquivProdPi fun _ : Fin d ⊕ J => ℂ).symm).trans
    ((MeasurableEquiv.arrowCongr' ε.symm (MeasurableEquiv.refl ℂ)).trans (MeasurableEquiv.toLp 2 (Fin n → ℂ)))

/- English proof (translation)
Use extensionality with `i`. Express the relevant statement in the definitionally equal form `(Equiv.sumPiEquivProdPi fun _ : Fin d ⊕ J => ℂ).symm (x.1.ofLp, x.2) (ε i) = Sum.elim (fun a => x.1.ofLp a) x.2 (ε i)`. Apply the tactic sequence `cases ε i <;> rfl`.
-/
theorem ptEquiv_apply (n d : ℕ) (J : Type) [Fintype J] (ε : Fin n ≃ Fin d ⊕ J) (x : V d × (J → ℂ)) :
    ptEquiv n d J ε x = pt ε x.1 x.2 := by
  ext i
  change (Equiv.sumPiEquivProdPi fun _ : Fin d ⊕ J => ℂ).symm (x.1.ofLp, x.2) (ε i) = Sum.elim (fun a => x.1.ofLp a) x.2 (ε i)
  cases ε i <;> rfl

/- English proof (translation)
Introduce `n d J _ ε`. Establish `e : (fun x : V d × (J → ℂ) => pt ε x.1 x.2) = ⇑(ptEquiv n d J ε)`. Use function extensionality and compare the values at `x`. Conclude with `(ptEquiv_apply n d J ε x).symm`. Rewrite using `[e]`.

Use `⟨?_, (ptEquiv n d J ε).measurableEmbedding⟩` and prove the remaining obligations. Establish `h1 : MeasurePreserving (fun z : V d => z.ofLp) volume volume` using `volume_preserving_ofLp_complex (Fin d)`. Establish `h2` using `h1.prod (MeasurePreserving.id (volume : Measure (J → ℂ)))`. Establish `h3` using `(volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin d ⊕ J => ℂ)).comp h2`. Establish `h4` using `(volume_preserving_arrowCongr' ε.symm (MeasurableEquiv.refl ℂ) (MeasurePreserving.id volume)).comp h3`.

Establish `h5 : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin n → ℂ)) volume volume` using `MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin n → ℂ)).symm (volume_preserving_ofLp_complex (Fin n))`. Conclude with `h5.comp h4`.
-/
theorem measurePreserving_pt_split : ∀ (n d : ℕ) (J : Type) [Fintype J] (ε : Fin n ≃ Fin d ⊕ J),
    MeasurePreserving (fun x : V d × (J → ℂ) => pt ε x.1 x.2) volume volume ∧
      MeasurableEmbedding (fun x : V d × (J → ℂ) => pt ε x.1 x.2) := by
  intro n d J _ ε
  have e : (fun x : V d × (J → ℂ) => pt ε x.1 x.2) = ⇑(ptEquiv n d J ε) := by
    funext x; exact (ptEquiv_apply n d J ε x).symm
  rw [e]
  refine ⟨?_, (ptEquiv n d J ε).measurableEmbedding⟩
  have h1 : MeasurePreserving (fun z : V d => z.ofLp) volume volume := volume_preserving_ofLp_complex (Fin d)
  have h2 := h1.prod (MeasurePreserving.id (volume : Measure (J → ℂ)))
  have h3 := (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin d ⊕ J => ℂ)).comp h2
  have h4 := (volume_preserving_arrowCongr' ε.symm (MeasurableEquiv.refl ℂ) (MeasurePreserving.id volume)).comp h3
  have h5 : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin n → ℂ)) volume volume :=
    MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin n → ℂ)).symm (volume_preserving_ofLp_complex (Fin n))
  exact h5.comp h4

end GlobalTheory.FlagCell2
