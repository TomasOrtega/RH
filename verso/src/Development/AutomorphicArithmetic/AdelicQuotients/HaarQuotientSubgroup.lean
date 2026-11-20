import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SelmerRankBoundLaurent
import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.NormEx
import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotEq
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open MeasureTheory

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ H hH μ j ν hp Φ hΦ hi`. Use `haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)`. Take `⟨ρ₀, -, hρ₀, -⟩` from `normEx H T μ j ν hp`. Establish `hemb : MeasurableEmbedding (Subtype.val : H → G)` using `MeasurableEmbedding.subtype_coe hH.measurableSet`.

Establish `hinj : Function.Injective (Subtype.val : H → G)` using `Subtype.val_injective`. Establish `hex : ∃ ρ, IsNormAlong (fun x : H => (x : G)) (fun t => (j t : G)) ν ρ`. Use `⟨Function.extend Subtype.val (fun x : H => (ρ₀ x : ENNReal)) 0, hemb.measurable_extend hρ₀.1 measurable_const, fun x => ?_⟩` and prove the remaining obligations. Establish `e : ∀ t, Function.extend Subtype.val (fun x : H => (ρ₀ x : ENNReal)) 0 ((j t : G) * (x : G)) = (ρ₀ (j t * x) : ENNReal)` using `fun t => by`. Rewrite using `[← Subgroup.coe_mul]`.

Conclude with `hinj.extend_apply _ _ _`. Simplify using `only [e]`. Conclude with `hρ₀.2 x`. Unfold `quotInt`. Rewrite using `[dif_pos hex]`.

Establish `hn : IsNrm j ν (fun x : H => hex.choose (x : G))` using `⟨hex.choose_spec.1.comp measurable_subtype_coe, fun x => by`. Simplify `hex.choose_spec.2 x⟩` using `only [Subgroup.coe_mul]`. Conclude with `((quotEq H T μ j ν hp Φ hΦ hi _ hn).2.2).symm`.
-/
theorem UpperTheory.haar_quotient_subgroup :
    QSub := by
  intro G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ H hH μ j ν hp Φ hΦ hi
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  obtain ⟨ρ₀, -, hρ₀, -⟩ := normEx H T μ j ν hp
  have hemb : MeasurableEmbedding (Subtype.val : H → G) := MeasurableEmbedding.subtype_coe hH.measurableSet
  have hinj : Function.Injective (Subtype.val : H → G) := Subtype.val_injective
  have hex : ∃ ρ, IsNormAlong (fun x : H => (x : G)) (fun t => (j t : G)) ν ρ := by
    refine ⟨Function.extend Subtype.val (fun x : H => (ρ₀ x : ENNReal)) 0,
      hemb.measurable_extend hρ₀.1 measurable_const, fun x => ?_⟩
    have e : ∀ t, Function.extend Subtype.val (fun x : H => (ρ₀ x : ENNReal)) 0 ((j t : G) * (x : G))
        = (ρ₀ (j t * x) : ENNReal) := fun t => by
      rw [← Subgroup.coe_mul]
      exact hinj.extend_apply _ _ _
    simp only [e]
    exact hρ₀.2 x
  unfold quotInt
  rw [dif_pos hex]
  have hn : IsNrm j ν (fun x : H => hex.choose (x : G)) :=
    ⟨hex.choose_spec.1.comp measurable_subtype_coe, fun x => by
      simpa only [Subgroup.coe_mul] using hex.choose_spec.2 x⟩
  exact ((quotEq H T μ j ν hp Φ hΦ hi _ hn).2.2).symm
