import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace
import Development.DiscreteGroups.GlobalIrreducibility.ExistsUniformizerValuation

open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

/- English proof (translation)
Introduce `E _ _ _ _ ϖ hϖ ψ hψ hψ1`. Take `⟨c, hc⟩` from `DiscreteGroups.sglob.DzType.exists_hasConductor_of_continuous_ne_one ψ hψ hψ1`. Establish `h1 : ord E ϖ = 1` using `ord_eq_one hϖ`. Establish `hz : ∀ d : ℤ, ord E (ϖ ^ d) = d`. Introduce `d`.

Consider the cases of `d with`. Consider the case `ofNat n => simp [DiscreteGroups.sglob.DzType.ord_pow_bis, h1]`. Consider the case `negSucc n`. Rewrite using `[zpow_negSucc, DiscreteGroups.sglob.DzType.ord_inv_eq_neg_ord, DiscreteGroups.sglob.DzType.ord_pow_bis, h1, Int.negSucc_eq]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hv : valuation E ((ϖ ^ ord E c : Eˣ) : E) = valuation E (c : E)` using `le_antisymm ((DiscreteGroups.sglob.DzType.valuation_le_iff_ord_le _ _).2 (by rw [hz])) ((DiscreteGroups.sglob.DzType.valuation_le_iff_ord_le _ _).2 (by rw [hz]))`. Use `⟨ord E c, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[hv]`. Conclude with `hc x`.
-/
theorem UpperTheory.V.Z.Tf.L4.condEx :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (ϖ : Eˣ), valuation E (ϖ : E) = uniformizer E → ∀ ψ : AddChar E Circle, Continuous ψ → ψ ≠ 1 → ∃ d : ℤ, HasConductor ψ (ϖ ^ d) := by
  intro E _ _ _ _ ϖ hϖ ψ hψ hψ1
  obtain ⟨c, hc⟩ := DiscreteGroups.sglob.DzType.exists_hasConductor_of_continuous_ne_one ψ hψ hψ1
  have h1 : ord E ϖ = 1 := ord_eq_one hϖ
  have hz : ∀ d : ℤ, ord E (ϖ ^ d) = d := by
    intro d
    cases d with
    | ofNat n => simp [DiscreteGroups.sglob.DzType.ord_pow_bis, h1]
    | negSucc n =>
      rw [zpow_negSucc, DiscreteGroups.sglob.DzType.ord_inv_eq_neg_ord, DiscreteGroups.sglob.DzType.ord_pow_bis, h1, Int.negSucc_eq]
      push_cast; ring
  have hv : valuation E ((ϖ ^ ord E c : Eˣ) : E) = valuation E (c : E) :=
    le_antisymm ((DiscreteGroups.sglob.DzType.valuation_le_iff_ord_le _ _).2 (by rw [hz]))
      ((DiscreteGroups.sglob.DzType.valuation_le_iff_ord_le _ _).2 (by rw [hz]))
  refine ⟨ord E c, fun x => ?_⟩
  rw [hv]
  exact hc x
