import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDvrFrobeniusLift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramifiedNonsplitExistsConjInvolutionUniformise
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNonsplitPlaceWithInertDatum
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertDatumGiven

open scoped TensorProduct

/- English proof (translation)
Establish `h : Filter.Tendsto s (nhds 0) (nhds 0)`. Rewrite using `[(Valued.hasBasis_nhds_zero K Γ₀).tendsto_iff (Valued.hasBasis_nhds_zero K Γ₀)]`. Introduce `γ _`. Use `⟨γ, trivial, fun x hx => ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding] at hx ⊢`.

Rewrite using `[hs]` and apply the resulting hypothesis. Conclude with `continuous_of_continuousAt_zero s (by simpa [ContinuousAt] using h)`.
-/
theorem continuous_of_valued_eq {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (s : K →+* K) (hs : ∀ x, Valued.v (s x) = Valued.v x) : Continuous s := by
  have h : Filter.Tendsto s (nhds 0) (nhds 0) := by
    rw [(Valued.hasBasis_nhds_zero K Γ₀).tendsto_iff (Valued.hasBasis_nhds_zero K Γ₀)]
    intro γ _
    refine ⟨γ, trivial, fun x hx => ?_⟩
    simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding] at hx ⊢
    rwa [hs]
  exact continuous_of_continuousAt_zero s (by simpa [ContinuousAt] using h)

/- English proof (translation)
Introduce `L _ _ _ n v w hov hu hns s ϖ hs hU`. Establish `hunder : w.under (𝓞 (maximalRealSubfield L)) = v` using `HeightOneSpectrum.ext hov`. Establish `hw : Formalism.UG.IsInertAt (maximalRealSubfield L) L v w`. Establish `h` using `GlobalTheory.InertPlaceConj.isInertAt_of_not_split w hu hns`. Rewrite `h` using `[hunder]`. Then use the resulting hypothesis.

Take `⟨c, hc, -⟩` from `GlobalTheory.LFun.InertChart.existsUnique_isConjAt (IsCMField.complexConj L).toAlgHom hw hunder`. Take `⟨ϖ', hU'⟩` from `GlobalTheory.LFun.InertChart.exists_isUnramInv (GlobalTheory.InertDatumExist.isCMExt L) hw hc`. Establish `hsc : s = c`. Apply `DFunLike.coe_injective` to reduce the goal to its premises. Use `GlobalTheory.UnramCompletion.ringHom_ext_of_continuous w (continuous_of_valued_eq s hU.2.1) (continuous_of_valued_eq c hU'.2.1) fun k => ?_` and prove the remaining obligations.

Rewrite using `[hs, GlobalTheory.LFun.InertChart.conj_algebraMap hc]`. Both sides reduce to the same expression. Substitute `hsc` using the available equality. Take `⟨k, hk, hke⟩` from `GlobalTheory.LFun.InertChart.exists_congr_antiJ (n := n) hU (B := 1) (one_mem _) (by simp [Formalism.UG.cT, Matrix.map_one])`. Establish `hO : Formalism.UG.Ov L w = Formalism.UG.intL (w.adicCompletion L)` using `Subring.ext fun _ => Iff.rfl`.

Set `e` to `(Algebra.TensorProduct.comm (maximalRealSubfield L) L (v.adicCompletion (maximalRealSubfield L))).toRingEquiv.trans (GlobalTheory.LFun.InertChart.complEquiv hw hunder)`. Use `⟨⟨e, s, ϖ, k, ?_, hU, ?_, ?_, ?_⟩, rfl, rfl⟩` and prove the remaining obligations. Introduce `x show GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _ (Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom _ x)) = s (GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _ x))`. Rewrite using `[hc]`. Use `congr 1`.

Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => rfl`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Introduce `x`.

Rewrite using `[GlobalTheory.InertDatumExist.mem_tensInt_iff, GlobalTheory.LFun.InertChart.mem_intLoc_iff hw hunder, hO]`. Conclude with `Iff.rfl`. Rewrite using `[← hO]`. Conclude with `hk`. Simplify using `using hke`.
-/
theorem exists_inertDatum_of : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal → ¬ IsSplitAt w → ∀ (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L), (∀ x : L, s (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → Formalism.UG.IsUnramInv ϖ s (Formalism.UG.qV (maximalRealSubfield L) v) → ∃ Dv : InertDatum L n v w, Dv.σw = s ∧ Dv.ϖ = ϖ := by
  intro L _ _ _ n v w hov hu hns s ϖ hs hU
  classical
  have hunder : w.under (𝓞 (maximalRealSubfield L)) = v := HeightOneSpectrum.ext hov
  have hw : Formalism.UG.IsInertAt (maximalRealSubfield L) L v w := by
    have h := GlobalTheory.InertPlaceConj.isInertAt_of_not_split w hu hns
    rwa [hunder] at h
  obtain ⟨c, hc, -⟩ := GlobalTheory.LFun.InertChart.existsUnique_isConjAt
    (IsCMField.complexConj L).toAlgHom hw hunder
  obtain ⟨ϖ', hU'⟩ := GlobalTheory.LFun.InertChart.exists_isUnramInv (GlobalTheory.InertDatumExist.isCMExt L) hw hc
  have hsc : s = c := by
    apply DFunLike.coe_injective
    refine GlobalTheory.UnramCompletion.ringHom_ext_of_continuous w (continuous_of_valued_eq s hU.2.1)
      (continuous_of_valued_eq c hU'.2.1) fun k => ?_
    rw [hs, GlobalTheory.LFun.InertChart.conj_algebraMap hc]
    rfl
  subst hsc
  obtain ⟨k, hk, hke⟩ := GlobalTheory.LFun.InertChart.exists_congr_antiJ (n := n) hU (B := 1) (one_mem _)
    (by simp [Formalism.UG.cT, Matrix.map_one])
  have hO : Formalism.UG.Ov L w = Formalism.UG.intL (w.adicCompletion L) := Subring.ext fun _ => Iff.rfl
  let e := (Algebra.TensorProduct.comm (maximalRealSubfield L) L
    (v.adicCompletion (maximalRealSubfield L))).toRingEquiv.trans (GlobalTheory.LFun.InertChart.complEquiv hw hunder)
  refine ⟨⟨e, s, ϖ, k, ?_, hU, ?_, ?_, ?_⟩, rfl, rfl⟩
  · intro x
    show GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _
        (Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom _ x)) =
      s (GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _ x))
    rw [hc]
    congr 1
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  · intro x
    rw [GlobalTheory.InertDatumExist.mem_tensInt_iff, GlobalTheory.LFun.InertChart.mem_intLoc_iff hw hunder, hO]
    exact Iff.rfl
  · rw [← hO]; exact hk
  · simpa using hke

end GlobalTheory.InertDatumGiven

end
