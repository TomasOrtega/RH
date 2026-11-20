import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertSatakeParametersEqOfIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosetsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegralStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosetsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNonsplitPlaceWithInertDatum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertDatumAtInert

open scoped TensorProduct

/- English proof (translation)
Use `set v := Pp.under (𝓞 (maximalRealSubfield E)) with hv`. Establish `hunder : Pp.under (𝓞 (maximalRealSubfield E)) = v` using `rfl`. Take `⟨c, hc, -⟩` from `GlobalTheory.LFun.InertChart.existsUnique_isConjAt (IsCMField.complexConj E).toAlgHom hw hunder`. Take `⟨ϖ, hU⟩` from `GlobalTheory.LFun.InertChart.exists_isUnramInv (GlobalTheory.InertDatumExist.isCMExt E) hw hc`. Take `⟨k, hk, hke⟩` from `GlobalTheory.LFun.InertChart.exists_congr_antiJ (n := n) hU (B := 1) (one_mem _) (by simp [Formalism.UG.cT, Matrix.map_one])`.

Establish `hO : Formalism.UG.Ov E Pp = Formalism.UG.intL (Pp.adicCompletion E)` using `Subring.ext fun _ => Iff.rfl`. Set `e` to `(Algebra.TensorProduct.comm (maximalRealSubfield E) E (v.adicCompletion (maximalRealSubfield E))).toRingEquiv.trans (GlobalTheory.LFun.InertChart.complEquiv hw hunder)`. Use `⟨⟨e, c, ϖ, k, ?_, hU, ?_, ?_, ?_⟩⟩` and prove the remaining obligations. Introduce `x show GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _ (Formalism.UG.sigR (IsCMField.complexConj E).toAlgHom _ x)) = c (GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _ x))`. Rewrite using `[hc]`.

Use `congr 1`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => rfl`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.

Introduce `x`. Rewrite using `[GlobalTheory.InertDatumExist.mem_tensInt_iff, GlobalTheory.LFun.InertChart.mem_intLoc_iff hw hunder, hO]`. Conclude with `Iff.rfl`. Rewrite using `[← hO]`. Conclude with `hk`.

Simplify using `using hke`.
-/
theorem exists_inertDatum_of_isInertAt (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (Pp : HeightOneSpectrum (𝓞 E))
    (hw : Formalism.UG.IsInertAt (maximalRealSubfield E) E (Pp.under (𝓞 (maximalRealSubfield E))) Pp) :
    Nonempty (InertDatum E n (Pp.under (𝓞 (maximalRealSubfield E))) Pp) := by
  classical
  set v := Pp.under (𝓞 (maximalRealSubfield E)) with hv
  have hunder : Pp.under (𝓞 (maximalRealSubfield E)) = v := rfl
  obtain ⟨c, hc, -⟩ := GlobalTheory.LFun.InertChart.existsUnique_isConjAt
    (IsCMField.complexConj E).toAlgHom hw hunder
  obtain ⟨ϖ, hU⟩ := GlobalTheory.LFun.InertChart.exists_isUnramInv (GlobalTheory.InertDatumExist.isCMExt E) hw hc
  obtain ⟨k, hk, hke⟩ := GlobalTheory.LFun.InertChart.exists_congr_antiJ (n := n) hU (B := 1) (one_mem _)
    (by simp [Formalism.UG.cT, Matrix.map_one])
  have hO : Formalism.UG.Ov E Pp = Formalism.UG.intL (Pp.adicCompletion E) := Subring.ext fun _ => Iff.rfl
  let e := (Algebra.TensorProduct.comm (maximalRealSubfield E) E
    (v.adicCompletion (maximalRealSubfield E))).toRingEquiv.trans (GlobalTheory.LFun.InertChart.complEquiv hw hunder)
  refine ⟨⟨e, c, ϖ, k, ?_, hU, ?_, ?_, ?_⟩⟩
  · intro x
    show GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _
        (Formalism.UG.sigR (IsCMField.complexConj E).toAlgHom _ x)) =
      c (GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _ x))
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

/- English proof (translation)
Introduce `D hF Pp hI`. Rewrite `hI` using `[hF]`. Take `⟨Dv⟩` from `exists_inertDatum_of_isInertAt D.host.E D.R.nV Pp hI`. Conclude with `⟨_, Dv, rfl⟩`.
-/
theorem main : ∀ (D : D7), D.host.F = maximalRealSubfield D.host.E → ∀ (Pp : HeightOneSpectrum (𝓞 D.host.E)),
    Formalism.UG.IsInertAt D.host.F D.host.E (Pp.under (𝓞 D.host.F)) Pp →
    ∃ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) (_ : InertDatum D.host.E D.R.nV v Pp),
      NG.OverPl Pp v := by
  intro D hF Pp hI
  rw [hF] at hI
  obtain ⟨Dv⟩ := exists_inertDatum_of_isInertAt D.host.E D.R.nV Pp hI
  exact ⟨_, Dv, rfl⟩

end GlobalTheory.InertDatumAtInert

end
