import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertHeckeOperatorIndepOfInertDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertOfUnramifiedIsometricInvolution
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInertDatumOfInvolutionUniformizer
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical
noncomputable section

namespace GlobalTheory.InertTransferCanon

/- English proof (translation)
Introduce `L _ _ _ n F v w hov Dv hs`. Take `⟨hu, hns, -⟩` from `GlobalTheory.InertOfUnramInv.inert_of_isUnramInv L v w hov Dv.σw Dv.ϖ _ hs Dv.unram`. Establish `hunder : w.under (𝓞 (maximalRealSubfield L)) = v` using `HeightOneSpectrum.ext hov`. Establish `hw : Formalism.UG.IsInertAt (maximalRealSubfield L) L v w`. Establish `h` using `GlobalTheory.InertPlaceConj.isInertAt_of_not_split w hu hns`.

Rewrite `h` using `[hunder]`. Then use the resulting hypothesis. Take `⟨c, hc, -⟩` from `GlobalTheory.LFun.InertChart.existsUnique_isConjAt (IsCMField.complexConj L).toAlgHom hw hunder`. Take `⟨ϖ', hU'⟩` from `GlobalTheory.LFun.InertChart.exists_isUnramInv (GlobalTheory.InertDatumExist.isCMExt L) hw hc`. Establish `hsc : Dv.σw = c`. Apply `DFunLike.coe_injective` to reduce the goal to its premises.

Use `GlobalTheory.UnramCompletion.ringHom_ext_of_continuous w (GlobalTheory.InertDatumGiven.continuous_of_valued_eq _ Dv.unram.2.1) (GlobalTheory.InertDatumGiven.continuous_of_valued_eq c hU'.2.1) fun k => ?_` and prove the remaining obligations. Rewrite using `[hs, GlobalTheory.LFun.InertChart.conj_algebraMap hc]`. Both sides reduce to the same expression. Establish `hO : Formalism.UG.Ov L w = Formalism.UG.intL (w.adicCompletion L)` using `Subring.ext fun _ => Iff.rfl`. Set `e` to `(Algebra.TensorProduct.comm (maximalRealSubfield L) L (v.adicCompletion (maximalRealSubfield L))).toRingEquiv.trans (GlobalTheory.LFun.InertChart.complEquiv hw hunder)`.

Take `⟨i, hic, hi⟩` from `F.right w v hov`. Establish `hiy : ∀ y : maximalRealSubfield L, i (algebraMap _ (v.adicCompletion (maximalRealSubfield L)) y) = GlobalTheory.LFun.complMap hunder (algebraMap _ (v.adicCompletion (maximalRealSubfield L)) y)`. Introduce `y`. Rewrite using `[GlobalTheory.LFun.complMap_algebraMap]`. Establish `h1` using `hi (algebraMap (maximalRealSubfield L) _ y)`.

Establish `h2 : (1 : L) ⊗ₜ[maximalRealSubfield L] (algebraMap (maximalRealSubfield L) (FiniteAdeleRing (𝓞 (maximalRealSubfield L)) (maximalRealSubfield L)) y) = (algebraMap (maximalRealSubfield L) L y) ⊗ₜ 1`. Rewrite using `[Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']`. Rewrite `h1` using `[h2, F.left]`. Conclude with `h1.symm`. Establish `hieq : (i : v.adicCompletion (maximalRealSubfield L) → w.adicCompletion L) = GlobalTheory.LFun.complMap hunder` using `(HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield L) v).equalizer hic (GlobalTheory.LFun.InertChart.continuous_complMap hunder) (funext hiy)`.

Use `⟨e, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x show GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _ (Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom _ x)) = Dv.σw (GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _ x))`. Rewrite using `[hsc, hc]`. Use `congr 1`. Proceed by induction on `x using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul a b => rfl`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Introduce `x`. Rewrite using `[GlobalTheory.InertDatumExist.mem_tensInt_iff, GlobalTheory.LFun.InertChart.mem_intLoc_iff hw hunder, hO]`.

Conclude with `Iff.rfl`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.

Both sides reduce to the same expression. Consider the case `tmul x a`. Establish `hk : F.κ (x ⊗ₜ a) = F.κ (x ⊗ₜ 1) * F.κ (1 ⊗ₜ a)`. Rewrite using `[← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Use `show GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _ (compAt L v (x ⊗ₜ a))) = _`.

Establish `hm : ∀ p q : FiniteAdeleRing (𝓞 L) L, (p * q) w = p w * q w` using `fun _ _ => rfl`. Rewrite using `[hk, F.left, hm, hi, hieq]`. Use `show GlobalTheory.LFun.complMap hunder (a v) * algebraMap L _ x = _`. Rewrite using `[mul_comm]`. Both sides reduce to the same expression.
-/
theorem exists_canonical_equiv : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ Dv : InertDatum L n v w, (∀ x : L, Dv.σw (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → ∃ e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) ≃+* w.adicCompletion L, (∀ x, e (Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (v.adicCompletion (maximalRealSubfield L)) x) = Dv.σw (e x)) ∧ (∀ x, x ∈ Formalism.UG.tensInt (F := maximalRealSubfield L) (v.adicCompletion (maximalRealSubfield L)) (Formalism.UG.intOE L) (Formalism.UG.Ov (maximalRealSubfield L) v) ↔ e x ∈ Formalism.UG.intL (w.adicCompletion L)) ∧ ∀ z : AL L, e (compAt L v z) = F.κ z w := by
  intro L _ _ _ n F v w hov Dv hs
  obtain ⟨hu, hns, -⟩ := GlobalTheory.InertOfUnramInv.inert_of_isUnramInv L v w hov Dv.σw Dv.ϖ _ hs Dv.unram
  have hunder : w.under (𝓞 (maximalRealSubfield L)) = v := HeightOneSpectrum.ext hov
  have hw : Formalism.UG.IsInertAt (maximalRealSubfield L) L v w := by
    have h := GlobalTheory.InertPlaceConj.isInertAt_of_not_split w hu hns
    rwa [hunder] at h
  obtain ⟨c, hc, -⟩ := GlobalTheory.LFun.InertChart.existsUnique_isConjAt
    (IsCMField.complexConj L).toAlgHom hw hunder
  obtain ⟨ϖ', hU'⟩ := GlobalTheory.LFun.InertChart.exists_isUnramInv (GlobalTheory.InertDatumExist.isCMExt L) hw hc
  have hsc : Dv.σw = c := by
    apply DFunLike.coe_injective
    refine GlobalTheory.UnramCompletion.ringHom_ext_of_continuous w
      (GlobalTheory.InertDatumGiven.continuous_of_valued_eq _ Dv.unram.2.1)
      (GlobalTheory.InertDatumGiven.continuous_of_valued_eq c hU'.2.1) fun k => ?_
    rw [hs, GlobalTheory.LFun.InertChart.conj_algebraMap hc]
    rfl
  have hO : Formalism.UG.Ov L w = Formalism.UG.intL (w.adicCompletion L) := Subring.ext fun _ => Iff.rfl
  let e := (Algebra.TensorProduct.comm (maximalRealSubfield L) L
    (v.adicCompletion (maximalRealSubfield L))).toRingEquiv.trans (GlobalTheory.LFun.InertChart.complEquiv hw hunder)

  obtain ⟨i, hic, hi⟩ := F.right w v hov
  have hiy : ∀ y : maximalRealSubfield L,
      i (algebraMap _ (v.adicCompletion (maximalRealSubfield L)) y) =
        GlobalTheory.LFun.complMap hunder (algebraMap _ (v.adicCompletion (maximalRealSubfield L)) y) := by
    intro y
    rw [GlobalTheory.LFun.complMap_algebraMap]
    have h1 := hi (algebraMap (maximalRealSubfield L) _ y)
    have h2 : (1 : L) ⊗ₜ[maximalRealSubfield L]
        (algebraMap (maximalRealSubfield L) (FiniteAdeleRing (𝓞 (maximalRealSubfield L)) (maximalRealSubfield L)) y) =
        (algebraMap (maximalRealSubfield L) L y) ⊗ₜ 1 := by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul']
    rw [h2, F.left] at h1
    exact h1.symm
  have hieq : (i : v.adicCompletion (maximalRealSubfield L) → w.adicCompletion L) = GlobalTheory.LFun.complMap hunder :=
    (HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield L) v).equalizer hic
      (GlobalTheory.LFun.InertChart.continuous_complMap hunder) (funext hiy)
  refine ⟨e, ?_, ?_, ?_⟩
  · intro x
    show GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _
        (Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom _ x)) =
      Dv.σw (GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _ x))
    rw [hsc, hc]
    congr 1
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  · intro x
    rw [GlobalTheory.InertDatumExist.mem_tensInt_iff, GlobalTheory.LFun.InertChart.mem_intLoc_iff hw hunder, hO]
    exact Iff.rfl
  · intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]; rfl
    | tmul x a =>
      have hk : F.κ (x ⊗ₜ a) = F.κ (x ⊗ₜ 1) * F.κ (1 ⊗ₜ a) := by
        rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      show GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _ (compAt L v (x ⊗ₜ a))) = _
      have hm : ∀ p q : FiniteAdeleRing (𝓞 L) L, (p * q) w = p w * q w := fun _ _ => rfl
      rw [hk, F.left, hm, hi, hieq]
      show GlobalTheory.LFun.complMap hunder (a v) * algebraMap L _ x = _
      rw [mul_comm]
      rfl

end GlobalTheory.InertTransferCanon

end
