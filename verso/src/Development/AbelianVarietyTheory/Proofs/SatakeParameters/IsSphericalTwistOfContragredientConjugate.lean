import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgebraicHeckeCharOfRegularAlgebraicPolarizedP
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicHeckeCharSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.CsdTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeCharParallelWeight
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeCharAlgebraicOfSign
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehShapeIffOfDiscreteSpectrum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentsThetaPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryLocalPoints
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section

namespace GlobalTheory.ContraPair.SphTwist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

/- English proof (translation)
Establish `key : ∀ u (h : conjSrc (IsCMField.complexConj E).toRingEquiv w = u) (k : GL (Fin a) (u.adicCompletion E)), k ∈ GlobalTheory.LFun.KGL u a → ∃ k' ∈ GlobalTheory.LFun.KGL w a, Matrix.GeneralLinearGroup.map (conjFin (IsCMField.complexConj E).toRingEquiv) (locGL E a u k) = locGL E a w …`. Introduce `u h k hk`. Substitute `h` using the available equality. Use `⟨_, ?_, GlobalTheory.ConjPairLoc.conjFin_locGL _ w k⟩` and prove the remaining obligations. Take `⟨k0, rfl⟩` from `hk`.

Set `r : Formalism.UG.Ov E (conjSrc (IsCMField.complexConj E).toRingEquiv w) →+* Formalism.UG.Ov E w` to `(conjLoc (IsCMField.complexConj E).toRingEquiv w).restrict _ _ fun x hx => by`. Express the relevant statement in the definitionally equal form `_ ∈ w.adicCompletionIntegers E`. Express the relevant statement in the definitionally equal form `x ∈ (conjSrc (IsCMField.complexConj E).toRingEquiv w).adicCompletionIntegers E at hx`. Rewrite `hx`, the goal using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Rewrite using `[(conjLoc_spec _ w).2.2]`.

Conclude with `hx`. Use `⟨Matrix.GeneralLinearGroup.map r k0, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Both sides reduce to the same expression. Conclude with `key w hw k hk`.
-/
theorem conjFin_locGL_mem (w : HeightOneSpectrum (𝓞 E))
    (hw : conjSrc (IsCMField.complexConj E).toRingEquiv w = w) (k : GL (Fin a) (w.adicCompletion E))
    (hk : k ∈ GlobalTheory.LFun.KGL w a) : ∃ k' ∈ GlobalTheory.LFun.KGL w a,
      Matrix.GeneralLinearGroup.map (conjFin (IsCMField.complexConj E).toRingEquiv) (locGL E a w k) = locGL E a w k' := by
  have key : ∀ u (h : conjSrc (IsCMField.complexConj E).toRingEquiv w = u) (k : GL (Fin a) (u.adicCompletion E)),
      k ∈ GlobalTheory.LFun.KGL u a → ∃ k' ∈ GlobalTheory.LFun.KGL w a,
        Matrix.GeneralLinearGroup.map (conjFin (IsCMField.complexConj E).toRingEquiv) (locGL E a u k) = locGL E a w k' := by
    intro u h k hk
    subst h
    refine ⟨_, ?_, GlobalTheory.ConjPairLoc.conjFin_locGL _ w k⟩
    obtain ⟨k0, rfl⟩ := hk
    let r : Formalism.UG.Ov E (conjSrc (IsCMField.complexConj E).toRingEquiv w) →+* Formalism.UG.Ov E w :=
      (conjLoc (IsCMField.complexConj E).toRingEquiv w).restrict _ _ fun x hx => by
        change _ ∈ w.adicCompletionIntegers E
        change x ∈ (conjSrc (IsCMField.complexConj E).toRingEquiv w).adicCompletionIntegers E at hx
        rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hx ⊢
        rw [(conjLoc_spec _ w).2.2]
        exact hx
    refine ⟨Matrix.GeneralLinearGroup.map r k0, ?_⟩
    ext i j
    rfl
  exact key w hw k hk

end GlobalTheory.ContraPair.SphTwist

open GlobalTheory.ContraPair.SphTwist in

/- English proof (translation)
Introduce `E _ _ _ a _ π ψ hP w hns hS`. Take `⟨B0, hB0⟩` from `hS`. Take `⟨B, -, hB2, hfin, -, -⟩` from `hP`. Establish `hsat : GlobalTheory.LFun.HasSatGL w (π.locRep w) B0` using `(CG.hasSat_mk π w B0).1 hB0`. Take `⟨x, hx, hx0⟩` from `(Submodule.ne_bot_iff _).1 hsat.1`.

Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : ∃ y, B y x ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hx0 (hB2 x h)`. Establish `hw : conjSrc (IsCMField.complexConj E).toRingEquiv w = w`.

Assume the negation of the conclusion as `h`. Conclude with `hns ⟨_, h, GlobalTheory.DefU.LocRet.under_conjSrc w⟩`. Establish `hL : ∀ k ∈ GlobalTheory.LFun.KGL w a, B.flip x ((π.twist ψ⁻¹).locRep w k y) = B.flip x y`. Introduce `k hk`. Take `⟨k', hk', e⟩` from `conjFin_locGL_mem w hw k hk`.

Establish `hx' : π.op (.fin (locGL E a w k')) x = x` using `GlobalTheory.LGrp.mem_fixed.1 hx k' hk'`. Establish `h1` using `hfin (locGL E a w k) y x`. Express the relevant statement in the definitionally equal form `B ((π.twist ψ⁻¹).op (.fin (locGL E a w k)) y) x = B y x`. Use `conv_lhs => rw [← hx']`. Rewrite using `[← e]`.

Conclude with `h1`. Take `⟨v, hv, hve⟩` from `GlobalTheory.SmGL.IwahoriOnto.exists_fixed_map_eq ((π.twist ψ⁻¹).isSmooth_locRep w) GlobalTheory.BcSpehCompare.isCompact_KGL (B.flip x) y hL`. Use `(Submodule.ne_bot_iff _).2 ⟨v, hv, fun h => hy ?_⟩` and prove the remaining obligations. Establish `: B.flip x v = B y x` using `hve`. Rewrite using `[← this, h, map_zero]`.
-/
theorem GlobalTheory.ContraPair.isSpherical_twist_of_dualIsConjBy : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (ψ : HChar E), GlobalTheory.ContraPair.DualIsConjBy π ψ → ∀ w : HeightOneSpectrum (𝓞 E), ¬ GlobalTheory.UnitaryBC.IsSplitAt w → (∃ B, (CG.mk π).HasSat w B) → GlobalTheory.LGrp.IsSpherical ((π.twist ψ⁻¹).locRep w) (GlobalTheory.LFun.KGL w a) := by
  intro E _ _ _ a _ π ψ hP w hns hS
  obtain ⟨B0, hB0⟩ := hS
  obtain ⟨B, -, hB2, hfin, -, -⟩ := hP
  have hsat : GlobalTheory.LFun.HasSatGL w (π.locRep w) B0 := (CG.hasSat_mk π w B0).1 hB0
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hsat.1
  obtain ⟨y, hy⟩ : ∃ y, B y x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx0 (hB2 x h)
  have hw : conjSrc (IsCMField.complexConj E).toRingEquiv w = w := by
    by_contra h
    exact hns ⟨_, h, GlobalTheory.DefU.LocRet.under_conjSrc w⟩
  have hL : ∀ k ∈ GlobalTheory.LFun.KGL w a, B.flip x ((π.twist ψ⁻¹).locRep w k y) = B.flip x y := by
    intro k hk
    obtain ⟨k', hk', e⟩ := conjFin_locGL_mem w hw k hk
    have hx' : π.op (.fin (locGL E a w k')) x = x := GlobalTheory.LGrp.mem_fixed.1 hx k' hk'
    have h1 := hfin (locGL E a w k) y x
    change B ((π.twist ψ⁻¹).op (.fin (locGL E a w k)) y) x = B y x
    conv_lhs => rw [← hx']
    rw [← e]
    exact h1
  obtain ⟨v, hv, hve⟩ := GlobalTheory.SmGL.IwahoriOnto.exists_fixed_map_eq ((π.twist ψ⁻¹).isSmooth_locRep w)
    GlobalTheory.BcSpehCompare.isCompact_KGL (B.flip x) y hL
  refine (Submodule.ne_bot_iff _).2 ⟨v, hv, fun h => hy ?_⟩
  have : B.flip x v = B y x := hve
  rw [← this, h, map_zero]
