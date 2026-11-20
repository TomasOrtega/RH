import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitarySphericalIffHasSatakeInertStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertSatakeGiven

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem continuous_of_valuation_eq {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (s : K →+* K) (hs : ∀ x, Valued.v (s x) = Valued.v x) : Continuous s := by
  have h : Filter.Tendsto s (nhds 0) (nhds 0) := by
    rw [(Valued.hasBasis_nhds_zero K Γ₀).tendsto_iff (Valued.hasBasis_nhds_zero K Γ₀)]
    intro γ _
    refine ⟨γ, trivial, fun x hx => ?_⟩
    simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding] at hx ⊢
    rwa [hs]
  exact continuous_of_continuousAt_zero s (by simpa [ContinuousAt] using h)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Substitute using the available equality.

Establish an intermediate fact. Substitute using the available equality. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem exists_hasSatAt : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (U : Submodule ℂ (UA L n → ℂ)), IsAutRepU U → ∀ (w : HeightOneSpectrum (𝓞 L)), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal → ¬ IsSplitAt w → ∀ (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L) (q : ℕ), (∀ x : L, s (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → Formalism.UG.IsUnramInv ϖ s q → IsUnramU U w → ∃ α0 : Fin (n / 2) → ℂˣ, HasSatAt U w s ϖ q α0 := by
  intro L _ _ _ n U hU w hun hns s ϖ q hs hI hph
  have hsph : (GlobalTheory.DefU.AU.mk ⟨U, hU⟩).Sph w := (GlobalTheory.DefU.AU.sph_mk _ w).2 hph
  obtain ⟨α0, hα⟩ := (GlobalTheory.T.definiteUnitary_spherical_iff_hasSatake_inert L n _ w hun hns).1 hsph
  rw [GlobalTheory.DefU.AU.isSat_mk] at hα
  obtain ⟨s', ϖ', q', hs', hI', hsat⟩ := hα
  have hss : s' = s := by
    apply DFunLike.coe_injective
    refine (HeightOneSpectrum.denseRange_algebraMap L w).equalizer (continuous_of_valuation_eq s' hI'.2.1)
      (continuous_of_valuation_eq s hI.2.1) (funext fun k => ?_)
    simp only [Function.comp_apply, hs', hs]
  subst hss
  have hqq : q' = q := Nat.pow_left_injective (n := 2) (by norm_num) (hI'.2.2.2.2.2.2.symm.trans hI.2.2.2.2.2.2)
  subst hqq
  obtain ⟨b, hb, hbJ, p, hp, σ, hc, hS⟩ := hsat
  exact ⟨α0, b, hb, hbJ, p, hp, σ, hc, hS.1, fun x hx h0 => (hS.2 x hx h0).of_unif hI' hI⟩

end GlobalTheory.InertSatakeGiven

end
