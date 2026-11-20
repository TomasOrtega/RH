import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertSplitAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfDecompositionLeRestrictionRange
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSolvableCmExtensionSplitPlace

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.UnitaryBC
open scoped Pointwise

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
private theorem apply_eq_of_not_fixes {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    {s t : G (maximalRealSubfield L) Ω} (hs : ¬ Fixes L s) (ht : ¬ Fixes L t) (y : L) :
    s (algebraMap L Ω y) = t (algebraMap L Ω y) := by
  haveI : IsGalois (maximalRealSubfield L) L := Algebra.IsQuadraticExtension.isGalois _ _
  have hcard : Nat.card (L ≃ₐ[maximalRealSubfield L] L) = 2 := by
    rw [IsGalois.card_aut_eq_finrank]
    exact Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hne : ∀ r : G (maximalRealSubfield L) Ω, ¬ Fixes L r → r.restrictNormal L ≠ 1 := by
    intro r hr h1
    apply hr
    intro x
    rw [← AlgEquiv.restrictNormal_commutes r L x, h1]
    rfl
  have heq : s.restrictNormal L = t.restrictNormal L :=
    ((Nat.card_eq_two_iff' 1).1 hcard).unique (hne s hs) (hne t ht)
  rw [← AlgEquiv.restrictNormal_commutes s L y, ← AlgEquiv.restrictNormal_commutes t L y, heq]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components.

Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem splitIff : SplitIff := by
  intro L Ω _ _ _ _ _ _ A w hA
  show IsSplitAt w ↔ ∀ g ∈ Dec (F := maximalRealSubfield L) A, Fixes L g
  have up : ∀ (B : ValuationSubring Ω) (u : HeightOneSpectrum (𝓞 L)), IsPlaceOver B u →
      IsPlaceOver B (HeightOneSpectrum.under (𝓞 (maximalRealSubfield L)) u) := by
    intro B u hB x
    have e : algebraMap (maximalRealSubfield L) Ω (x : maximalRealSubfield L) =
        algebraMap L Ω ((algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) x : 𝓞 L) : L) := by
      rw [IsScalarTower.algebraMap_apply (maximalRealSubfield L) L Ω]
      rfl
    rw [e, hB]
    simp [HeightOneSpectrum.under]
  have hv := up A w hA
  have val : ∀ (σ : G (maximalRealSubfield L) Ω) (y : Ω),
      (σ • A).valuation y < 1 ↔ A.valuation (σ⁻¹ y) < 1 := by
    intro σ y
    rw [valuation_lt_one_iff', valuation_lt_one_iff',
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    simp
  constructor
  · rintro ⟨u, hu, huw⟩ g hg
    by_contra hgL
    obtain ⟨A', hA'⟩ := exists_isPlaceOver Ω u
    obtain ⟨σ, rfl⟩ := exists_smul_eq_of_isPlaceOver hv (huw ▸ up A' u hA')
    apply hu
    refine eq_of_isPlaceOver hA' ?_
    intro x
    rw [val, ← hA x]
    by_cases hσ : Fixes L σ⁻¹
    · rw [hσ]
    · rw [apply_eq_of_not_fixes hσ hgL, valuation_apply_lt_one_iff hg]
  · intro h
    refine UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω A _ hv ?_ w rfl
    intro g hg
    refine ⟨AlgEquiv.ofRingEquiv (f := g.toRingEquiv) (fun x => h g hg x), ?_⟩
    ext x
    rfl

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
