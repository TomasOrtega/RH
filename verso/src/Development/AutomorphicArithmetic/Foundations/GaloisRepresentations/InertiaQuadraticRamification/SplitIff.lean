import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertSplitAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfDecompositionLeRestrictionRange
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSolvableCmExtensionSplitPlace

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.UnitaryBC
open scoped Pointwise

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

/- English proof (translation)
Use `haveI : IsGalois (maximalRealSubfield L) L := Algebra.IsQuadraticExtension.isGalois _ _`. Establish `hcard : Nat.card (L ≃ₐ[maximalRealSubfield L] L) = 2`. Rewrite using `[IsGalois.card_aut_eq_finrank]`. Conclude with `Algebra.IsQuadraticExtension.finrank_eq_two _ _`. Establish `hne : ∀ r : G (maximalRealSubfield L) Ω, ¬ Fixes L r → r.restrictNormal L ≠ 1`.

Introduce `r hr h1`. Apply `hr` to reduce the goal to its premises. Introduce `x`. Rewrite using `[← AlgEquiv.restrictNormal_commutes r L x, h1]`. Both sides reduce to the same expression.

Establish `heq : s.restrictNormal L = t.restrictNormal L` using `((Nat.card_eq_two_iff' 1).1 hcard).unique (hne s hs) (hne t ht)`. Rewrite using `[← AlgEquiv.restrictNormal_commutes s L y, ← AlgEquiv.restrictNormal_commutes t L y, heq]`.
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
Introduce `L Ω _ _ _ _ _ _ A w hA`. Use `show IsSplitAt w ↔ ∀ g ∈ Dec (F := maximalRealSubfield L) A, Fixes L g`. Establish `up : ∀ (B : ValuationSubring Ω) (u : HeightOneSpectrum (𝓞 L)), IsPlaceOver B u → IsPlaceOver B (HeightOneSpectrum.under (𝓞 (maximalRealSubfield L)) u)`. Introduce `B u hB x`. Establish `e : algebraMap (maximalRealSubfield L) Ω (x : maximalRealSubfield L) = algebraMap L Ω ((algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) x : 𝓞 L) : L)`.

Rewrite using `[IsScalarTower.algebraMap_apply (maximalRealSubfield L) L Ω]`. Both sides reduce to the same expression. Rewrite using `[e, hB]`. Simplify using `[HeightOneSpectrum.under]`. Establish `hv` using `up A w hA`.

Establish `val : ∀ (σ : G (maximalRealSubfield L) Ω) (y : Ω), (σ • A).valuation y < 1 ↔ A.valuation (σ⁻¹ y) < 1`. Introduce `σ y`. Rewrite using `[valuation_lt_one_iff', valuation_lt_one_iff', ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]`. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨u, hu, huw⟩ g hg`. Assume the negation of the conclusion as `hgL`. Take `⟨A', hA'⟩` from `exists_isPlaceOver Ω u`. Take `⟨σ, rfl⟩` from `exists_smul_eq_of_isPlaceOver hv (huw ▸ up A' u hA')`. Apply `hu` to reduce the goal to its premises.

Use `eq_of_isPlaceOver hA' ?_` and prove the remaining obligations. Introduce `x`. Rewrite using `[val, ← hA x]`. Distinguish the cases in `hσ : Fixes L σ⁻¹`. Rewrite using `[hσ]`.

Rewrite using `[apply_eq_of_not_fixes hσ hgL, valuation_apply_lt_one_iff hg]`. Introduce `h`. Use `UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω A _ hv ?_ w rfl` and prove the remaining obligations. Introduce `g hg`. Use `⟨AlgEquiv.ofRingEquiv (f := g.toRingEquiv) (fun x => h g hg x), ?_⟩` and prove the remaining obligations.

Use extensionality with `x`. Both sides reduce to the same expression.
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
