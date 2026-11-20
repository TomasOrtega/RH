import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalizationAtPrimeQuotient
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u

noncomputable section

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Unfold both sides to obtain the same proposition, which implies itself. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

By extensionality, compare the relevant components. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Introduce a local definition for the expression.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem LocalizationAtPrimeQuotient.proof : LocalizationAtPrimeQuotient.Statement.{u} := by
  intro A _ I T P _ W _ hP
  let Q := A ⧸ I
  let B := Localization.AtPrime W ⧸ I.map (algebraMap A (Localization.AtPrime W))

  have hsub : (P.comap (algebraMap Q (Localization T))).primeCompl =
      Algebra.algebraMapSubmonoid Q W.primeCompl := by
    have hmem : ∀ r : A, Ideal.Quotient.mk I r ∈ P.comap (algebraMap Q (Localization T)) ↔ r ∈ W := by
      intro r; rw [← hP]; exact Iff.rfl
    have hIW : I ≤ W := fun r hr => by
      rw [← hmem, Ideal.Quotient.eq_zero_iff_mem.2 hr]; exact Ideal.zero_mem _
    ext q
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    have h1 : Ideal.Quotient.mk I r ∈ (P.comap (algebraMap Q (Localization T))).primeCompl ↔ r ∉ W :=
      not_congr (hmem r)
    rw [h1]
    constructor
    · intro hr; exact ⟨r, hr, rfl⟩
    · rintro ⟨r', hr', he⟩ hr
      apply hr'
      have : r' - r ∈ I := Ideal.Quotient.eq.1 he
      simpa using W.add_mem (hIW this) hr
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid Q W.primeCompl) (Localization.AtPrime P) := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization T
      (Localization.AtPrime P) P
    rw [IsLocalization.AtPrime, hsub] at this
    exact this
  let e := IsLocalization.algEquiv (Algebra.algebraMapSubmonoid Q W.primeCompl)
    (Localization.AtPrime P) B
  refine ⟨e.toRingEquiv, fun a => ?_⟩
  have h2 : algebraMap (Localization T) (Localization.AtPrime P)
      (algebraMap Q (Localization T) (Ideal.Quotient.mk I a)) =
      algebraMap Q (Localization.AtPrime P) (Ideal.Quotient.mk I a) :=
    (IsScalarTower.algebraMap_apply Q (Localization T) (Localization.AtPrime P) _).symm
  rw [h2]
  exact e.commutes (Ideal.Quotient.mk I a)

end

end GroundTheory.Heights₂.Heights
