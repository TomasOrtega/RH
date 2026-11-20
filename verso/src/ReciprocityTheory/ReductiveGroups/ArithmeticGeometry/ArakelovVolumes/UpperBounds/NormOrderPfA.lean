import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement
import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.NOrd

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact.

Treat this case separately. Treat this case separately. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_val_of_prime {Kf : Type*} [Field Kf] (A : Subring Kf) (P : Ideal A) [P.IsPrime] :
    ∃ V : ValuationSubring Kf, (∀ a : A, (a : Kf) ∈ V) ∧ (∀ a : A, a ∉ P → (a : Kf)⁻¹ ∈ V) ∧
      ∀ a : A, a ∈ P → V.valuation (a : Kf) < 1 := by
  obtain ⟨B, hB⟩ := (LocalSubring.ofPrime A P).exists_le_valuationSubring
  obtain ⟨hle, hloc⟩ := LocalSubring.le_def.1 hB
  let e := LocalSubring.ofPrimeEquiv A P
  let f : Localization.AtPrime P →+* B.toLocalSubring.toSubring :=
    (Subring.inclusion hle).comp (e : Localization.AtPrime P →+* (LocalSubring.ofPrime A P).toSubring)
  have hf : ∀ a : A, ((f (algebraMap A (Localization.AtPrime P) a) : B.toLocalSubring.toSubring) : Kf) = a := by
    intro a
    show ((e (algebraMap A (Localization.AtPrime P) a) : (LocalSubring.ofPrime A P).toSubring) : Kf) = a
    rw [AlgEquiv.commutes]
    rfl
  have hmem : ∀ a : A, (a : Kf) ∈ B := by
    intro a
    have h := (f (algebraMap A (Localization.AtPrime P) a)).2
    rw [hf] at h
    exact h
  refine ⟨B, hmem, fun a ha => ?_, fun a ha => ?_⟩
  · have hu : IsUnit (algebraMap A (Localization.AtPrime P) a) :=
      IsLocalization.map_units _ (⟨a, ha⟩ : P.primeCompl)
    obtain ⟨u, hu'⟩ := hu.map f
    have h1 : ((u⁻¹ : (B.toLocalSubring.toSubring)ˣ) : B.toLocalSubring.toSubring) * (u : _) = 1 :=
      u.inv_mul
    have h2 : (((u⁻¹ : (B.toLocalSubring.toSubring)ˣ) : B.toLocalSubring.toSubring) : Kf) * (a : Kf) = 1 := by
      rw [← hf a, ← hu']
      exact congrArg Subtype.val h1
    rw [← eq_inv_of_mul_eq_one_left h2]
    exact ((u⁻¹ : (B.toLocalSubring.toSubring)ˣ) : B.toLocalSubring.toSubring).2
  · have hnu : ¬ IsUnit (algebraMap A (Localization.AtPrime P) a) := fun h =>
      (IsLocalization.AtPrime.isUnit_to_map_iff _ P a).1 h ha
    have hnu2 : ¬ IsUnit (f (algebraMap A (Localization.AtPrime P) a)) := by
      intro h
      apply hnu
      have h' : IsUnit (e (algebraMap A (Localization.AtPrime P) a)) := hloc.map_nonunit _ h
      have h'' := h'.map (e.symm : (LocalSubring.ofPrime A P).toSubring →+* Localization.AtPrime P)
      first
      | (convert h'' using 1
         exact (e.symm_apply_apply _).symm)
      | (rwa [show (e.symm : (LocalSubring.ofPrime A P).toSubring →+* Localization.AtPrime P)
            (e (algebraMap A (Localization.AtPrime P) a)) = algebraMap A (Localization.AtPrime P) a from
            e.symm_apply_apply _] at h'')
    by_contra hge
    push_neg at hge
    have hv1 : B.valuation (a : Kf) = 1 := le_antisymm ((B.valuation_le_one_iff _).2 (hmem a)) hge
    have hunit : IsUnit (⟨a, hmem a⟩ : B) := (B.valuation_eq_one_iff ⟨a, hmem a⟩).2 hv1
    apply hnu2
    have heq : f (algebraMap A (Localization.AtPrime P) a) = ⟨a, hmem a⟩ := Subtype.ext (hf a)
    rw [heq]
    exact hunit

end ReciprocityTheory.ChartRestriction.G.AR.Up.NOrd
