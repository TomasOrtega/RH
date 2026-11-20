import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement
import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.NOrd

/- English proof (translation)
Take `⟨B, hB⟩` from `(LocalSubring.ofPrime A P).exists_le_valuationSubring`. Take `⟨hle, hloc⟩` from `LocalSubring.le_def.1 hB`. Set `e` to `LocalSubring.ofPrimeEquiv A P`. Set `f : Localization.AtPrime P →+* B.toLocalSubring.toSubring` to `(Subring.inclusion hle).comp (e : Localization.AtPrime P →+* (LocalSubring.ofPrime A P).toSubring)`. Establish `hf : ∀ a : A, ((f (algebraMap A (Localization.AtPrime P) a) : B.toLocalSubring.toSubring) : Kf) = a`.

Introduce `a`. Use `show ((e (algebraMap A (Localization.AtPrime P) a) : (LocalSubring.ofPrime A P).toSubring) : Kf) = a`. Rewrite using `[AlgEquiv.commutes]`. Both sides reduce to the same expression. Establish `hmem : ∀ a : A, (a : Kf) ∈ B`.

Introduce `a`. Establish `h` using `(f (algebraMap A (Localization.AtPrime P) a)).2`. Rewrite `h` using `[hf]`. Conclude with `h`. Use `⟨B, hmem, fun a ha => ?_, fun a ha => ?_⟩` and prove the remaining obligations.

Establish `hu : IsUnit (algebraMap A (Localization.AtPrime P) a)` using `IsLocalization.map_units _ (⟨a, ha⟩ : P.primeCompl)`. Take `⟨u, hu'⟩` from `hu.map f`. Establish `h1 : ((u⁻¹ : (B.toLocalSubring.toSubring)ˣ) : B.toLocalSubring.toSubring) * (u : _) = 1` using `u.inv_mul`. Establish `h2 : (((u⁻¹ : (B.toLocalSubring.toSubring)ˣ) : B.toLocalSubring.toSubring) : Kf) * (a : Kf) = 1`. Rewrite using `[← hf a, ← hu']`.

Conclude with `congrArg Subtype.val h1`. Rewrite using `[← eq_inv_of_mul_eq_one_left h2]`. Conclude with `((u⁻¹ : (B.toLocalSubring.toSubring)ˣ) : B.toLocalSubring.toSubring).2`. Establish `hnu : ¬ IsUnit (algebraMap A (Localization.AtPrime P) a)` using `fun h => (IsLocalization.AtPrime.isUnit_to_map_iff _ P a).1 h ha`. Establish `hnu2 : ¬ IsUnit (f (algebraMap A (Localization.AtPrime P) a))`.

Introduce `h`. Apply `hnu` to reduce the goal to its premises. Establish `h' : IsUnit (e (algebraMap A (Localization.AtPrime P) a))` using `hloc.map_nonunit _ h`. Establish `h''` using `h'.map (e.symm : (LocalSubring.ofPrime A P).toSubring →+* Localization.AtPrime P)`. Use `first`.

Consider the case `(convert h'' using 1`. Conclude with `(e.symm_apply_apply _).symm)`. Consider the case `(rwa [show (e.symm : (LocalSubring.ofPrime A P).toSubring →+* Localization.AtPrime P) (e (algebraMap A (Localization.AtPrime P) a)) = algebraMap A (Localization.AtPrime P) a from e.symm_apply_apply _] at h'')`. Assume the negation of the conclusion as `hge`. Use `push_neg at hge`.

Establish `hv1 : B.valuation (a : Kf) = 1` using `le_antisymm ((B.valuation_le_one_iff _).2 (hmem a)) hge`. Establish `hunit : IsUnit (⟨a, hmem a⟩ : B)` using `(B.valuation_eq_one_iff ⟨a, hmem a⟩).2 hv1`. Apply `hnu2` to reduce the goal to its premises. Establish `heq : f (algebraMap A (Localization.AtPrime P) a) = ⟨a, hmem a⟩` using `Subtype.ext (hf a)`. Rewrite using `[heq]`.

Conclude with `hunit`.
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
