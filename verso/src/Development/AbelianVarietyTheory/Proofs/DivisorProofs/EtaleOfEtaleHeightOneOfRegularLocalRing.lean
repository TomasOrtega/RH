import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfEtaleAtHeightOnePrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeOfIsIntegrallyClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtPrimeTensorIsDomainIsIntegrallyClosedFaithfulS
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalizationAtPrimeOfHeightOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeOfEtalePuncturedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFractionFieldOfEtaleHeightOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
open IsLocalRing

namespace GlobalTheory.BranchPurity

/- English proof (translation)
Rewrite using `[IsLocalization.AtPrime.ringKrullDim_eq_height p, ← maximalIdeal_height_eq_ringKrullDim]`. Conclude with `WithBot.coe_lt_coe.mpr (Ideal.height_strict_mono_of_isPrime_of_isPrime (lt_of_le_of_ne (le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) hp))`.
-/
theorem dim_lt (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (p : Ideal R) [p.IsPrime]
    (hp : p ≠ maximalIdeal R) : ringKrullDim (Localization.AtPrime p) < ringKrullDim R := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p, ← maximalIdeal_height_eq_ringKrullDim]
  exact WithBot.coe_lt_coe.mpr (Ideal.height_strict_mono_of_isPrime_of_isPrime
    (lt_of_le_of_ne (le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) hp))

/- English proof (translation)
Use `haveI : IsRegularLocalRing R := (isRegularLocalRing_iff R).mpr hR`. Use `haveI : IsRegularRing R := GlobalTheory.isRegularRing_of_isRegularLocalRing R`. Conclude with `(IsRegularRing.isRegularLocalRing_localization p).spanFinrank_maximalIdeal`.
-/
theorem regular_localization (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R) (p : Ideal R) [p.IsPrime] :
    ((maximalIdeal (Localization.AtPrime p)).spanFinrank : WithBot ℕ∞) =
      ringKrullDim (Localization.AtPrime p) := by
  haveI : IsRegularLocalRing R := (isRegularLocalRing_iff R).mpr hR
  haveI : IsRegularRing R := GlobalTheory.isRegularRing_of_isRegularLocalRing R
  exact (IsRegularRing.isRegularLocalRing_localization p).spanFinrank_maximalIdeal

/- English proof (translation)
Use `haveI : IsRegularLocalRing R := (isRegularLocalRing_iff R).mpr hR`. Conclude with `(GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R).2`.
-/
theorem integrallyClosed (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R) : IsIntegrallyClosed R := by
  haveI : IsRegularLocalRing R := (isRegularLocalRing_iff R).mpr hR
  exact (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R).2

/- English proof (translation)
Rewrite using `[IsLocalRing.isField_iff_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal]`. Introduce `h`. Apply `hp` to reduce the goal to its premises. Establish `hinj : Function.Injective (algebraMap R (Localization.AtPrime p))` using `IsLocalization.injective (Localization.AtPrime p) p.primeCompl_le_nonZeroDivisors`. Conclude with `(Ideal.map_eq_bot_iff_of_injective hinj).mp h`.
-/
theorem not_isField_localization (R : Type) [CommRing R] [IsDomain R] (p : Ideal R) [p.IsPrime]
    (hp : p ≠ ⊥) : ¬ IsField (Localization.AtPrime p) := by
  rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal]
  intro h
  apply hp
  have hinj : Function.Injective (algebraMap R (Localization.AtPrime p)) :=
    IsLocalization.injective (Localization.AtPrime p) p.primeCompl_le_nonZeroDivisors
  exact (Ideal.map_eq_bot_iff_of_injective hinj).mp h

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n IH`. Introduce `R A _ _ _ _ _ _ _ _ _ _ hn hR hF hA`. Use `haveI : IsIntegrallyClosed R := integrallyClosed R hR`.

Establish `hfree : Module.Free R A`. Distinguish the cases in `h2 : ringKrullDim R ≤ 2`. Conclude with `GlobalTheory.PurFree.free_of_isIntegrallyClosed R A hR h2`. Use `GlobalTheory.T.free_of_etale_on_punctured_spectrum R A hR ?_ ?_` and prove the remaining obligations. Rewrite `h2` using `[not_le]`.

Establish `h2' : ((2 : ℕ) : WithBot ℕ∞) < ringKrullDim R` using `by exact_mod_cast h2`. Rewrite `h2'`, the goal using `[← hR]`. Establish `: 2 < (maximalIdeal R).spanFinrank` using `by exact_mod_cast h2'`. Conclude with `this` after adjusting the coercions. Introduce `p _ hp`.

Distinguish the cases in `hb : p = ⊥`. Substitute `hb` using the available equality. Conclude with `GlobalTheory.etale_fractionField_of_etale_height_one R A hF hA`. Take `⟨hdom, hic, hfs⟩` from `GlobalTheory.atPrime_tensor_isDomain_isIntegrallyClosed_faithfulSMul R A p`. Establish `hlt` using `dim_lt R p hp`.

Establish `hreg` using `regular_localization R hR p`. Use `IH (maximalIdeal (Localization.AtPrime p)).spanFinrank ?_ (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A) rfl hreg (not_isField_localization R p hb) (GlobalTheory.etale_localization_atPrime_of_height_one R A p hA)` and prove the remaining obligations. Rewrite `hlt` using `[← hreg, ← hR, hn]`. Conclude with `hlt` after adjusting the coercions. Conclude with `GlobalTheory.PurityDisc.etale_of_etale_height_one R A hF hA`.
-/
theorem finiteRing_sq_sub_mul_sq_eq_of_card : ∀ (n : ℕ) (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra R A] [Module.Finite R A] [FaithfulSMul R A], (maximalIdeal R).spanFinrank = n → (((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R) → ¬ IsField R → (∀ (p : Ideal R) [p.IsPrime], p.height = 1 → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → Algebra.Etale R A := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro R A _ _ _ _ _ _ _ _ _ _ hn hR hF hA
  haveI : IsIntegrallyClosed R := integrallyClosed R hR
  have hfree : Module.Free R A := by
    by_cases h2 : ringKrullDim R ≤ 2
    · exact GlobalTheory.PurFree.free_of_isIntegrallyClosed R A hR h2
    · refine GlobalTheory.T.free_of_etale_on_punctured_spectrum R A hR ?_ ?_
      · rw [not_le] at h2
        have h2' : ((2 : ℕ) : WithBot ℕ∞) < ringKrullDim R := by exact_mod_cast h2
        rw [← hR] at h2' ⊢
        have : 2 < (maximalIdeal R).spanFinrank := by exact_mod_cast h2'
        exact_mod_cast this
      · intro p _ hp
        by_cases hb : p = ⊥
        · subst hb
          exact GlobalTheory.etale_fractionField_of_etale_height_one R A hF hA
        obtain ⟨hdom, hic, hfs⟩ := GlobalTheory.atPrime_tensor_isDomain_isIntegrallyClosed_faithfulSMul R A p
        have hlt := dim_lt R p hp
        have hreg := regular_localization R hR p
        refine IH (maximalIdeal (Localization.AtPrime p)).spanFinrank ?_ (Localization.AtPrime p)
          (TensorProduct R (Localization.AtPrime p) A) rfl hreg (not_isField_localization R p hb)
          (GlobalTheory.etale_localization_atPrime_of_height_one R A p hA)
        rw [← hreg, ← hR, hn] at hlt
        exact_mod_cast hlt
  exact GlobalTheory.PurityDisc.etale_of_etale_height_one R A hF hA

/- English proof (translation)
Introduce `R A _ _ _ _ _ _ _ _ _ _ hR _ hF hA`. Conclude with `finiteRing_sq_sub_mul_sq_eq_of_card _ R A rfl hR hF hA`.
-/
theorem etale_of_etale_height_one : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra R A] [Module.Finite R A] [FaithfulSMul R A], (((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R) → 1 ≤ ringKrullDim R → ¬ IsField R → (∀ (p : Ideal R) [p.IsPrime], p.height = 1 → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → Algebra.Etale R A := by
  intro R A _ _ _ _ _ _ _ _ _ _ hR _ hF hA
  exact finiteRing_sq_sub_mul_sq_eq_of_card _ R A rfl hR hF hA

end GlobalTheory.BranchPurity
