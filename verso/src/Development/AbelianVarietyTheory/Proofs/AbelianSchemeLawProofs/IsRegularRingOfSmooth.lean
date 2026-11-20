import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Establish `hlo : q.LiesOver (q.under R)` using `⟨rfl⟩`. Set `_` to `Localization.AtPrime.algebraOfLiesOver (q.under R) q`. Establish `hmax : (q.under R).map (algebraMap R (Localization.AtPrime q)) = IsLocalRing.maximalIdeal (Localization.AtPrime q)` using `((Algebra.isUnramifiedAt_iff_map_eq R (q.under R) q).mp inferInstance).2`. Establish `hsf : (IsLocalRing.maximalIdeal (Localization.AtPrime q)).spanFinrank ≤ (IsLocalRing.maximalIdeal (Localization.AtPrime (q.under R))).spanFinrank`. Establish `heq : IsLocalRing.maximalIdeal (Localization.AtPrime q) = (IsLocalRing.maximalIdeal (Localization.AtPrime (q.under R))).map (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q))`.

Rewrite using `[← hmax, ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq]`. Rewrite using `[heq]`. Conclude with `Ideal.spanFinrank_map_le_of_fg _ (IsLocalRing.maximalIdeal _).fg_of_isNoetherianRing`. Establish `hht : (q.under R).height ≤ q.height`. Rewrite using `[Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (q.under R) q]`.

Conclude with `le_self_add`. Apply `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Conclude with `hsf` after adjusting the coercions. Use `_ = ringKrullDim (Localization.AtPrime (q.under R)) := h.spanFinrank_maximalIdeal`.

Use `_ = ((q.under R).height : WithBot ℕ∞) := IsLocalization.AtPrime.ringKrullDim_eq_height (q.under R) _`. Use `_ ≤ (q.height : WithBot ℕ∞) := by exact_mod_cast hht`. Use `_ = ringKrullDim (Localization.AtPrime q) := (IsLocalization.AtPrime.ringKrullDim_eq_height q _).symm`.
-/
private theorem isRegularLocalRing_atPrime_of_etale' (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S] [Algebra.Etale R S] (q : Ideal S) [q.IsPrime]
    (h : IsRegularLocalRing (Localization.AtPrime (q.under R))) :
    IsRegularLocalRing (Localization.AtPrime q) := by
  have hlo : q.LiesOver (q.under R) := ⟨rfl⟩
  let _ := Localization.AtPrime.algebraOfLiesOver (q.under R) q
  have hmax : (q.under R).map (algebraMap R (Localization.AtPrime q)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q) :=
    ((Algebra.isUnramifiedAt_iff_map_eq R (q.under R) q).mp inferInstance).2
  have hsf : (IsLocalRing.maximalIdeal (Localization.AtPrime q)).spanFinrank ≤
      (IsLocalRing.maximalIdeal (Localization.AtPrime (q.under R))).spanFinrank := by
    have heq : IsLocalRing.maximalIdeal (Localization.AtPrime q) =
        (IsLocalRing.maximalIdeal (Localization.AtPrime (q.under R))).map
          (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q)) := by
      rw [← hmax, ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
        ← IsScalarTower.algebraMap_eq]
    rw [heq]
    exact Ideal.spanFinrank_map_le_of_fg _ (IsLocalRing.maximalIdeal _).fg_of_isNoetherianRing
  have hht : (q.under R).height ≤ q.height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (q.under R) q]
    exact le_self_add
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  calc ((IsLocalRing.maximalIdeal (Localization.AtPrime q)).spanFinrank : WithBot ℕ∞)
      ≤ ((IsLocalRing.maximalIdeal (Localization.AtPrime (q.under R))).spanFinrank : WithBot ℕ∞) := by
        exact_mod_cast hsf
    _ = ringKrullDim (Localization.AtPrime (q.under R)) := h.spanFinrank_maximalIdeal
    _ = ((q.under R).height : WithBot ℕ∞) :=
        IsLocalization.AtPrime.ringKrullDim_eq_height (q.under R) _
    _ ≤ (q.height : WithBot ℕ∞) := by exact_mod_cast hht
    _ = ringKrullDim (Localization.AtPrime q) :=
        (IsLocalization.AtPrime.ringKrullDim_eq_height q _).symm

/- English proof (translation)
Establish `: IsNoetherianRing S` using `Algebra.FiniteType.isNoetherianRing R S`. Conclude with `isRegularRing_iff.mpr fun q _ => isRegularLocalRing_atPrime_of_etale' R S q inferInstance`.
-/
theorem isRegularRing_of_etale (R S : Type*) [CommRing R] [IsRegularRing R] [CommRing S]
    [Algebra R S] [Algebra.Etale R S] : IsRegularRing S := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  exact isRegularRing_iff.mpr fun q _ => isRegularLocalRing_atPrime_of_etale' R S q inferInstance

/- English proof (translation)
Introduce `V B _ _ _ _ _`. Establish `: IsNoetherianRing B` using `Algebra.FiniteType.isNoetherianRing V B`. Use `isRegularRing_iff.mpr fun Q _ => ?_` and prove the remaining obligations. Take `⟨f, hf, n, _, _, _⟩` from `Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := V) (p := Q)`. Establish `hT : IsRegularRing (Localization.Away f)` using `isRegularRing_of_etale (MvPolynomial (Fin n) V) (Localization.Away f)`.

Establish `disj : Disjoint (Submonoid.powers f : Set B) (Q : Set B)` using `(Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hf`. Set `Q'` to `Q.map (algebraMap B (Localization.Away f))`. Establish `: Q'.IsPrime` using `IsLocalization.isPrime_of_isPrime_disjoint (.powers f) _ _ ‹_› disj`. Establish `: IsLocalization.AtPrime (Localization.AtPrime Q') Q`. Use `IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (.powers f) (Localization.AtPrime Q') Q'` and compare the differences between its conclusion and the goal.

Conclude with `(IsLocalization.under_map_of_isPrime_disjoint (.powers f) _ ‹_› disj).symm`. Conclude with `IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv Q.primeCompl (Localization.AtPrime Q') (Localization.AtPrime Q)).toRingEquiv`.
-/
theorem isRegularRing_of_smooth :
    ∀ (V B : Type) [CommRing V] [IsRegularRing V] [CommRing B] [Algebra V B] [Algebra.Smooth V B],
      IsRegularRing B := by
  intro V B _ _ _ _ _
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing V B
  refine isRegularRing_iff.mpr fun Q _ => ?_
  obtain ⟨f, hf, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := V) (p := Q)
  have hT : IsRegularRing (Localization.Away f) :=
    isRegularRing_of_etale (MvPolynomial (Fin n) V) (Localization.Away f)
  have disj : Disjoint (Submonoid.powers f : Set B) (Q : Set B) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hf
  let Q' := Q.map (algebraMap B (Localization.Away f))
  have : Q'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (.powers f) _ _ ‹_› disj
  have : IsLocalization.AtPrime (Localization.AtPrime Q') Q := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (.powers f)
      (Localization.AtPrime Q') Q'
    exact (IsLocalization.under_map_of_isPrime_disjoint (.powers f) _ ‹_› disj).symm
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv Q.primeCompl
    (Localization.AtPrime Q') (Localization.AtPrime Q)).toRingEquiv

end GlobalTheory
