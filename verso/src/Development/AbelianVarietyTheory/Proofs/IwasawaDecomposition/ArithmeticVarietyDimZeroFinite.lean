import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfSpecializesOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.ArithCurveFinite

/- English proof (translation)
Take `⟨S, hS, hc, hi, rfl⟩` from `NoetherianSpace.exists_finite_set_isClosed_irreducible hs`. Use `hS.sUnion fun t ht => ?_` and prove the remaining obligations. Take `⟨x, hx⟩` from `QuasiSober.sober (hi t ht) (hc t ht)`. Establish `hne : x ≠ genericPoint Z`. Introduce and unpack `rfl`.

Conclude with `hη ⟨t, ht, hx.mem⟩`. Rewrite using `[← hx.def, (GlobalTheory.SmallSecHeight.isClosed_of_ne hd hne).closure_eq]`. Conclude with `Set.finite_singleton x`.
-/
theorem finite_of_isClosed {Z : Scheme.{0}} [IsIntegral Z] [IsNoetherian Z] (hd : topologicalKrullDim Z = 1)
    {s : Set Z} (hs : IsClosed s) (hη : genericPoint Z ∉ s) : s.Finite := by
  obtain ⟨S, hS, hc, hi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hs
  refine hS.sUnion fun t ht => ?_
  obtain ⟨x, hx⟩ := QuasiSober.sober (hi t ht) (hc t ht)
  have hne : x ≠ genericPoint Z := by
    rintro rfl
    exact hη ⟨t, ht, hx.mem⟩
  rw [← hx.def, (GlobalTheory.SmallSecHeight.isClosed_of_ne hd hne).closure_eq]
  exact Set.finite_singleton x

/- English proof (translation)
Introduce `k _ Z q hZ`. Use `hZ.isIntegral` as an intermediate fact. Use `hZ.isNoetherian` as an intermediate fact. Use `GlobalTheory.Mean4O.isProper_int hZ` as an intermediate fact. Set `t` to `q ≫ spMap (Int.castRingHom k)`.

Establish `hd : topologicalKrullDim Z = 1` using `hZ.dim_eq`. Use `hZ.charZero` as an intermediate fact. Establish `: CharZero Z.functionField` using `((Z.germToFunctionField ⊤).hom.charZero_iff (Z.germToFunctionField_injective ⊤)).1 this`. Establish `: CharZero (Z.residueField (genericPoint Z))` using `(RingHom.charZero_iff (R := Z.functionField) (Z.residue (genericPoint Z)).hom.injective).1 this`. Establish `h0 : (t (genericPoint Z)).asIdeal = ⊥` using `GlobalTheory.Mean4O.asIdeal_eq_bot t _`.

Establish `hb : ¬ (⊥ : Ideal ℤ).IsMaximal` using `fun h => Int.not_isField (Ring.isField_iff_maximal_bot.2 h)`. Establish `: LocallyQuasiFinite t`. Use `.of_finite_preimage_singleton t fun (y : PrimeSpectrum ℤ) => ?_` and prove the remaining obligations. Distinguish the cases in `hy : y.asIdeal = ⊥`. Use `(Set.finite_singleton (genericPoint Z)).subset fun z hz => ?_` and prove the remaining obligations.

Assume the negation of the conclusion as `hne`. Establish `h1` using `t.isClosedMap _ (GlobalTheory.SmallSecHeight.isClosed_of_ne hd hne)`. Rewrite `h1` using `[Set.image_singleton, show t z = y from hz]`. Conclude with `hb (hy ▸ (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).1 h1)`. Use `finite_of_isClosed hd (((PrimeSpectrum.isClosed_singleton_iff_isMaximal y).2 (y.isPrime.isMaximal hy)).preimage t.continuous) fun h => hy ?_` and prove the remaining obligations.

Rewrite using `[← show t (genericPoint Z) = y from h]`. Conclude with `h0`. Establish `: IsFinite t` using `.of_isProper_of_locallyQuasiFinite t`. Conclude with `IsFinite.of_comp q (spMap (Int.castRingHom k))`.
-/
theorem isFinite : ∀ (k : Type) [CommRing k] (Z : Scheme.{0}) (q : Z ⟶ Sp k), IsArithVar q 0 → IsFinite q := by
  intro k _ Z q hZ
  have := hZ.isIntegral
  have := hZ.isNoetherian
  have := GlobalTheory.Mean4O.isProper_int hZ
  let t := q ≫ spMap (Int.castRingHom k)
  have hd : topologicalKrullDim Z = 1 := hZ.dim_eq
  have := hZ.charZero
  have : CharZero Z.functionField := ((Z.germToFunctionField ⊤).hom.charZero_iff
    (Z.germToFunctionField_injective ⊤)).1 this
  have : CharZero (Z.residueField (genericPoint Z)) :=
    (RingHom.charZero_iff (R := Z.functionField) (Z.residue (genericPoint Z)).hom.injective).1 this
  have h0 : (t (genericPoint Z)).asIdeal = ⊥ := GlobalTheory.Mean4O.asIdeal_eq_bot t _
  have hb : ¬ (⊥ : Ideal ℤ).IsMaximal := fun h => Int.not_isField (Ring.isField_iff_maximal_bot.2 h)
  have : LocallyQuasiFinite t := by
    refine .of_finite_preimage_singleton t fun (y : PrimeSpectrum ℤ) => ?_
    by_cases hy : y.asIdeal = ⊥
    · refine (Set.finite_singleton (genericPoint Z)).subset fun z hz => ?_
      by_contra hne
      have h1 := t.isClosedMap _ (GlobalTheory.SmallSecHeight.isClosed_of_ne hd hne)
      rw [Set.image_singleton, show t z = y from hz] at h1
      exact hb (hy ▸ (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).1 h1)
    · refine finite_of_isClosed hd (((PrimeSpectrum.isClosed_singleton_iff_isMaximal y).2
        (y.isPrime.isMaximal hy)).preimage t.continuous) fun h => hy ?_
      rw [← show t (genericPoint Z) = y from h]
      exact h0
  have : IsFinite t := .of_isProper_of_locallyQuasiFinite t
  exact IsFinite.of_comp q (spMap (Int.castRingHom k))

end GlobalTheory.ArithCurveFinite
