import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapCompConstFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

namespace GlobalTheory

open IsLocalRing in

/- English proof (translation)
Establish `hT` using `tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (Localization.AtPrime q)`. Establish `h1 : IsIntegrallyClosed (Localization.AtPrime q)` using `isIntegrallyClosed_of_isLocalization _ q.primeCompl q.primeCompl_le_nonZeroDivisors`. Establish `h2 : ∀ Q' : Ideal (Localization.AtPrime q), Q' ≠ ⊥ → Q'.IsPrime → Q' = maximalIdeal (Localization.AtPrime q)`. Introduce `Q' hQ' hQ'p`. Establish `hc : (Q'.comap (algebraMap A (Localization.AtPrime q))).IsPrime` using `Ideal.comap_isPrime _ _`.

Establish `hle : Q'.comap (algebraMap A (Localization.AtPrime q)) ≤ q`. Introduce `x hx`. Assume the negation of the conclusion as `hxq`. Conclude with `hQ'p.ne_top (Ideal.eq_top_of_isUnit_mem _ hx (IsLocalization.map_units (Localization.AtPrime q) (⟨x, hxq⟩ : q.primeCompl)))`. Establish `hne : Q'.comap (algebraMap A (Localization.AtPrime q)) ≠ ⊥`.

Introduce `h0`. Apply `hQ'` to reduce the goal to its premises. Rewrite using `[← IsLocalization.map_under q.primeCompl (Localization.AtPrime q) Q']`. Rewrite using `[Ideal.under, h0, Ideal.map_bot]`. Establish `heq` using `hmin _ hc hne hle`.

Rewrite using `[← IsLocalization.map_under q.primeCompl (Localization.AtPrime q) Q']`. Rewrite using `[Ideal.under, heq, Localization.AtPrime.map_eq_maximalIdeal]`. Establish `h12 : IsIntegrallyClosed (Localization.AtPrime q) ∧ ∀ Q' : Ideal (Localization.AtPrime q), Q' ≠ ⊥ → Q'.IsPrime → Q' = maximalIdeal (Localization.AtPrime q)` using `⟨h1, h2⟩`. Conclude with `(hT.out 3 1).mp h12`.
-/
theorem valuationRing_atPrime_of_minimal {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (q : Ideal A) [q.IsPrime]
    (hmin : ∀ p : Ideal A, p.IsPrime → p ≠ ⊥ → p ≤ q → p = q) :
    ValuationRing (Localization.AtPrime q) := by
  have hT := tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (Localization.AtPrime q)
  have h1 : IsIntegrallyClosed (Localization.AtPrime q) :=
    isIntegrallyClosed_of_isLocalization _ q.primeCompl q.primeCompl_le_nonZeroDivisors
  have h2 : ∀ Q' : Ideal (Localization.AtPrime q), Q' ≠ ⊥ → Q'.IsPrime →
      Q' = maximalIdeal (Localization.AtPrime q) := by
    intro Q' hQ' hQ'p
    have hc : (Q'.comap (algebraMap A (Localization.AtPrime q))).IsPrime := Ideal.comap_isPrime _ _
    have hle : Q'.comap (algebraMap A (Localization.AtPrime q)) ≤ q := by
      intro x hx
      by_contra hxq
      exact hQ'p.ne_top (Ideal.eq_top_of_isUnit_mem _ hx
        (IsLocalization.map_units (Localization.AtPrime q) (⟨x, hxq⟩ : q.primeCompl)))
    have hne : Q'.comap (algebraMap A (Localization.AtPrime q)) ≠ ⊥ := by
      intro h0
      apply hQ'
      rw [← IsLocalization.map_under q.primeCompl (Localization.AtPrime q) Q']
      rw [Ideal.under, h0, Ideal.map_bot]
    have heq := hmin _ hc hne hle
    rw [← IsLocalization.map_under q.primeCompl (Localization.AtPrime q) Q']
    rw [Ideal.under, heq, Localization.AtPrime.map_eq_maximalIdeal]
  have h12 : IsIntegrallyClosed (Localization.AtPrime q) ∧ ∀ Q' : Ideal (Localization.AtPrime q),
      Q' ≠ ⊥ → Q'.IsPrime → Q' = maximalIdeal (Localization.AtPrime q) := ⟨h1, h2⟩
  exact (hT.out 3 1).mp h12

/- English proof (translation)
Rewrite `h` using `[IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_iff_eq_mul, ← map_mul]`. Conclude with `IsLocalization.injective (Localization.AtPrime q) q.primeCompl_le_nonZeroDivisors h`.
-/
theorem mul_eq_mul_of_atPrime {A : Type} [CommRing A] [IsDomain A] (q : Ideal A) [q.IsPrime]
    (x y a : A) (s : q.primeCompl)
    (h : algebraMap A (Localization.AtPrime q) x * IsLocalization.mk' _ a s =
      algebraMap A (Localization.AtPrime q) y) : x * a = y * s := by
  rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_iff_eq_mul, ← map_mul] at h
  exact IsLocalization.injective (Localization.AtPrime q) q.primeCompl_le_nonZeroDivisors h

end GlobalTheory

namespace GlobalTheory

/- English proof (translation)
Introduce `K _ R _ _ _ E hRE hyp e he`. Set `φ : R →+* E` to `{ toFun := fun r => ⟨r, hRE r.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl }`. Set `q : Ideal R` to `(IsLocalRing.maximalIdeal E).comap φ`. Establish `hqmem : ∀ r : R, r ∈ q ↔ E.valuation (r : K) < 1` using `fun r => E.valuation_lt_one_iff (φ r)`. Establish `hRv : ∀ r : R, E.valuation (r : K) ≤ 1` using `fun r => (E.valuation_le_one_iff _).2 (hRE r.2)`.

Establish `hv1 : ∀ s : R, s ∉ q → E.valuation (s : K) = 1` using `fun s hs => le_antisymm (hRv s) (not_lt.1 ((hqmem s).not.1 hs))`. Establish `hinv : ∀ s : R, s ∉ q → (s : K)⁻¹ ∈ E`. Introduce `s hs`. Rewrite using `[← E.valuation_le_one_iff, map_inv₀, hv1 s hs, inv_one]`. Establish `hne0 : ∀ s : R, s ∉ q → (s : K) ≠ 0`.

Introduce `s hs h`. Use `hv1 s hs` as an intermediate fact. Rewrite `this` using `[h, map_zero]`. Conclude with `zero_ne_one this`. Use `haveI : q.IsPrime := Ideal.comap_isPrime _ _`.

Take `⟨⟨x, y⟩, hxy⟩` from `IsLocalization.mk'_surjective (S := K) (nonZeroDivisors R) e`. Simplify using `only at hxy`. Rewrite `hxy` using `[IsFractionRing.mk'_eq_div]`. Establish `hy0 : (algebraMap R K y) ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors y.2`. Express the relevant statement in the definitionally equal form `((x : R) : K) / ((y : R) : K) = e at hxy`.

Express the relevant statement in the definitionally equal form `((y : R) : K) ≠ 0 at hy0`. Distinguish the cases in `hq : q = ⊥`. Establish `hyq : (y : R) ∉ q`. Rewrite using `[hq, Ideal.mem_bot]`. Introduce `h`.

Apply `hy0` to reduce the goal to its premises. Rewrite using `[h]`. Both sides reduce to the same expression. Conclude with `⟨x, (x : R).2, y, (y : R).2, hinv _ hyq, hxy.symm⟩`. Establish `hmin : ∀ p : Ideal R, p.IsPrime → p ≠ ⊥ → p ≤ q → p = q`.

Introduce `p hp hp0 hpq`. Use `le_antisymm hpq ?_` and prove the remaining obligations. Introduce `r hr`. Use `hyp p hp hp0 (fun t ht => ?_) r ?_` and prove the remaining obligations. Conclude with `E.mem_nonunits_iff.2 ((hqmem t).1 (hpq ht))`.

Conclude with `E.mem_nonunits_iff.2 ((hqmem r).1 hr)`. Use `haveI : ValuationRing (Localization.AtPrime q) := valuationRing_atPrime_of_minimal q hmin`. Take `⟨c, hc⟩` from `ValuationRing.cond (algebraMap R (Localization.AtPrime q) x) (algebraMap R (Localization.AtPrime q) y)`. Take `⟨⟨a, s⟩, rfl⟩` from `IsLocalization.mk'_surjective (S := Localization.AtPrime q) q.primeCompl c`. Simplify using `only at hc`.

Establish `hsq : (s : R) ∉ q` using `s.2`. Break down `hc with hc | hc` into its components or cases. Establish `h` using `mul_eq_mul_of_atPrime q _ _ _ _ hc`. Establish `hK : ((x : R) : K) * (a : K) = ((y : R) : K) * ((s : R) : K)`. Use `congrArg (fun t : R => (t : K)) h` as an intermediate fact.

Simplify using `using this`. Distinguish the cases in `haq : a ∈ q`. It suffices to derive a contradiction. Establish `hea : e * (a : K) = ((s : R) : K)`. Rewrite using `[← hxy]`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `hK`. Establish `h1` using `hv1 _ hsq`. Rewrite `h1` using `[← hea, map_mul]`. Establish `hle : E.valuation e * E.valuation (a : K) ≤ E.valuation (a : K)` using `mul_le_of_le_one_left' ((E.valuation_le_one_iff e).2 he)`.

Use `(hqmem a).1 haq` as an intermediate fact. Rewrite `hle` using `[h1]`. Conclude with `absurd (lt_of_le_of_lt hle this) (lt_irrefl 1)`. Use `⟨((s : R) : K), (s : R).2, (a : K), a.2, hinv a haq, ?_⟩` and prove the remaining obligations. Rewrite using `[← hxy, div_eq_div_iff hy0 (hne0 a haq)]`.

Take the linear combination `hK`. Establish `h` using `mul_eq_mul_of_atPrime q _ _ _ _ hc`. Establish `hK : ((y : R) : K) * (a : K) = ((x : R) : K) * ((s : R) : K)`. Use `congrArg (fun t : R => (t : K)) h` as an intermediate fact. Simplify using `using this`.

Use `⟨(a : K), a.2, ((s : R) : K), (s : R).2, hinv _ hsq, ?_⟩` and prove the remaining obligations. Rewrite using `[← hxy, div_eq_div_iff hy0 (hne0 _ hsq)]`. Take the linear combination `-hK`.
-/
theorem exists_div_of_center_height_le_one : ∀ (K : Type) [Field K] (R : Subring K) [IsNoetherianRing R]
    [IsIntegrallyClosed R] [IsFractionRing R K] (E : ValuationSubring K), R ≤ E.toSubring →
    (∀ p : Ideal R, p.IsPrime → p ≠ ⊥ → (∀ r ∈ p, (r : K) ∈ E.nonunits) →
      ∀ r : R, (r : K) ∈ E.nonunits → r ∈ p) →
    ∀ e ∈ E, ∃ a ∈ R, ∃ s ∈ R, s⁻¹ ∈ E ∧ e = a / s := by
  intro K _ R _ _ _ E hRE hyp e he
  classical
  let φ : R →+* E :=
    { toFun := fun r => ⟨r, hRE r.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  let q : Ideal R := (IsLocalRing.maximalIdeal E).comap φ
  have hqmem : ∀ r : R, r ∈ q ↔ E.valuation (r : K) < 1 := fun r => E.valuation_lt_one_iff (φ r)
  have hRv : ∀ r : R, E.valuation (r : K) ≤ 1 := fun r => (E.valuation_le_one_iff _).2 (hRE r.2)
  have hv1 : ∀ s : R, s ∉ q → E.valuation (s : K) = 1 := fun s hs =>
    le_antisymm (hRv s) (not_lt.1 ((hqmem s).not.1 hs))
  have hinv : ∀ s : R, s ∉ q → (s : K)⁻¹ ∈ E := by
    intro s hs
    rw [← E.valuation_le_one_iff, map_inv₀, hv1 s hs, inv_one]
  have hne0 : ∀ s : R, s ∉ q → (s : K) ≠ 0 := by
    intro s hs h
    have := hv1 s hs
    rw [h, map_zero] at this
    exact zero_ne_one this
  haveI : q.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.mk'_surjective (S := K) (nonZeroDivisors R) e
  dsimp only at hxy
  rw [IsFractionRing.mk'_eq_div] at hxy
  have hy0 : (algebraMap R K y) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors y.2
  change ((x : R) : K) / ((y : R) : K) = e at hxy
  change ((y : R) : K) ≠ 0 at hy0
  by_cases hq : q = ⊥
  · have hyq : (y : R) ∉ q := by
      rw [hq, Ideal.mem_bot]
      intro h; apply hy0; rw [h]; rfl
    exact ⟨x, (x : R).2, y, (y : R).2, hinv _ hyq, hxy.symm⟩
  · have hmin : ∀ p : Ideal R, p.IsPrime → p ≠ ⊥ → p ≤ q → p = q := by
      intro p hp hp0 hpq
      refine le_antisymm hpq ?_
      intro r hr
      refine hyp p hp hp0 (fun t ht => ?_) r ?_
      · exact E.mem_nonunits_iff.2 ((hqmem t).1 (hpq ht))
      · exact E.mem_nonunits_iff.2 ((hqmem r).1 hr)
    haveI : ValuationRing (Localization.AtPrime q) := valuationRing_atPrime_of_minimal q hmin
    obtain ⟨c, hc⟩ := ValuationRing.cond (algebraMap R (Localization.AtPrime q) x)
      (algebraMap R (Localization.AtPrime q) y)
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (S := Localization.AtPrime q) q.primeCompl c
    dsimp only at hc
    have hsq : (s : R) ∉ q := s.2
    rcases hc with hc | hc
    · have h := mul_eq_mul_of_atPrime q _ _ _ _ hc
      have hK : ((x : R) : K) * (a : K) = ((y : R) : K) * ((s : R) : K) := by
        have := congrArg (fun t : R => (t : K)) h
        simpa using this
      by_cases haq : a ∈ q
      · exfalso
        have hea : e * (a : K) = ((s : R) : K) := by
          rw [← hxy]
          field_simp
          linear_combination hK
        have h1 := hv1 _ hsq
        rw [← hea, map_mul] at h1
        have hle : E.valuation e * E.valuation (a : K) ≤ E.valuation (a : K) :=
          mul_le_of_le_one_left' ((E.valuation_le_one_iff e).2 he)
        have := (hqmem a).1 haq
        rw [h1] at hle
        exact absurd (lt_of_le_of_lt hle this) (lt_irrefl 1)
      · refine ⟨((s : R) : K), (s : R).2, (a : K), a.2, hinv a haq, ?_⟩
        rw [← hxy, div_eq_div_iff hy0 (hne0 a haq)]
        linear_combination hK
    · have h := mul_eq_mul_of_atPrime q _ _ _ _ hc
      have hK : ((y : R) : K) * (a : K) = ((x : R) : K) * ((s : R) : K) := by
        have := congrArg (fun t : R => (t : K)) h
        simpa using this
      refine ⟨(a : K), a.2, ((s : R) : K), (s : R).2, hinv _ hsq, ?_⟩
      rw [← hxy, div_eq_div_iff hy0 (hne0 _ hsq)]
      linear_combination -hK

end GlobalTheory
