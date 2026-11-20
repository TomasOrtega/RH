import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChPrime
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Monomial
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsMulMemOfAlgebraMapLocRingEqZero
import ReciprocityTheory.AnalyticForms.RegularLocalRings.StalkLoc

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par

open MvPolynomial ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages GlobalTheory.CompanionTheory.Ar.Cmp

variable {m : ℕ}

/- English proof (translation)
Establish `halg : algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t) h = Ideal.Quotient.mk _ (algebraMap _ (locPt t) h)` using `rfl`. Rewrite using `[halg, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.mem_map_of_mem _ hh`.
-/
theorem algebraMap_locRing_eq_zero_of_mem {I : Ideal (MvPolynomial (Fin m) ℂ)} (t : Fin m → ℂ)
    {h : MvPolynomial (Fin m) ℂ} (hh : h ∈ I) : algebraMap _ (locRing I t) h = 0 := by
  have halg : algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t) h =
      Ideal.Quotient.mk _ (algebraMap _ (locPt t) h) := rfl
  rw [halg, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_map_of_mem _ hh

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `g hg`. Rewrite using `[Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_algebraMap_locRing_iff I t hI]`. Simplify using `using RingHom.mem_ker.mp hg`.

Introduce `x hx`. Take `⟨a, b, hb, hab⟩` from `exists_mk_locRing I t x`. Establish `hbu` using `(isUnit_algebraMap_locRing_iff I t hI b).mpr hb`. Establish `ha : a ∈ ptIdeal t`. Use `RingHom.mem_ker.mpr ?_` and prove the remaining obligations.

Assume the negation of the conclusion as `hne`. Establish `hau` using `(isUnit_algebraMap_locRing_iff I t hI a).mpr hne`. Rewrite `hau` using `[← hab]`. Conclude with `((IsLocalRing.mem_maximalIdeal _).mp hx) (isUnit_of_mul_isUnit_left hau)`. Take `⟨v, hv⟩` from `hbu.exists_right_inv`.

Establish `: x = algebraMap _ (locRing I t) a * v`. Rewrite using `[← hab, mul_assoc, hv, mul_one]`. Rewrite using `[this]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)`.
-/
theorem map_ptIdeal_eq_maximalIdeal {I : Ideal (MvPolynomial (Fin m) ℂ)} {t : Fin m → ℂ}
    (hI : ∀ h ∈ I, eval t h = 0) [IsLocalRing (locRing I t)] :
    Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) = IsLocalRing.maximalIdeal (locRing I t) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      isUnit_algebraMap_locRing_iff I t hI]
    simpa using RingHom.mem_ker.mp hg
  · intro x hx
    obtain ⟨a, b, hb, hab⟩ := exists_mk_locRing I t x
    have hbu := (isUnit_algebraMap_locRing_iff I t hI b).mpr hb
    have ha : a ∈ ptIdeal t := by
      refine RingHom.mem_ker.mpr ?_
      by_contra hne
      have hau := (isUnit_algebraMap_locRing_iff I t hI a).mpr hne
      rw [← hab] at hau
      exact ((IsLocalRing.mem_maximalIdeal _).mp hx) (isUnit_of_mul_isUnit_left hau)
    obtain ⟨v, hv⟩ := hbu.exists_right_inv
    have : x = algebraMap _ (locRing I t) a * v := by
      rw [← hab, mul_assoc, hv, mul_one]
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)

/- English proof (translation)
Introduce `g hg`. Take `⟨a, ha⟩` from `Ideal.mem_span_singleton'.mp (Ideal.mem_comap.mp hg)`. Take `⟨a₀, b₀, hb₀, hab⟩` from `exists_mk_locRing I t a`. Establish `hz : algebraMap _ (locRing I t) (b₀ * g - a₀ * f) = 0`. Rewrite using `[map_sub, map_mul, map_mul, ← ha, ← hab]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨s, hs, hsI⟩` from `exists_mul_mem_of_algebraMap_locRing_eq_zero I t hz`. Establish `hmem : (s * b₀) * g ∈ 𝔮`. Establish `h1` using `𝔮.add_mem (hI𝔮 hsI) (𝔮.mul_mem_left (s * a₀) hf)`. Establish `h2 : s * (b₀ * g - a₀ * f) + s * a₀ * f = (s * b₀) * g` using `by ring`.

Rewrite `h1` using `[h2]`. Then use the resulting hypothesis. Use `(h𝔮.mem_or_mem hmem).resolve_left fun hc => ?_` and prove the remaining obligations. Use `RingHom.mem_ker.mp (h𝔮t hc)` as an intermediate fact. Rewrite `this` using `[map_mul]`. Conclude with `mul_ne_zero hs hb₀ this`.
-/
theorem chPrime_le_of_mem {I 𝔮 : Ideal (MvPolynomial (Fin m) ℂ)} {t : Fin m → ℂ}
    {f : MvPolynomial (Fin m) ℂ} (h𝔮 : 𝔮.IsPrime) (hI𝔮 : I ≤ 𝔮) (h𝔮t : 𝔮 ≤ ptIdeal t)
    (hf : f ∈ 𝔮) : chPrime I t f ≤ 𝔮 := by
  intro g hg
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp (Ideal.mem_comap.mp hg)
  obtain ⟨a₀, b₀, hb₀, hab⟩ := exists_mk_locRing I t a
  have hz : algebraMap _ (locRing I t) (b₀ * g - a₀ * f) = 0 := by
    rw [map_sub, map_mul, map_mul, ← ha, ← hab]
    ring
  obtain ⟨s, hs, hsI⟩ := exists_mul_mem_of_algebraMap_locRing_eq_zero I t hz
  have hmem : (s * b₀) * g ∈ 𝔮 := by
    have h1 := 𝔮.add_mem (hI𝔮 hsI) (𝔮.mul_mem_left (s * a₀) hf)
    have h2 : s * (b₀ * g - a₀ * f) + s * a₀ * f = (s * b₀) * g := by ring
    rwa [h2] at h1
  refine (h𝔮.mem_or_mem hmem).resolve_left fun hc => ?_
  have := RingHom.mem_ker.mp (h𝔮t hc)
  rw [map_mul] at this
  exact mul_ne_zero hs hb₀ this

/- English proof (translation)
Introduce `m e I Dc t r Jf hIDc hI hreg hdim hspan hDc i hi`. Use `haveI := hreg`. Use `haveI : IsDomain (locRing I t) := isDomain_of_isRegularLocalRing`. Establish `hmax` using `map_ptIdeal_eq_maximalIdeal hI`. Establish `hspan' : Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) = IsLocalRing.maximalIdeal (locRing I t)` using `hspan.trans hmax`.

Establish `hprime : ∀ l, Prime (algebraMap _ (locRing I t) (r l))` using `prime_of_regular_params (fun l => algebraMap _ (locRing I t) (r l)) hspan' hdim.symm`. Establish `hnassoc` using `(regular_params_spec (fun l => algebraMap _ (locRing I t) (r l)) hspan' hdim.symm).2`. Establish `hIt : I ≤ ptIdeal t` using `fun h hh => RingHom.mem_ker.mpr (hI h hh)`. Establish `hRi : r i ∈ chPrime I t (r i)` using `Ideal.mem_comap.mpr (Ideal.mem_span_singleton_self _)`. Establish `hle : chPrime I t (r i) ≤ ptIdeal t`.

Introduce `g hg`. Establish `hg' : algebraMap _ (locRing I t) g ∈ Ideal.span {algebraMap _ (locRing I t) (r i)}` using `Ideal.mem_comap.mp hg`. Establish `hsub : Ideal.span {algebraMap _ (locRing I t) (r i)} ≤ IsLocalRing.maximalIdeal (locRing I t)`. Rewrite using `[Ideal.span_singleton_le_iff_mem, ← hspan']`. Conclude with `Ideal.subset_span ⟨i, rfl⟩`.

Establish `hnu` using `(IsLocalRing.mem_maximalIdeal _).mp (hsub hg')`. Use `RingHom.mem_ker.mpr ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Conclude with `hnu ((isUnit_algebraMap_locRing_iff I t hI g).mpr hne)`. Establish `hpr : (chPrime I t (r i)).IsPrime` using `by haveI : (Ideal.span {algebraMap _ (locRing I t) (r i)}).IsPrime := (Ideal.span_singleton_prime (hprime i).ne_zero).mpr (hprime i)`.

Conclude with `Ideal.comap_isPrime _ _`. Establish `hIle : I ≤ chPrime I t (r i)`. Introduce `h hh`. Use `Ideal.mem_comap.mpr ?_` and prove the remaining obligations. Rewrite using `[algebraMap_locRing_eq_zero_of_mem t hh]`.

Conclude with `Ideal.zero_mem _`. Use `⟨hpr, hIle, hle, (hDc _ hpr hIle hle).mpr ⟨i, hi, hRi⟩, hRi, ?_, ?_⟩` and prove the remaining obligations. Introduce `j _ hji hj`. Establish `hd : algebraMap _ (locRing I t) (r i) ∣ algebraMap _ (locRing I t) (r j)` using `Ideal.mem_span_singleton.mp (Ideal.mem_comap.mp hj)`. Conclude with `hnassoc i j (Ne.symm hji) ((hprime i).associated_of_dvd (hprime j) hd)`.

Introduce `𝔮 h𝔮 hI𝔮 h𝔮t hr`. Conclude with `chPrime_le_of_mem h𝔮 hI𝔮 h𝔮t hr`.
-/
theorem primes_below_params : ∀ (m e : ℕ) (I Dc : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ) (r : Fin e → MvPolynomial (Fin m) ℂ) (Jf : Finset (Fin e)), I ≤ Dc → (∀ h ∈ I, eval t h = 0) → IsRegularLocalRing (locRing I t) → ringKrullDim (locRing I t) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) = Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) → (∀ 𝔮 : Ideal (MvPolynomial (Fin m) ℂ), 𝔮.IsPrime → I ≤ 𝔮 → 𝔮 ≤ ptIdeal t → (Dc ≤ 𝔮 ↔ ∃ i ∈ Jf, r i ∈ 𝔮)) → ∀ i ∈ Jf, (SncRes.Par.chPrime I t (r i)).IsPrime ∧ I ≤ SncRes.Par.chPrime I t (r i) ∧ SncRes.Par.chPrime I t (r i) ≤ ptIdeal t ∧ Dc ≤ SncRes.Par.chPrime I t (r i) ∧ r i ∈ SncRes.Par.chPrime I t (r i) ∧ (∀ j ∈ Jf, j ≠ i → r j ∉ SncRes.Par.chPrime I t (r i)) ∧ ∀ 𝔮 : Ideal (MvPolynomial (Fin m) ℂ), 𝔮.IsPrime → I ≤ 𝔮 → 𝔮 ≤ ptIdeal t → r i ∈ 𝔮 → SncRes.Par.chPrime I t (r i) ≤ 𝔮 := by
  intro m e I Dc t r Jf hIDc hI hreg hdim hspan hDc i hi
  haveI := hreg
  haveI : IsDomain (locRing I t) := isDomain_of_isRegularLocalRing
  have hmax := map_ptIdeal_eq_maximalIdeal hI
  have hspan' : Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) =
      IsLocalRing.maximalIdeal (locRing I t) := hspan.trans hmax
  have hprime : ∀ l, Prime (algebraMap _ (locRing I t) (r l)) :=
    prime_of_regular_params (fun l => algebraMap _ (locRing I t) (r l)) hspan' hdim.symm
  have hnassoc := (regular_params_spec (fun l => algebraMap _ (locRing I t) (r l)) hspan' hdim.symm).2
  have hIt : I ≤ ptIdeal t := fun h hh => RingHom.mem_ker.mpr (hI h hh)
  have hRi : r i ∈ chPrime I t (r i) := Ideal.mem_comap.mpr (Ideal.mem_span_singleton_self _)
  have hle : chPrime I t (r i) ≤ ptIdeal t := by
    intro g hg
    have hg' : algebraMap _ (locRing I t) g ∈ Ideal.span {algebraMap _ (locRing I t) (r i)} :=
      Ideal.mem_comap.mp hg
    have hsub : Ideal.span {algebraMap _ (locRing I t) (r i)} ≤ IsLocalRing.maximalIdeal (locRing I t) := by
      rw [Ideal.span_singleton_le_iff_mem, ← hspan']
      exact Ideal.subset_span ⟨i, rfl⟩
    have hnu := (IsLocalRing.mem_maximalIdeal _).mp (hsub hg')
    refine RingHom.mem_ker.mpr ?_
    by_contra hne
    exact hnu ((isUnit_algebraMap_locRing_iff I t hI g).mpr hne)
  have hpr : (chPrime I t (r i)).IsPrime := by
    haveI : (Ideal.span {algebraMap _ (locRing I t) (r i)}).IsPrime :=
      (Ideal.span_singleton_prime (hprime i).ne_zero).mpr (hprime i)
    exact Ideal.comap_isPrime _ _
  have hIle : I ≤ chPrime I t (r i) := by
    intro h hh
    refine Ideal.mem_comap.mpr ?_
    rw [algebraMap_locRing_eq_zero_of_mem t hh]
    exact Ideal.zero_mem _
  refine ⟨hpr, hIle, hle, (hDc _ hpr hIle hle).mpr ⟨i, hi, hRi⟩, hRi, ?_, ?_⟩
  · intro j _ hji hj
    have hd : algebraMap _ (locRing I t) (r i) ∣ algebraMap _ (locRing I t) (r j) :=
      Ideal.mem_span_singleton.mp (Ideal.mem_comap.mp hj)
    exact hnassoc i j (Ne.symm hji) ((hprime i).associated_of_dvd (hprime j) hd)
  · intro 𝔮 h𝔮 hI𝔮 h𝔮t hr
    exact chPrime_le_of_mem h𝔮 hI𝔮 h𝔮t hr

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
