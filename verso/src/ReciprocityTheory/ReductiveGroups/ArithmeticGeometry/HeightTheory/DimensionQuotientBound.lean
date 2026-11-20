import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AvPrimeDimOne

namespace ReciprocityTheory.ChartRestriction.G.T0.DimensionQuotientBound

open IsLocalRing

/- English proof (translation)
Rewrite using `[ringKrullDim_quotient]`. Set `a : PrimeSpectrum.zeroLocus (p : Set R)` to `⟨⟨p, hp⟩, fun x hx => hx⟩`. Set `b : PrimeSpectrum.zeroLocus (p : Set R)` to `⟨⟨P, hP⟩, fun x hx => h1.le hx⟩`. Set `c : PrimeSpectrum.zeroLocus (p : Set R)` to `⟨⟨m, hm⟩, fun x hx => (h1.trans h2).le hx⟩`. Establish `hab : a < b` using `h1`.

Establish `hbc : b < c` using `h2`. Apply the tactic sequence `have hs : ((2 : ℕ) : WithBot ℕ∞) ≤ Order.krullDim (PrimeSpectrum.zeroLocus (p : Set R)) := Order.LTSeries.length_le_krullDim (((RelSeries.singleton _ a).snoc b (by first | exact hab | exact ⟨_, _, rfl, hab⟩ | simpa using hab)).snoc c (by first | exact hbc | exact ⟨_, _, rfl, hbc⟩ …`. Conclude with `hs` after adjusting the coercions.
-/
lemma le_dim_quot {R : Type*} [CommRing R] (p P m : Ideal R) [hp : p.IsPrime] [hP : P.IsPrime]
    [hm : m.IsPrime] (h1 : p < P) (h2 : P < m) : (2 : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) := by
  rw [ringKrullDim_quotient]
  let a : PrimeSpectrum.zeroLocus (p : Set R) := ⟨⟨p, hp⟩, fun x hx => hx⟩
  let b : PrimeSpectrum.zeroLocus (p : Set R) := ⟨⟨P, hP⟩, fun x hx => h1.le hx⟩
  let c : PrimeSpectrum.zeroLocus (p : Set R) := ⟨⟨m, hm⟩, fun x hx => (h1.trans h2).le hx⟩
  have hab : a < b := h1
  have hbc : b < c := h2
  have hs : ((2 : ℕ) : WithBot ℕ∞) ≤ Order.krullDim (PrimeSpectrum.zeroLocus (p : Set R)) :=
    Order.LTSeries.length_le_krullDim (((RelSeries.singleton _ a).snoc b
      (by first | exact hab | exact ⟨_, _, rfl, hab⟩ | simpa using hab)).snoc c
      (by first | exact hbc | exact ⟨_, _, rfl, hbc⟩ | (simp only [RelSeries.last_snoc]; exact hbc) | simpa using hbc))
  exact_mod_cast hs

/- English proof (translation)
Set `a : PrimeSpectrum R` to `⟨p, inferInstance⟩`. Set `b : PrimeSpectrum R` to `⟨m, inferInstance⟩`. Establish `hab : a < b` using `h`. Establish `hs : ((1 : ℕ) : WithBot ℕ∞) ≤ Order.krullDim (PrimeSpectrum R)` using `Order.LTSeries.length_le_krullDim ((RelSeries.singleton _ a).snoc b hab)`. Conclude with `hs` after adjusting the coercions.
-/
lemma one_le_dim {R : Type*} [CommRing R] (p m : Ideal R) [p.IsPrime] [m.IsPrime] (h : p < m) :
    (1 : WithBot ℕ∞) ≤ ringKrullDim R := by
  let a : PrimeSpectrum R := ⟨p, inferInstance⟩
  let b : PrimeSpectrum R := ⟨m, inferInstance⟩
  have hab : a < b := h
  have hs : ((1 : ℕ) : WithBot ℕ∞) ≤ Order.krullDim (PrimeSpectrum R) :=
    Order.LTSeries.length_le_krullDim ((RelSeries.singleton _ a).snoc b hab)
  exact_mod_cast hs

/- English proof (translation)
Set `R` to `Localization.AtPrime M`. Use `haveI : IsDomain R := IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors M)`. Establish `hinj : Function.Injective (algebraMap B R)` using `IsLocalization.injective R (Ideal.primeCompl_le_nonZeroDivisors M)`. Establish `hcm : (IsLocalRing.maximalIdeal R).comap (algebraMap B R) = M` using `Localization.AtPrime.comap_maximalIdeal (I := M)`. Establish `hh : algebraMap B R (e * w) ≠ 0`.

Introduce `h`. Conclude with `mul_ne_zero he hw0 (hinj (by rw [h, map_zero]))`. Establish `hmax : (⊥ : Ideal R) < IsLocalRing.maximalIdeal R`. Rewrite using `[bot_lt_iff_ne_bot]`. Introduce `h`.

Establish `hw' : algebraMap B R w ∈ IsLocalRing.maximalIdeal R`. Rewrite using `[← Ideal.mem_comap, hcm]`. Conclude with `hw`. Rewrite `hw'` using `[h, Ideal.mem_bot]`. Conclude with `hw0 (hinj (by rw [hw', map_zero]))`.

Establish `hdim : 1 ≤ ringKrullDim R` using `one_le_dim ⊥ (IsLocalRing.maximalIdeal R) hmax`. Take `⟨p, hp, hpd, hpn⟩` from `ReciprocityTheory.ChartRestriction.G.T0.av_prime_dim_one hdim _ hh`. Use `haveI := hp`. Use `⟨p.comap (algebraMap B R), Ideal.comap_isPrime _ _, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`.

Rewrite using `[← hcm]`. Conclude with `IsLocalRing.le_maximalIdeal hp.ne_top hx`. Introduce `he'`. Apply `hpn` to reduce the goal to its premises. Rewrite using `[map_mul]`.

Conclude with `p.mul_mem_right _ he'`. Introduce `hw'`. Apply `hpn` to reduce the goal to its premises. Rewrite using `[map_mul]`. Conclude with `p.mul_mem_left _ hw'`.

Introduce `P hP hqP hPM hwP`. Assume the negation of the conclusion as `hne`. Establish `hdisj : Disjoint (M.primeCompl : Set B) P`. Rewrite using `[Set.disjoint_left]`. Introduce `x hx hxP`.

Conclude with `hx (hPM hxP)`. Use `haveI hP' : (P.map (algebraMap B R)).IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M.primeCompl R P hP hdisj`. Establish `hcomap : (P.map (algebraMap B R)).comap (algebraMap B R) = P` using `IsLocalization.comap_map_of_isPrime_disjoint M.primeCompl R hP hdisj`. Establish `h1 : p < P.map (algebraMap B R)`. Use `lt_of_le_of_ne ?_ ?_` and prove the remaining obligations.

Establish `hpe : (p.comap (algebraMap B R)).map (algebraMap B R) = p` using `IsLocalization.map_comap M.primeCompl R p`. Rewrite using `[← hpe]`. Conclude with `Ideal.map_mono hqP`. Introduce `heq`. Apply `hpn` to reduce the goal to its premises.

Rewrite using `[heq, map_mul]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hwP)`. Establish `h2 : P.map (algebraMap B R) < IsLocalRing.maximalIdeal R`. Use `lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hP'.ne_top) ?_` and prove the remaining obligations. Introduce `heq`.

Apply `hne` to reduce the goal to its premises. Rewrite using `[← hcomap, heq, hcm]`. Establish `h3` using `le_dim_quot p (P.map (algebraMap B R)) (IsLocalRing.maximalIdeal R) h1 h2`. Rewrite `h3` using `[hpd]`. Conclude with `absurd h3 (by decide)`.
-/
theorem local_step {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] (M : Ideal B) [hM : M.IsMaximal]
    (w e : B) (hw : w ∈ M) (hw0 : w ≠ 0) (he : e ≠ 0) :
    ∃ q : Ideal B, q.IsPrime ∧ q ≤ M ∧ e ∉ q ∧ w ∉ q ∧
      ∀ P : Ideal B, P.IsPrime → q ≤ P → P ≤ M → w ∈ P → P = M := by
  classical
  let R := Localization.AtPrime M
  haveI : IsDomain R := IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors M)
  have hinj : Function.Injective (algebraMap B R) :=
    IsLocalization.injective R (Ideal.primeCompl_le_nonZeroDivisors M)
  have hcm : (IsLocalRing.maximalIdeal R).comap (algebraMap B R) = M :=
    Localization.AtPrime.comap_maximalIdeal (I := M)
  have hh : algebraMap B R (e * w) ≠ 0 := by
    intro h
    exact mul_ne_zero he hw0 (hinj (by rw [h, map_zero]))
  have hmax : (⊥ : Ideal R) < IsLocalRing.maximalIdeal R := by
    rw [bot_lt_iff_ne_bot]
    intro h
    have hw' : algebraMap B R w ∈ IsLocalRing.maximalIdeal R := by
      rw [← Ideal.mem_comap, hcm]; exact hw
    rw [h, Ideal.mem_bot] at hw'
    exact hw0 (hinj (by rw [hw', map_zero]))
  have hdim : 1 ≤ ringKrullDim R := one_le_dim ⊥ (IsLocalRing.maximalIdeal R) hmax
  obtain ⟨p, hp, hpd, hpn⟩ := ReciprocityTheory.ChartRestriction.G.T0.av_prime_dim_one hdim _ hh
  haveI := hp
  refine ⟨p.comap (algebraMap B R), Ideal.comap_isPrime _ _, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [← hcm]
    exact IsLocalRing.le_maximalIdeal hp.ne_top hx
  · intro he'
    apply hpn
    rw [map_mul]
    exact p.mul_mem_right _ he'
  · intro hw'
    apply hpn
    rw [map_mul]
    exact p.mul_mem_left _ hw'
  · intro P hP hqP hPM hwP
    by_contra hne
    have hdisj : Disjoint (M.primeCompl : Set B) P := by
      rw [Set.disjoint_left]
      intro x hx hxP
      exact hx (hPM hxP)
    haveI hP' : (P.map (algebraMap B R)).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint M.primeCompl R P hP hdisj
    have hcomap : (P.map (algebraMap B R)).comap (algebraMap B R) = P :=
      IsLocalization.comap_map_of_isPrime_disjoint M.primeCompl R hP hdisj
    have h1 : p < P.map (algebraMap B R) := by
      refine lt_of_le_of_ne ?_ ?_
      · have hpe : (p.comap (algebraMap B R)).map (algebraMap B R) = p :=
          IsLocalization.map_comap M.primeCompl R p
        rw [← hpe]
        exact Ideal.map_mono hqP
      · intro heq
        apply hpn
        rw [heq, map_mul]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hwP)
    have h2 : P.map (algebraMap B R) < IsLocalRing.maximalIdeal R := by
      refine lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hP'.ne_top) ?_
      intro heq
      apply hne
      rw [← hcomap, heq, hcm]
    have h3 := le_dim_quot p (P.map (algebraMap B R)) (IsLocalRing.maximalIdeal R) h1 h2
    rw [hpd] at h3
    exact absurd h3 (by decide)

end ReciprocityTheory.ChartRestriction.G.T0.DimensionQuotientBound
