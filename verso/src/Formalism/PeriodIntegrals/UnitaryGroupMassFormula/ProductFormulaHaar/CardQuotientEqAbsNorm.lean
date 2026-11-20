import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.NormMod

noncomputable section

open IsDedekindDomain NumberField ValuativeRel

namespace PI.ProdFormulaE

/- English proof (translation)
Rewrite using `[v.intValuation_if_neg hs, ← Ideal.dvd_span_singleton]`. Conclude with `v.intValuation_le_pow_iff_dvd r _`.
-/
private theorem intValuation_le_iff_mem_maxPowDividing {R : Type*} [CommRing R] [IsDedekindDomain R]
    (v : HeightOneSpectrum R) (r s : R) (hs : s ≠ 0) :
    v.intValuation r ≤ v.intValuation s ↔ r ∈ v.maxPowDividing (Ideal.span {s}) := by
  rw [v.intValuation_if_neg hs, ← Ideal.dvd_span_singleton]
  exact v.intValuation_le_pow_iff_dvd r _

/- English proof (translation)
Take `⟨b, c, hc, rfl⟩` from `IsFractionRing.div_surjective (A := R) f`. Establish `hc0 : c ≠ 0` using `nonZeroDivisors.ne_zero hc`. Establish `hcK : algebraMap R K c ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hc0`. Establish `hpos : 0 < v.valuation K (algebraMap R K c)` using `zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hcK)`. Establish `hbc : v.intValuation b ≤ v.intValuation c`.

Rewrite `hf` using `[map_div₀, div_le_one₀ hpos]`. Simplify `hf` using `only [HeightOneSpectrum.valuation_of_algebraMap]`. Establish `hca : c * a ≠ 0` using `mul_ne_zero hc0 ha`. Take `⟨N, hN⟩ : ∃ N : ℕ, v.maxPowDividing (Ideal.span {c * a}) = v.asIdeal ^ N` from `⟨_, rfl⟩`. Establish `hS : Ideal.span {c} ⊔ v.asIdeal ^ N ∣ v.asIdeal ^ N` using `Ideal.dvd_iff_le.2 le_sup_right`.

Take `⟨k, -, hk⟩` from `(dvd_prime_pow v.prime N).1 hS`. Rewrite `hk` using `[associated_iff_eq]`. Establish `hbk : b ∈ v.asIdeal ^ k`. Rewrite using `[← Ideal.dvd_span_singleton]`. Apply `(v.intValuation_le_pow_iff_dvd b k).1` to reduce the goal to its premises.

Use `hbc.trans ((v.intValuation_le_pow_iff_dvd c k).2 ?_)` and prove the remaining obligations. Rewrite using `[← hk]`. Conclude with `Ideal.dvd_iff_le.2 le_sup_left`. Rewrite `hbk` using `[← hk]`. Take `⟨y, hy, z, hz, hyz⟩` from `Submodule.mem_sup.1 hbk`.

Take `⟨x, rfl⟩` from `Ideal.mem_span_singleton'.1 hy`. Use `⟨x, ?_⟩` and prove the remaining obligations. Establish `hzle : v.intValuation z ≤ v.intValuation (c * a)`. Rewrite using `[intValuation_le_iff_mem_maxPowDividing v z _ hca, hN]`. Conclude with `hz`.

Establish `hsub : algebraMap R K b / algebraMap R K c - algebraMap R K x = algebraMap R K z / algebraMap R K c`. Rewrite using `[← hyz, map_add, map_mul, add_div, mul_div_assoc, div_self hcK, mul_one, add_sub_cancel_left]`. Rewrite using `[hsub, map_div₀, div_le_iff₀ hpos]`. Simplify using `only [HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `hzle.trans_eq (by rw [map_mul, mul_comm])`.
-/
private theorem exists_valuation_sub_algebraMap_le {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) {f : K}
    (hf : v.valuation K f ≤ 1) {a : R} (ha : a ≠ 0) :
    ∃ x : R, v.valuation K (f - algebraMap R K x) ≤ v.valuation K (algebraMap R K a) := by
  obtain ⟨b, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := R) f
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hcK : algebraMap R K c ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hc0
  have hpos : 0 < v.valuation K (algebraMap R K c) :=
    zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hcK)
  have hbc : v.intValuation b ≤ v.intValuation c := by
    rw [map_div₀, div_le_one₀ hpos] at hf
    simpa only [HeightOneSpectrum.valuation_of_algebraMap] using hf
  have hca : c * a ≠ 0 := mul_ne_zero hc0 ha
  obtain ⟨N, hN⟩ : ∃ N : ℕ, v.maxPowDividing (Ideal.span {c * a}) = v.asIdeal ^ N := ⟨_, rfl⟩
  have hS : Ideal.span {c} ⊔ v.asIdeal ^ N ∣ v.asIdeal ^ N := Ideal.dvd_iff_le.2 le_sup_right
  obtain ⟨k, -, hk⟩ := (dvd_prime_pow v.prime N).1 hS
  rw [associated_iff_eq] at hk
  have hbk : b ∈ v.asIdeal ^ k := by
    rw [← Ideal.dvd_span_singleton]
    apply (v.intValuation_le_pow_iff_dvd b k).1
    refine hbc.trans ((v.intValuation_le_pow_iff_dvd c k).2 ?_)
    rw [← hk]
    exact Ideal.dvd_iff_le.2 le_sup_left
  rw [← hk] at hbk
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hbk
  obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  refine ⟨x, ?_⟩
  have hzle : v.intValuation z ≤ v.intValuation (c * a) := by
    rw [intValuation_le_iff_mem_maxPowDividing v z _ hca, hN]
    exact hz
  have hsub : algebraMap R K b / algebraMap R K c - algebraMap R K x =
      algebraMap R K z / algebraMap R K c := by
    rw [← hyz, map_add, map_mul, add_div, mul_div_assoc, div_self hcK, mul_one,
      add_sub_cancel_left]
  rw [hsub, map_div₀, div_le_iff₀ hpos]
  simp only [HeightOneSpectrum.valuation_of_algebraMap]
  exact hzle.trans_eq (by rw [map_mul, mul_comm])

/- English proof (translation)
Establish `h` using `Valuation.isOpen_closedBall (v := ValuativeRel.valuation K) (r := (ValuativeRel.valuation K).restrict r) (by simpa using hr)`. Simplify using `using h`.
-/
private theorem isOpen_setOf_valuation_le_of_ne_zero {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {r : K} (hr : r ≠ 0) :
    IsOpen {y : K | ValuativeRel.valuation K y ≤ ValuativeRel.valuation K r} := by
  have h := Valuation.isOpen_closedBall (v := ValuativeRel.valuation K)
    (r := (ValuativeRel.valuation K).restrict r) (by simpa using hr)
  simpa using h

/- English proof (translation)
Unfold `CardStep`. Introduce `F _ _ p K _ _ _ _ ι hι hv a ha t ht`. Establish `hcomp : ∀ x y : F, (ValuativeRel.valuation K) (ι x) ≤ (ValuativeRel.valuation K) (ι y) ↔ p.valuation F x ≤ p.valuation F y`. Introduce `x y`. Rewrite using `[← hv x y]`.

Conclude with `(Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation K) (ι x) (ι y)).symm`. Establish `haF : (a : F) ≠ 0`. Conclude with `(map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 ha`. Establish `htK : (t : K) ≠ 0`. Rewrite using `[ht]`.

Conclude with `(map_ne_zero ι).2 haF`. Establish `hdvd : ∀ u w : 𝒪[K], u ∣ w ↔ (ValuativeRel.valuation K) (w : K) ≤ (ValuativeRel.valuation K) (u : K)` using `fun u w => (Valuation.integer.integers (ValuativeRel.valuation K)).dvd_iff_le`. Establish `hint_r : ∀ x : 𝓞 F, ι (algebraMap (𝓞 F) F x) ∈ 𝒪[K]`. Introduce `x`. Rewrite using `[Valuation.mem_integer_iff]`.

Establish `h` using `(hcomp (algebraMap (𝓞 F) F x) 1).2 (by`. Rewrite using `[map_one]`. Conclude with `p.valuation_le_one x)`. Simplify using `using h`. Set `ι₀ : 𝓞 F →+* 𝒪[K]` to `(ι.comp (algebraMap (𝓞 F) F)).codRestrict 𝒪[K] hint_r`.

Set `φ : 𝓞 F →+* 𝒪[K] ⧸ Ideal.span {t}` to `(Ideal.Quotient.mk _).comp ι₀`. Establish `hker : RingHom.ker φ = p.maxPowDividing (Ideal.span {a})`. Use extensionality with `x`. Rewrite using `[RingHom.mem_ker]`. Use `show Ideal.Quotient.mk (Ideal.span {t}) (ι₀ x) = 0 ↔ _`.

Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, hdvd, ht]`. Use `show (ValuativeRel.valuation K) (ι (algebraMap (𝓞 F) F x)) ≤ (ValuativeRel.valuation K) (ι (algebraMap (𝓞 F) F a)) ↔ _`. Rewrite using `[hcomp, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `intValuation_le_iff_mem_maxPowDividing p x a ha`. Establish `hsurj : Function.Surjective φ`.

Introduce `q`. Take `⟨s, rfl⟩` from `Ideal.Quotient.mk_surjective q`. Establish `hU : IsOpen {y : K | (ValuativeRel.valuation K) (y - s) ≤ (ValuativeRel.valuation K) t}`. Establish `hB` using `isOpen_setOf_valuation_le_of_ne_zero htK`. Conclude with `hB.preimage (continuous_sub_right (s : K))`.

Take `⟨f, hf⟩` from `hι.exists_mem_open hU ⟨(s : K), by simp⟩`. Establish `hf' : (ValuativeRel.valuation K) (ι f - s) ≤ (ValuativeRel.valuation K) t` using `hf`. Establish `hfK : (ValuativeRel.valuation K) (ι f) ≤ 1`. Establish `h1 : (ValuativeRel.valuation K) (ι f - s) ≤ 1` using `hf'.trans ((Valuation.mem_integer_iff _ _).1 t.2)`. Establish `h2 : (ValuativeRel.valuation K) (s : K) ≤ 1` using `(Valuation.mem_integer_iff _ _).1 s.2`.

Simplify using `using (ValuativeRel.valuation K).map_add_le h1 h2`. Establish `hf1 : p.valuation F f ≤ 1`. Use `(hcomp f 1).1 (by simpa using hfK)` as an intermediate fact. Simplify using `using this`. Take `⟨x, hx⟩` from `exists_valuation_sub_algebraMap_le p hf1 ha`.

Use `⟨x, ?_⟩` and prove the remaining obligations. Use `show Ideal.Quotient.mk _ (ι₀ x) = Ideal.Quotient.mk _ s`. Rewrite using `[Ideal.Quotient.eq, Ideal.mem_span_singleton, hdvd]`. Establish `h3 : (ValuativeRel.valuation K) (ι (algebraMap (𝓞 F) F x) - ι f) ≤ (ValuativeRel.valuation K) t`. Rewrite using `[← map_sub, ht]`.

Use `show (ValuativeRel.valuation K) (ι (algebraMap (𝓞 F) F x - f)) ≤ (ValuativeRel.valuation K) (ι (algebraMap (𝓞 F) F a))`. Rewrite using `[hcomp, ← neg_sub, Valuation.map_neg]`. Conclude with `hx`. Establish `h4 : ι (algebraMap (𝓞 F) F x) - (s : K) = (ι (algebraMap (𝓞 F) F x) - ι f) + (ι f - s)` using `by ring`. Use `show (ValuativeRel.valuation K) (ι (algebraMap (𝓞 F) F x) - (s : K)) ≤ (ValuativeRel.valuation K) t`.

Rewrite using `[h4]`. Conclude with `(ValuativeRel.valuation K).map_add_le h3 hf'`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply, ← hker]`. Conclude with `Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv.symm`.
-/
theorem card_quotient_eq_absNorm : CardStep := by
  unfold CardStep
  intro F _ _ p K _ _ _ _ ι hι hv a ha t ht
  have hcomp : ∀ x y : F, (ValuativeRel.valuation K) (ι x) ≤ (ValuativeRel.valuation K) (ι y) ↔ p.valuation F x ≤ p.valuation F y := by
    intro x y
    rw [← hv x y]
    exact (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation K) (ι x) (ι y)).symm
  have haF : (a : F) ≠ 0 := by
    exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 ha
  have htK : (t : K) ≠ 0 := by
    rw [ht]
    exact (map_ne_zero ι).2 haF
  have hdvd : ∀ u w : 𝒪[K], u ∣ w ↔ (ValuativeRel.valuation K) (w : K) ≤ (ValuativeRel.valuation K) (u : K) := fun u w =>
    (Valuation.integer.integers (ValuativeRel.valuation K)).dvd_iff_le
  have hint_r : ∀ x : 𝓞 F, ι (algebraMap (𝓞 F) F x) ∈ 𝒪[K] := by
    intro x
    rw [Valuation.mem_integer_iff]
    have h := (hcomp (algebraMap (𝓞 F) F x) 1).2 (by
      rw [map_one]
      exact p.valuation_le_one x)
    simpa using h
  let ι₀ : 𝓞 F →+* 𝒪[K] := (ι.comp (algebraMap (𝓞 F) F)).codRestrict 𝒪[K] hint_r
  let φ : 𝓞 F →+* 𝒪[K] ⧸ Ideal.span {t} := (Ideal.Quotient.mk _).comp ι₀
  have hker : RingHom.ker φ = p.maxPowDividing (Ideal.span {a}) := by
    ext x
    rw [RingHom.mem_ker]
    show Ideal.Quotient.mk (Ideal.span {t}) (ι₀ x) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, hdvd, ht]
    show (ValuativeRel.valuation K) (ι (algebraMap (𝓞 F) F x)) ≤ (ValuativeRel.valuation K) (ι (algebraMap (𝓞 F) F a)) ↔ _
    rw [hcomp, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap]
    exact intValuation_le_iff_mem_maxPowDividing p x a ha
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
    have hU : IsOpen {y : K | (ValuativeRel.valuation K) (y - s) ≤ (ValuativeRel.valuation K) t} := by
      have hB := isOpen_setOf_valuation_le_of_ne_zero htK
      exact hB.preimage (continuous_sub_right (s : K))
    obtain ⟨f, hf⟩ := hι.exists_mem_open hU ⟨(s : K), by simp⟩
    have hf' : (ValuativeRel.valuation K) (ι f - s) ≤ (ValuativeRel.valuation K) t := hf
    have hfK : (ValuativeRel.valuation K) (ι f) ≤ 1 := by
      have h1 : (ValuativeRel.valuation K) (ι f - s) ≤ 1 := hf'.trans ((Valuation.mem_integer_iff _ _).1 t.2)
      have h2 : (ValuativeRel.valuation K) (s : K) ≤ 1 := (Valuation.mem_integer_iff _ _).1 s.2
      simpa using (ValuativeRel.valuation K).map_add_le h1 h2
    have hf1 : p.valuation F f ≤ 1 := by
      have := (hcomp f 1).1 (by simpa using hfK)
      simpa using this
    obtain ⟨x, hx⟩ := exists_valuation_sub_algebraMap_le p hf1 ha
    refine ⟨x, ?_⟩
    show Ideal.Quotient.mk _ (ι₀ x) = Ideal.Quotient.mk _ s
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, hdvd]
    have h3 : (ValuativeRel.valuation K) (ι (algebraMap (𝓞 F) F x) - ι f) ≤ (ValuativeRel.valuation K) t := by
      rw [← map_sub, ht]
      show (ValuativeRel.valuation K) (ι (algebraMap (𝓞 F) F x - f)) ≤ (ValuativeRel.valuation K) (ι (algebraMap (𝓞 F) F a))
      rw [hcomp, ← neg_sub, Valuation.map_neg]
      exact hx
    have h4 : ι (algebraMap (𝓞 F) F x) - (s : K) =
        (ι (algebraMap (𝓞 F) F x) - ι f) + (ι f - s) := by ring
    show (ValuativeRel.valuation K) (ι (algebraMap (𝓞 F) F x) - (s : K)) ≤ (ValuativeRel.valuation K) t
    rw [h4]
    exact (ValuativeRel.valuation K).map_add_le h3 hf'
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, ← hker]
  exact Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv.symm

end PI.ProdFormulaE
