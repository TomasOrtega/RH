import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

/- English proof (translation)
Introduce `hA E _ _ _ A`. Set `F : Type` to `maximalRealSubfield E`. Establish `hcF : (A.c : E) ∈ maximalRealSubfield E`. Rewrite using `[← IsCMField.complexConj_eq_self_iff E, ← A.bar_eq, A.c_real]`. Set `cf : F` to `⟨(A.c : E), hcF⟩`.

Establish `hcfE : algebraMap F E cf = (A.c : E)` using `rfl`. Establish `hcint : IsIntegral ℤ cf`. Establish `h : IsIntegral ℤ (algebraMap F E cf)` using `by rw [hcfE]; exact A.c.2`. Conclude with `(isIntegral_algebraMap_iff (algebraMap F E).injective).1 h`. Set `c0 : 𝓞 F` to `⟨cf, hcint⟩`.

Establish `hc0 : ((c0 : 𝓞 F) : F) = cf` using `rfl`. Establish `hc0ne : c0 ≠ 0`. Introduce `h`. Establish `h1 : ((c0 : 𝓞 F) : F) = 0` using `by rw [h]; simp`. Establish `h2 : (A.c : E) = 0`.

Rewrite using `[← hcfE, ← hc0, h1, map_zero]`. Conclude with `A.c_ne h2`. Take `⟨a, ha1, ha2⟩` from `hA F A.tr A.nm A.disc_neg.ne c0 hc0ne`. Set `ι` to `GlobalTheory.AdeleBaseChange.adMap F E`. Set `ω' : FiniteAdeleRing (𝓞 E) E` to `algebraMap E (FiniteAdeleRing (𝓞 E) E) (A.ω : E)`.

Set `ωb : FiniteAdeleRing (𝓞 E) E` to `algebraMap E (FiniteAdeleRing (𝓞 E) E) ((A.bar A.ω : 𝓞 E) : E)`. Establish `hfix : ∀ x : F, (IsCMField.complexConj E).toRingEquiv (algebraMap F E x) = algebraMap F E x` using `fun x => (IsCMField.complexConj_eq_self_iff E _).2 x.2`. Establish `hcι : ∀ z, cF E (ι z) = ι z` using `fun z => GlobalTheory.DefU.ClassFin.conjFin_adMap _ hfix z`. Establish `hcω : cF E ω' = ωb` using `by show conjFin _ (algebraMap E _ _) = _`. Rewrite using `[conjFin_algebraMap]`.

Use `show algebraMap E _ (IsCMField.complexConj E (A.ω : E)) = _`. Rewrite using `[← A.bar_eq]`. Establish `hsum : ω' + ωb = (A.tr : FiniteAdeleRing (𝓞 E) E)`. Establish `h : (A.ω : E) + ((A.bar A.ω : 𝓞 E) : E) = (A.tr : E)`. Use `congrArg (fun t : 𝓞 E => (t : E)) A.tr_eq` as an intermediate fact.

Simplify using `using this`. Use `show algebraMap E _ _ + algebraMap E _ _ = _`. Rewrite using `[← map_add, h, map_intCast]`. Establish `hprod : ω' * ωb = (A.nm : FiniteAdeleRing (𝓞 E) E)`. Establish `h : (A.ω : E) * ((A.bar A.ω : 𝓞 E) : E) = (A.nm : E)`.

Use `congrArg (fun t : 𝓞 E => (t : E)) A.nm_eq` as an intermediate fact. Simplify using `using this`. Use `show algebraMap E _ _ * algebraMap E _ _ = _`. Rewrite using `[← map_mul, h, map_intCast]`. Establish `hnorm : ∀ s t, (ι s + ι t * ω') * cF E (ι s + ι t * ω') = ι (qf A.tr A.nm s t)`.

Introduce `s t`. Rewrite using `[map_add, map_mul, hcι, hcι, hcω]`. Simplify using `only [qf, map_add, map_mul, map_pow, map_intCast]`. Take the linear combination `(ι s * ι t) * hsum + (ι t) ^ 2 * hprod`. Establish `hcalg : algebraMap E (FiniteAdeleRing (𝓞 E) E) (A.c : E) = ι (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((c0 : 𝓞 F) : F))`.

Rewrite using `[GlobalTheory.AdeleBaseChange.adMap_algebraMap]`. Both sides reduce to the same expression. Use `⟨ι (a 0) + ι (a 1) * ω', ι (a 2) + ι (a 3) * ω', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hnorm, hnorm, hcalg, ← map_add, ← map_mul, ha1, map_one]`. Introduce `w q hq hG hqw`.

Set `v : HeightOneSpectrum (𝓞 F)` to `w.under (𝓞 F)`. Establish `hqv : (q : 𝓞 F) ∈ v.asIdeal` using `by show algebraMap (𝓞 F) (𝓞 E) (q : 𝓞 F) ∈ w.asIdeal`. Rewrite using `[map_natCast]`. Conclude with `hqw`. Establish `hcv : c0 ∉ v.asIdeal`.

Introduce `hc`. Establish `hcw : A.c ∈ w.asIdeal` using `hc`. Take `⟨e, hcop, -, c', hc'⟩` from `hG.2`. Establish `hew : (e : 𝓞 E) ∈ w.asIdeal` using `hc' ▸ w.asIdeal.mul_mem_right c' hcw`. Establish `hb` using `Nat.isCoprime_iff_coprime.2 hcop`.

Take `⟨u, u', huu⟩` from `hb`. Establish `h1 : (1 : 𝓞 E) ∈ w.asIdeal`. Establish `h2 : (u : 𝓞 E) * (e : 𝓞 E) + (u' : 𝓞 E) * (q : 𝓞 E) = 1` using `by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) huu`. Rewrite using `[← h2]`. Conclude with `w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hew) (w.asIdeal.mul_mem_left _ hqw)`.

Conclude with `w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)`. Establish `hai : ∀ i, a i v ∈ v.adicCompletionIntegers F` using `ha2 v q hq hqv hG.1.1 hG.1.2 hcv`. Establish `hιi : ∀ i, pLoc E w (ι (a i)) ∈ w.adicCompletionIntegers E` using `fun i => GlobalTheory.AdeleBaseChange.locMap_int w _ (hai i)`. Establish `hωi : pLoc E w ω' ∈ w.adicCompletionIntegers E` using `HeightOneSpectrum.coe_mem_adicCompletionIntegers w A.ω`. Establish `hωbi : pLoc E w ωb ∈ w.adicCompletionIntegers E` using `HeightOneSpectrum.coe_mem_adicCompletionIntegers w (A.bar A.ω)`.

Establish `hform : ∀ i j, pLoc E w (ι (a i) + ι (a j) * ω') ∈ w.adicCompletionIntegers E` using `fun i j => by`. Rewrite using `[map_add, map_mul]`. Conclude with `add_mem (hιi i) (mul_mem (hιi j) hωi)`. Establish `hformc : ∀ i j, pLoc E w (cF E (ι (a i) + ι (a j) * ω')) ∈ w.adicCompletionIntegers E` using `fun i j => by`. Rewrite using `[map_add, map_mul, hcι, hcι, hcω, map_add, map_mul]`.

Conclude with `add_mem (hιi i) (mul_mem (hιi j) hωbi)`. Conclude with `⟨hform 0 1, hform 2 3, hformc 0 1, hformc 2 3⟩`.
-/
theorem UpperTheory.Gal.G1.pNormTwo :
    AdFour → NormTwo := by
  intro hA E _ _ _ A
  let F : Type := maximalRealSubfield E
  have hcF : (A.c : E) ∈ maximalRealSubfield E := by
    rw [← IsCMField.complexConj_eq_self_iff E, ← A.bar_eq, A.c_real]
  let cf : F := ⟨(A.c : E), hcF⟩
  have hcfE : algebraMap F E cf = (A.c : E) := rfl
  have hcint : IsIntegral ℤ cf := by
    have h : IsIntegral ℤ (algebraMap F E cf) := by rw [hcfE]; exact A.c.2
    exact (isIntegral_algebraMap_iff (algebraMap F E).injective).1 h
  let c0 : 𝓞 F := ⟨cf, hcint⟩
  have hc0 : ((c0 : 𝓞 F) : F) = cf := rfl
  have hc0ne : c0 ≠ 0 := by
    intro h
    have h1 : ((c0 : 𝓞 F) : F) = 0 := by rw [h]; simp
    have h2 : (A.c : E) = 0 := by
      rw [← hcfE, ← hc0, h1, map_zero]
    exact A.c_ne h2
  obtain ⟨a, ha1, ha2⟩ := hA F A.tr A.nm A.disc_neg.ne c0 hc0ne
  let ι := GlobalTheory.AdeleBaseChange.adMap F E
  let ω' : FiniteAdeleRing (𝓞 E) E := algebraMap E (FiniteAdeleRing (𝓞 E) E) (A.ω : E)
  let ωb : FiniteAdeleRing (𝓞 E) E := algebraMap E (FiniteAdeleRing (𝓞 E) E) ((A.bar A.ω : 𝓞 E) : E)
  have hfix : ∀ x : F, (IsCMField.complexConj E).toRingEquiv (algebraMap F E x) = algebraMap F E x := fun x =>
    (IsCMField.complexConj_eq_self_iff E _).2 x.2
  have hcι : ∀ z, cF E (ι z) = ι z := fun z => GlobalTheory.DefU.ClassFin.conjFin_adMap _ hfix z
  have hcω : cF E ω' = ωb := by
    show conjFin _ (algebraMap E _ _) = _
    rw [conjFin_algebraMap]
    show algebraMap E _ (IsCMField.complexConj E (A.ω : E)) = _
    rw [← A.bar_eq]
  have hsum : ω' + ωb = (A.tr : FiniteAdeleRing (𝓞 E) E) := by
    have h : (A.ω : E) + ((A.bar A.ω : 𝓞 E) : E) = (A.tr : E) := by
      have := congrArg (fun t : 𝓞 E => (t : E)) A.tr_eq
      simpa using this
    show algebraMap E _ _ + algebraMap E _ _ = _
    rw [← map_add, h, map_intCast]
  have hprod : ω' * ωb = (A.nm : FiniteAdeleRing (𝓞 E) E) := by
    have h : (A.ω : E) * ((A.bar A.ω : 𝓞 E) : E) = (A.nm : E) := by
      have := congrArg (fun t : 𝓞 E => (t : E)) A.nm_eq
      simpa using this
    show algebraMap E _ _ * algebraMap E _ _ = _
    rw [← map_mul, h, map_intCast]
  have hnorm : ∀ s t, (ι s + ι t * ω') * cF E (ι s + ι t * ω') = ι (qf A.tr A.nm s t) := by
    intro s t
    rw [map_add, map_mul, hcι, hcι, hcω]
    simp only [qf, map_add, map_mul, map_pow, map_intCast]
    linear_combination (ι s * ι t) * hsum + (ι t) ^ 2 * hprod
  have hcalg : algebraMap E (FiniteAdeleRing (𝓞 E) E) (A.c : E) =
      ι (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((c0 : 𝓞 F) : F)) := by
    rw [GlobalTheory.AdeleBaseChange.adMap_algebraMap]
    rfl
  refine ⟨ι (a 0) + ι (a 1) * ω', ι (a 2) + ι (a 3) * ω', ?_, ?_⟩
  · rw [hnorm, hnorm, hcalg, ← map_add, ← map_mul, ha1, map_one]
  · intro w q hq hG hqw
    let v : HeightOneSpectrum (𝓞 F) := w.under (𝓞 F)
    have hqv : (q : 𝓞 F) ∈ v.asIdeal := by
      show algebraMap (𝓞 F) (𝓞 E) (q : 𝓞 F) ∈ w.asIdeal
      rw [map_natCast]
      exact hqw
    have hcv : c0 ∉ v.asIdeal := by
      intro hc
      have hcw : A.c ∈ w.asIdeal := hc
      obtain ⟨e, hcop, -, c', hc'⟩ := hG.2
      have hew : (e : 𝓞 E) ∈ w.asIdeal := hc' ▸ w.asIdeal.mul_mem_right c' hcw
      have hb := Nat.isCoprime_iff_coprime.2 hcop
      obtain ⟨u, u', huu⟩ := hb
      have h1 : (1 : 𝓞 E) ∈ w.asIdeal := by
        have h2 : (u : 𝓞 E) * (e : 𝓞 E) + (u' : 𝓞 E) * (q : 𝓞 E) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) huu
        rw [← h2]
        exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hew) (w.asIdeal.mul_mem_left _ hqw)
      exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
    have hai : ∀ i, a i v ∈ v.adicCompletionIntegers F :=
      ha2 v q hq hqv hG.1.1 hG.1.2 hcv
    have hιi : ∀ i, pLoc E w (ι (a i)) ∈ w.adicCompletionIntegers E := fun i =>
      GlobalTheory.AdeleBaseChange.locMap_int w _ (hai i)
    have hωi : pLoc E w ω' ∈ w.adicCompletionIntegers E :=
      HeightOneSpectrum.coe_mem_adicCompletionIntegers w A.ω
    have hωbi : pLoc E w ωb ∈ w.adicCompletionIntegers E :=
      HeightOneSpectrum.coe_mem_adicCompletionIntegers w (A.bar A.ω)
    have hform : ∀ i j, pLoc E w (ι (a i) + ι (a j) * ω') ∈ w.adicCompletionIntegers E := fun i j => by
      rw [map_add, map_mul]
      exact add_mem (hιi i) (mul_mem (hιi j) hωi)
    have hformc : ∀ i j, pLoc E w (cF E (ι (a i) + ι (a j) * ω')) ∈ w.adicCompletionIntegers E := fun i j => by
      rw [map_add, map_mul, hcι, hcι, hcω, map_add, map_mul]
      exact add_mem (hιi i) (mul_mem (hιi j) hωbi)
    exact ⟨hform 0 1, hform 2 3, hformc 0 1, hformc 2 3⟩
