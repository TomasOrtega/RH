import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NilpotentOfNotIsUnit

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc PowerSeries

namespace GlobalTheory.Cyc.IoMap

section General

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/- English proof (translation)
Rewrite using `[X_pow_dvd_iff]`. Introduce `m hm`. Simplify using `[coeff_trunc, hm]`.
-/
theorem X_pow_dvd_sub_trunc (a : R⟦X⟧) (n : ℕ) :
    (X : R⟦X⟧) ^ n ∣ a - (trunc n a : Polynomial R) := by
  rw [X_pow_dvd_iff]
  intro m hm
  simp [coeff_trunc, hm]

/- English proof (translation)
Establish `: f.comp (Polynomial.coeToPowerSeries.algHom R) = Polynomial.aeval (f X)`. Use `ext`. Simplify using the standard rewrite rules. Simplify using `using DFunLike.congr_fun this p`.
-/
theorem algHom_coe (f : R⟦X⟧ →ₐ[R] A) (p : Polynomial R) :
    f (p : R⟦X⟧) = Polynomial.aeval (f X) p := by
  have : f.comp (Polynomial.coeToPowerSeries.algHom R) = Polynomial.aeval (f X) := by
    ext
    simp
  simpa using DFunLike.congr_fun this p

/- English proof (translation)
Use extensionality with `a`. Rewrite using `[← sub_eq_zero]`. Use `hs _ fun n => ?_` and prove the remaining obligations. Take `⟨b, hb⟩` from `X_pow_dvd_sub_trunc a n`. Establish `h1` using `congrArg f hb`.

Establish `h2` using `congrArg g hb`. Rewrite `h1`, `h2` using `[map_sub, map_mul, map_pow, algHom_coe]`. Rewrite `h2` using `[← h]`. Conclude with `⟨f b - g b, by linear_combination h1 - h2⟩`.
-/
theorem algHom_unique (f g : R⟦X⟧ →ₐ[R] A) (h : f X = g X)
    (hs : ∀ x : A, (∀ n, f X ^ n ∣ x) → x = 0) : f = g := by
  ext a
  rw [← sub_eq_zero]
  refine hs _ fun n => ?_
  obtain ⟨b, hb⟩ := X_pow_dvd_sub_trunc a n
  have h1 := congrArg f hb
  have h2 := congrArg g hb
  rw [map_sub, map_mul, map_pow, algHom_coe] at h1 h2
  rw [← h] at h2
  exact ⟨f b - g b, by linear_combination h1 - h2⟩

/- English proof (translation)
Establish `h1 : ∀ a : R⟦X⟧, ∃ L : A, ∀ n, y ^ n ∣ L - Polynomial.aeval y (trunc n a)`. Introduce `a`. Take `⟨L, hL⟩` from `hc fun i => algebraMap R A (coeff i a)`. Use `⟨L, fun n => ?_⟩` and prove the remaining obligations. Establish `e : Polynomial.aeval y (trunc n a) = ∑ i ∈ Finset.range n, y ^ i * algebraMap R A (coeff i a)`.

Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[trunc_succ, map_add, ih, Finset.sum_range_succ, Polynomial.aeval_monomial, mul_comm]`. Rewrite using `[e]`.

Conclude with `Ideal.mem_span_singleton.1 (hL n)`. Use `choose L hL using h1`. Establish `h2 : ∀ (a : R⟦X⟧) (p : Polynomial R) (n : ℕ), (X : R⟦X⟧) ^ n ∣ a - p → y ^ n ∣ L a - Polynomial.aeval y p`. Introduce `a p n h`. Establish `h3 : (Polynomial.X : Polynomial R) ^ n ∣ trunc n a - p`.

Rewrite using `[Polynomial.X_pow_dvd_iff]`. Introduce `d hd`. Use `X_pow_dvd_iff.1 h d hd` as an intermediate fact. Simplify `this` using `[coeff_trunc, hd]`. Establish `h4` using `map_dvd (Polynomial.aeval y) h3`.

Rewrite `h4` using `[map_pow, Polynomial.aeval_X, map_sub]`. Use `dvd_add (hL a n) h4 using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : ∀ p : Polynomial R, L p = Polynomial.aeval y p` using `fun p => by`. Rewrite using `[← sub_eq_zero]`.

Conclude with `hs _ fun n => h2 _ _ _ (by simp)`. Establish `hadd : ∀ a b, L (a + b) = L a + L b` using `fun a b => by`. Rewrite using `[← sub_eq_zero]`. Use `hs _ fun n => ?_` and prove the remaining obligations. Use `hL (a + b) n` as an intermediate fact.

Rewrite `this` using `[map_add, map_add]`. Use `dvd_sub (dvd_sub this (hL a n)) (hL b n) using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `hmul : ∀ a b, L (a * b) = L a * L b` using `fun a b => by`. Rewrite using `[← sub_eq_zero]`.

Use `hs _ fun n => ?_` and prove the remaining obligations. Use `h2 (a * b) (trunc n a * trunc n b) n (by` as an intermediate fact. Rewrite using `[Polynomial.coe_mul]`. Use `dvd_add ((X_pow_dvd_sub_trunc a n).mul_right b) ((X_pow_dvd_sub_trunc b n).mul_left (trunc n a : Polynomial R)) using 1` and compare the differences between its conclusion and the goal. Use the proof step `ring)`.

Rewrite `this` using `[map_mul]`. Use `dvd_sub (dvd_sub this ((hL a n).mul_right (L b))) ((hL b n).mul_left (Polynomial.aeval y (trunc n a))) using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Use `⟨{ toFun := L map_one' := by simpa using h3 1 map_mul' := hmul map_zero' := by simpa using h3 0 map_add' := hadd commutes' := fun r => by simpa using h3 (Polynomial.C r) }, ?_⟩` and prove the remaining obligations. Simplify using `using h3 Polynomial.X`.
-/
theorem algHom_exists (y : A) (hc : GlobalTheory.Per.AinfComplete.Summ y)
    (hs : ∀ x : A, (∀ n, y ^ n ∣ x) → x = 0) : ∃ f : R⟦X⟧ →ₐ[R] A, f X = y := by
  have h1 : ∀ a : R⟦X⟧, ∃ L : A, ∀ n, y ^ n ∣ L - Polynomial.aeval y (trunc n a) := by
    intro a
    obtain ⟨L, hL⟩ := hc fun i => algebraMap R A (coeff i a)
    refine ⟨L, fun n => ?_⟩
    have e : Polynomial.aeval y (trunc n a) =
        ∑ i ∈ Finset.range n, y ^ i * algebraMap R A (coeff i a) := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [trunc_succ, map_add, ih, Finset.sum_range_succ, Polynomial.aeval_monomial, mul_comm]
    rw [e]
    exact Ideal.mem_span_singleton.1 (hL n)
  choose L hL using h1
  have h2 : ∀ (a : R⟦X⟧) (p : Polynomial R) (n : ℕ), (X : R⟦X⟧) ^ n ∣ a - p →
      y ^ n ∣ L a - Polynomial.aeval y p := by
    intro a p n h
    have h3 : (Polynomial.X : Polynomial R) ^ n ∣ trunc n a - p := by
      rw [Polynomial.X_pow_dvd_iff]
      intro d hd
      have := X_pow_dvd_iff.1 h d hd
      simpa [coeff_trunc, hd] using this
    have h4 := map_dvd (Polynomial.aeval y) h3
    rw [map_pow, Polynomial.aeval_X, map_sub] at h4
    convert dvd_add (hL a n) h4 using 1
    ring
  have h3 : ∀ p : Polynomial R, L p = Polynomial.aeval y p := fun p => by
    rw [← sub_eq_zero]
    exact hs _ fun n => h2 _ _ _ (by simp)
  have hadd : ∀ a b, L (a + b) = L a + L b := fun a b => by
    rw [← sub_eq_zero]
    refine hs _ fun n => ?_
    have := hL (a + b) n
    rw [map_add, map_add] at this
    convert dvd_sub (dvd_sub this (hL a n)) (hL b n) using 1
    ring
  have hmul : ∀ a b, L (a * b) = L a * L b := fun a b => by
    rw [← sub_eq_zero]
    refine hs _ fun n => ?_
    have := h2 (a * b) (trunc n a * trunc n b) n (by
      rw [Polynomial.coe_mul]
      convert dvd_add ((X_pow_dvd_sub_trunc a n).mul_right b)
        ((X_pow_dvd_sub_trunc b n).mul_left (trunc n a : Polynomial R)) using 1
      ring)
    rw [map_mul] at this
    convert dvd_sub (dvd_sub this ((hL a n).mul_right (L b)))
      ((hL b n).mul_left (Polynomial.aeval y (trunc n a))) using 1
    ring
  refine ⟨{ toFun := L
            map_one' := by simpa using h3 1
            map_mul' := hmul
            map_zero' := by simpa using h3 0
            map_add' := hadd
            commutes' := fun r => by simpa using h3 (Polynomial.C r) }, ?_⟩
  simpa using h3 Polynomial.X

end General

variable (l : ℕ) [Fact l.Prime]

/- English proof (translation)
Establish `h0 : ∀ a : ℤ_[l]⟦X⟧, ¬ ((l : ℕ) : ℤ_[l]) ∣ constantCoeff a → ψ a ≠ 0`. Introduce `a ha`. Establish `: IsUnit (constantCoeff a)`. Assume the negation of the conclusion as `hn`. Conclude with `ha ((PadicInt.norm_lt_one_iff_dvd _).1 (PadicInt.not_isUnit_iff.1 hn))`.

Conclude with `((isUnit_iff_constantCoeff.2 this).map ψ).ne_zero`. Proceed by induction on `m with`. Consider the case `zero => intro a ha; exact h0 a (by simpa using ha)`. Consider the case `succ m ih`. Introduce `a ha`.

Distinguish the cases in `h : ((l : ℕ) : ℤ_[l]) ∣ constantCoeff a`. Take `⟨c, hc⟩` from `h`. Rewrite using `[eq_X_mul_shift_add_const a, hc, map_add, map_mul, map_mul, map_mul, map_natCast, map_natCast, CharP.cast_eq_zero, zero_mul, add_zero]`. Conclude with `mul_ne_zero hX (ih _ (by simpa using ha))`. Conclude with `h0 a h`.
-/
theorem ne_zero_of_coeff {B : Type*} [CommRing B] [IsDomain B] [CharP B l] (ψ : ℤ_[l]⟦X⟧ →+* B)
    (hX : ψ X ≠ 0) (m : ℕ) : ∀ a : ℤ_[l]⟦X⟧, ¬ ((l : ℕ) : ℤ_[l]) ∣ coeff m a → ψ a ≠ 0 := by
  have h0 : ∀ a : ℤ_[l]⟦X⟧, ¬ ((l : ℕ) : ℤ_[l]) ∣ constantCoeff a → ψ a ≠ 0 := by
    intro a ha
    have : IsUnit (constantCoeff a) := by
      by_contra hn
      exact ha ((PadicInt.norm_lt_one_iff_dvd _).1 (PadicInt.not_isUnit_iff.1 hn))
    exact ((isUnit_iff_constantCoeff.2 this).map ψ).ne_zero
  induction m with
  | zero => intro a ha; exact h0 a (by simpa using ha)
  | succ m ih =>
    intro a ha
    by_cases h : ((l : ℕ) : ℤ_[l]) ∣ constantCoeff a
    · obtain ⟨c, hc⟩ := h
      rw [eq_X_mul_shift_add_const a, hc, map_add, map_mul, map_mul, map_mul, map_natCast,
        map_natCast, CharP.cast_eq_zero, zero_mul, add_zero]
      exact mul_ne_zero hX (ih _ (by simpa using ha))
    · exact h0 a h

/- English proof (translation)
Assume the negation of the conclusion as `h`. Apply `ha` to reduce the goal to its premises. Establish `: ∀ m, ((l : ℕ) : ℤ_[l]) ∣ coeff m a` using `fun m => by`. Assume the negation of the conclusion as `hm`. Conclude with `ne_zero_of_coeff l ψ hX m a hm h`.

Use `choose c hc using this`. Use `⟨PowerSeries.mk c, ?_⟩` and prove the remaining obligations. Use extensionality with `m`. Rewrite using `[← map_natCast (C : ℤ_[l] →+* ℤ_[l]⟦X⟧), coeff_C_mul, coeff_mk, hc]`.
-/
theorem ne_zero_of_not_dvd {B : Type*} [CommRing B] [IsDomain B] [CharP B l] (ψ : ℤ_[l]⟦X⟧ →+* B)
    (hX : ψ X ≠ 0) (a : ℤ_[l]⟦X⟧) (ha : ¬ ((l : ℕ) : ℤ_[l]⟦X⟧) ∣ a) : ψ a ≠ 0 := by
  by_contra h
  apply ha
  have : ∀ m, ((l : ℕ) : ℤ_[l]) ∣ coeff m a := fun m => by
    by_contra hm
    exact ne_zero_of_coeff l ψ hX m a hm h
  choose c hc using this
  refine ⟨PowerSeries.mk c, ?_⟩
  ext m
  rw [← map_natCast (C : ℤ_[l] →+* ℤ_[l]⟦X⟧), coeff_C_mul, coeff_mk, hc]

/- English proof (translation)
Rewrite using `[phi, act, substAlgHom_X, cyc, binomialSeries_nat]`. Simplify using the standard rewrite rules.
-/
theorem phi_X : phi l ℤ_[l] X = (1 + X) ^ l - 1 := by
  rw [phi, act, substAlgHom_X, cyc, binomialSeries_nat]
  simp

/- English proof (translation)
Rewrite using `[map_sub, map_one, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]`.
-/
theorem constantCoeff_teich_sub (e : OCb l) :
    WittVector.constantCoeff (WittVector.teichmuller l e - 1 : Ainf l) = e - 1 := by
  rw [map_sub, map_one, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]

/- English proof (translation)
Establish `hy : ¬ IsUnit (WittVector.teichmuller l e - 1 : Ainf l)` using `fun h => he (constantCoeff_teich_sub l e ▸ h.map WittVector.constantCoeff)`. Use `(GlobalTheory.Per.AinfComplete.main l _ hy).2` as an intermediate fact. Conclude with `⟨GlobalTheory.Per.AinfComplete.summ_of_precomplete _, fun x hx => GlobalTheory.Per.AinfComplete.eq_zero_of_haus _ x fun n => Ideal.mem_span_singleton.2 (hx n)⟩`.
-/
theorem complete_teich (e : OCb l) (he : ¬ IsUnit (e - 1)) :
    GlobalTheory.Per.AinfComplete.Summ (WittVector.teichmuller l e - 1 : Ainf l) ∧
      ∀ x : Ainf l, (∀ n, (WittVector.teichmuller l e - 1 : Ainf l) ^ n ∣ x) → x = 0 := by
  have hy : ¬ IsUnit (WittVector.teichmuller l e - 1 : Ainf l) := fun h =>
    he (constantCoeff_teich_sub l e ▸ h.map WittVector.constantCoeff)
  have := (GlobalTheory.Per.AinfComplete.main l _ hy).2
  exact ⟨GlobalTheory.Per.AinfComplete.summ_of_precomplete _, fun x hx =>
    GlobalTheory.Per.AinfComplete.eq_zero_of_haus _ x fun n => Ideal.mem_span_singleton.2 (hx n)⟩

noncomputable def frobA : Ainf l →ₐ[ℤ_[l]] Ainf l where
  toRingHom := WittVector.map (frobenius (OCb l) l)
  commutes' := fun x => map_zlW l _ x

/- English proof (translation)
Rewrite using `[WittVector.frobenius_eq_map_frobenius]`. Both sides reduce to the same expression.
-/
theorem frobA_apply (x : Ainf l) : frobA l x = WittVector.frobenius x := by
  rw [WittVector.frobenius_eq_map_frobenius]
  rfl

/- English proof (translation)
Introduce `l hl e he`. Take `⟨hc, hs⟩` from `complete_teich l e he`. Use `⟨?_, fun io hio => ⟨?_, fun he1 a ha => ?_⟩⟩` and prove the remaining obligations. Take `⟨f, hf⟩` from `algHom_exists (R := ℤ_[l]) _ hc hs`. Use `⟨f, hf, fun g hg => algHom_unique g f (Eq.trans hg hf.symm) ?_⟩` and prove the remaining obligations.

Rewrite using `[show g X = _ from hg]`. Conclude with `hs`. Establish `he' : ¬ IsUnit (e ^ l - 1)` using `fun h => he (by`. Rewrite `h` using `[← geom_sum_mul]`. Conclude with `isUnit_of_mul_isUnit_right h)`.

Establish `hio' : io X = WittVector.teichmuller l e - 1` using `hio`. Establish `e1 : (io.comp (phi l ℤ_[l])) X = WittVector.teichmuller l (e ^ l) - 1`. Rewrite using `[AlgHom.comp_apply, phi_X, map_sub, map_pow, map_add, map_one, hio', map_pow]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : ((frobA l).comp io) X = WittVector.teichmuller l (e ^ l) - 1`.

Rewrite using `[AlgHom.comp_apply, hio', map_sub, map_one]`. Use `congr 1`. Conclude with `WittVector.map_teichmuller l (frobenius (OCb l) l) e`. Use `algHom_unique _ _ (e1.trans e2.symm) (by rw [e1]; exact (complete_teich l _ he').2)` as an intermediate fact. Introduce `a`.

Rewrite using `[← frobA_apply]`. Conclude with `DFunLike.congr_fun this a`. Apply `WittVector.isUnit_of_coeff_zero_ne_zero` to reduce the goal to its premises. Rewrite using `[inclW, WittVector.map_coeff]`. Establish `hio' : io X = WittVector.teichmuller l e - 1` using `hio`.

Use `ne_zero_of_not_dvd l ((WittVector.constantCoeff : Ainf l →+* OCb l).comp io.toRingHom) (by` as an intermediate fact. Express the relevant statement in the definitionally equal form `WittVector.constantCoeff (io X) ≠ 0`. Rewrite using `[hio', constantCoeff_teich_sub]`. Conclude with `sub_ne_zero.2 he1) a ha`. Introduce `hz`.

Conclude with `this ((IsFractionRing.injective (OCb l) (Cb l)) (hz.trans (map_zero _).symm))`.
-/
theorem main : ∀ (l : ℕ) [Fact l.Prime], ∀ e : OCb l, ¬ IsUnit (e - 1) →
    (∃! io : PowerSeries ℤ_[l] →ₐ[ℤ_[l]] Ainf l, IsIo e io) ∧
    ∀ io : PowerSeries ℤ_[l] →ₐ[ℤ_[l]] Ainf l, IsIo e io →
      (∀ a, io (phi l ℤ_[l] a) = WittVector.frobenius (io a)) ∧
      (e ≠ 1 → ∀ a, ¬ ((l : ℕ) : PowerSeries ℤ_[l]) ∣ a → IsUnit (inclW l (io a))) := by
  intro l hl e he
  obtain ⟨hc, hs⟩ := complete_teich l e he
  refine ⟨?_, fun io hio => ⟨?_, fun he1 a ha => ?_⟩⟩
  · obtain ⟨f, hf⟩ := algHom_exists (R := ℤ_[l]) _ hc hs
    refine ⟨f, hf, fun g hg => algHom_unique g f (Eq.trans hg hf.symm) ?_⟩
    rw [show g X = _ from hg]
    exact hs
  · have he' : ¬ IsUnit (e ^ l - 1) := fun h => he (by
      rw [← geom_sum_mul] at h
      exact isUnit_of_mul_isUnit_right h)
    have hio' : io X = WittVector.teichmuller l e - 1 := hio
    have e1 : (io.comp (phi l ℤ_[l])) X = WittVector.teichmuller l (e ^ l) - 1 := by
      rw [AlgHom.comp_apply, phi_X, map_sub, map_pow, map_add, map_one, hio', map_pow]
      ring
    have e2 : ((frobA l).comp io) X = WittVector.teichmuller l (e ^ l) - 1 := by
      rw [AlgHom.comp_apply, hio', map_sub, map_one]
      congr 1
      exact WittVector.map_teichmuller l (frobenius (OCb l) l) e
    have := algHom_unique _ _ (e1.trans e2.symm) (by rw [e1]; exact (complete_teich l _ he').2)
    intro a
    rw [← frobA_apply]
    exact DFunLike.congr_fun this a
  · apply WittVector.isUnit_of_coeff_zero_ne_zero
    rw [inclW, WittVector.map_coeff]
    have hio' : io X = WittVector.teichmuller l e - 1 := hio
    have := ne_zero_of_not_dvd l
      ((WittVector.constantCoeff : Ainf l →+* OCb l).comp io.toRingHom) (by
        change WittVector.constantCoeff (io X) ≠ 0
        rw [hio', constantCoeff_teich_sub]
        exact sub_ne_zero.2 he1) a ha
    intro hz
    exact this ((IsFractionRing.injective (OCb l) (Cb l)) (hz.trans (map_zero _).symm))

end GlobalTheory.Cyc.IoMap
