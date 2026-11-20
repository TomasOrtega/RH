import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SplitPlaceTypes
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.SplitRowIffOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Formalism.LocalRingCardinality.HostCls
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjSqrt

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

namespace GlobalTheory.SplitPlaces

variable {R : Ranks} (H : Host R)

/- English proof (translation)
Conclude with `H.sqd_sq`.
-/
theorem sqrt_sq : (H.sqd) ^ 2 = -(H.d : H.E) := by
  exact H.sqd_sq

/- English proof (translation)
Apply the tactic sequence `apply _root_.UpperTheory.Reformulated.B.Rc9.conj_sqrt <;> assumption`.
-/
theorem conj_sqrt : H.conj (H.sqd) = -H.sqd :=
  by apply _root_.UpperTheory.Reformulated.B.Rc9.conj_sqrt <;> assumption

/- English proof (translation)
Set `c : 𝓞 H.E ≃+* 𝓞 H.E` to `RingOfIntegers.mapRingEquiv H.conj.toRingEquiv`. Use `⟨HeightOneSpectrum.comap (c.symm : 𝓞 H.E →+* 𝓞 H.E) c.symm.surjective w, ?_, ?_⟩` and prove the remaining obligations. Use `show (c.symm : 𝓞 H.E →+* 𝓞 H.E) (l : 𝓞 H.E) ∈ w.asIdeal`. Rewrite using `[map_natCast]`. Conclude with `hw`.

Introduce `x y hxy`. Establish `: y = c x`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[hxy]`. Both sides reduce to the same expression.

Substitute `this` using the available equality. Use `show _ ↔ c.symm (c x) ∈ w.asIdeal`. Rewrite using `[c.symm_apply_apply]`.
-/
theorem exists_conjPl (l : ℕ) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E l) :
    ∃ w' ∈ placesOver H.E l, IsConjPl H w w' := by
  let c : 𝓞 H.E ≃+* 𝓞 H.E := RingOfIntegers.mapRingEquiv H.conj.toRingEquiv
  refine ⟨HeightOneSpectrum.comap (c.symm : 𝓞 H.E →+* 𝓞 H.E) c.symm.surjective w, ?_, ?_⟩
  · show (c.symm : 𝓞 H.E →+* 𝓞 H.E) (l : 𝓞 H.E) ∈ w.asIdeal
    rw [map_natCast]
    exact hw
  · intro x y hxy
    have : y = c x := by
      apply RingOfIntegers.ext
      rw [hxy]; rfl
    subst this
    show _ ↔ c.symm (c x) ∈ w.asIdeal
    rw [c.symm_apply_apply]

/- English proof (translation)
Introduce `h`. Establish `: Fact l.Prime` using `⟨hl⟩`. Take `⟨m, hm⟩` from `ZMod.isSquare_of_jacobiSym_eq_one hj`. Take `⟨n, rfl⟩` from `ZMod.intCast_surjective m`. Establish `hdvd : (l : ℤ) ∣ n * n + H.d`.

Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Move the coercions through the operations in `at hm ⊢`. Rewrite using `[← hm]`. Expand and normalize the polynomial expressions, which then agree. Establish `hint : IsIntegral ℤ (H.sqd)`.

Apply `IsIntegral.of_pow (n := 2) (by norm_num)` to reduce the goal to its premises. Rewrite using `[sqrt_sq]`. Conclude with `(isIntegral_natCast _).neg`. Set `b : 𝓞 H.E` to `⟨H.sqd, hint⟩`. Establish `hb : b ^ 2 = -(H.d : 𝓞 H.E)`.

Apply `RingOfIntegers.ext` to reduce the goal to its premises. Establish `e : ((b : 𝓞 H.E) : H.E) = H.sqd` using `rfl`. Simplify using `only [map_neg, map_pow, map_natCast, e]`. Conclude with `sqrt_sq H`. Establish `hiff : b - n ∈ w.asIdeal ↔ b + n ∈ w.asIdeal`.

Rewrite using `[h (b - n) (-(b + n)) ?_, neg_mem_iff]`. Establish `e : ((b : 𝓞 H.E) : H.E) = H.sqd` using `rfl`. Simplify using `only [map_neg, map_add, map_sub, map_intCast, e, conj_sqrt]`. Expand and normalize the polynomial expressions, which then agree. Establish `hprod : (b - n) * (b + n) ∈ w.asIdeal`.

Take `⟨k, hk⟩` from `hdvd`. Establish `hk' : ((n * n + H.d : ℤ) : 𝓞 H.E) = ((l * k : ℤ) : 𝓞 H.E)` using `by rw [hk]`. Move the coercions through the operations in `at hk'`. Establish `: (b - n) * (b + n) = (l : 𝓞 H.E) * (-k)`. Take the linear combination `hb - hk'`.

Rewrite using `[this]`. Conclude with `w.asIdeal.mul_mem_right _ hw`. Establish `hboth : b - n ∈ w.asIdeal ∧ b + n ∈ w.asIdeal`. Break down `w.isPrime.mem_or_mem hprod with h1 | h1` into its components or cases. Use `exacts [⟨h1, hiff.mp h1⟩, ⟨hiff.mpr h1, h1⟩]`.

Establish `h2n : ((2 * n : ℤ) : 𝓞 H.E) ∈ w.asIdeal`. Use `w.asIdeal.sub_mem hboth.2 hboth.1` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hlo` using `GlobalTheory.HubLoc.liesOver_of_mem hl hw`. Establish `hl2n : (l : ℤ) ∣ 2 * n`. Rewrite using `[← Ideal.mem_span_singleton, hlo.over, Ideal.under_def, Ideal.mem_comap]`. Simplify using `using h2n`. Establish `hp : Prime (l : ℤ)` using `Nat.prime_iff_prime_int.mp hl`.

Break down `hp.dvd_or_dvd hl2n with h1 | h1` into its components or cases. Establish `h3 : l ∣ 2` using `by exact_mod_cast h1`. Conclude with `hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp h3)`. Establish `h3 : (l : ℤ) ∣ H.d` using `(dvd_add_right (h1.mul_right n)).mp hdvd`. Establish `h4 : l ∣ H.d` using `by exact_mod_cast h3`.

Conclude with `hld ((Nat.prime_dvd_prime_iff_eq hl H.hyp.2.1).mp h4)`.
-/
theorem not_isConjPl_self {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) (hld : l ≠ H.d)
    (hj : jacobiSym (-(H.d : ℤ)) l = 1) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E l) :
    ¬ IsConjPl H w w := by
  intro h
  have : Fact l.Prime := ⟨hl⟩
  obtain ⟨m, hm⟩ := ZMod.isSquare_of_jacobiSym_eq_one hj
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective m
  have hdvd : (l : ℤ) ∣ n * n + H.d := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at hm ⊢
    rw [← hm]; ring
  have hint : IsIntegral ℤ (H.sqd) := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [sqrt_sq]
    exact (isIntegral_natCast _).neg
  let b : 𝓞 H.E := ⟨H.sqd, hint⟩
  have hb : b ^ 2 = -(H.d : 𝓞 H.E) := by
    apply RingOfIntegers.ext
    have e : ((b : 𝓞 H.E) : H.E) = H.sqd := rfl
    simp only [map_neg, map_pow, map_natCast, e]
    exact sqrt_sq H
  have hiff : b - n ∈ w.asIdeal ↔ b + n ∈ w.asIdeal := by
    rw [h (b - n) (-(b + n)) ?_, neg_mem_iff]
    have e : ((b : 𝓞 H.E) : H.E) = H.sqd := rfl
    simp only [map_neg, map_add, map_sub, map_intCast, e, conj_sqrt]
    ring
  have hprod : (b - n) * (b + n) ∈ w.asIdeal := by
    obtain ⟨k, hk⟩ := hdvd
    have hk' : ((n * n + H.d : ℤ) : 𝓞 H.E) = ((l * k : ℤ) : 𝓞 H.E) := by rw [hk]
    push_cast at hk'
    have : (b - n) * (b + n) = (l : 𝓞 H.E) * (-k) := by
      linear_combination hb - hk'
    rw [this]
    exact w.asIdeal.mul_mem_right _ hw
  have hboth : b - n ∈ w.asIdeal ∧ b + n ∈ w.asIdeal := by
    rcases w.isPrime.mem_or_mem hprod with h1 | h1
    exacts [⟨h1, hiff.mp h1⟩, ⟨hiff.mpr h1, h1⟩]
  have h2n : ((2 * n : ℤ) : 𝓞 H.E) ∈ w.asIdeal := by
    have := w.asIdeal.sub_mem hboth.2 hboth.1
    convert this using 1
    push_cast; ring
  have hlo := GlobalTheory.HubLoc.liesOver_of_mem hl hw
  have hl2n : (l : ℤ) ∣ 2 * n := by
    rw [← Ideal.mem_span_singleton, hlo.over, Ideal.under_def, Ideal.mem_comap]
    simpa using h2n
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  rcases hp.dvd_or_dvd hl2n with h1 | h1
  · have h3 : l ∣ 2 := by exact_mod_cast h1
    exact hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp h3)
  · have h3 : (l : ℤ) ∣ H.d := (dvd_add_right (h1.mul_right n)).mp hdvd
    have h4 : l ∣ H.d := by exact_mod_cast h3
    exact hld ((Nat.prime_dvd_prime_iff_eq hl H.hyp.2.1).mp h4)

/- English proof (translation)
Introduce `R H l ⟨hl, h5, _, hd, _, hc⟩ w hw`. Establish `hl2 : l ≠ 2` using `by omega`. Take `⟨hN, hj⟩` from `(primeClass_eq_splitK_iff' (H := H.toHostRaw) hl).1 hc`. Use `⟨GlobalTheory.HubLoc.ramIdx_eq_one H hl hN w hw, exists_conjPl H l w hw, ?_⟩` and prove the remaining obligations. Introduce and unpack `w' h rfl`.

Conclude with `not_isConjPl_self H hl hl2 hd hj _ hw h`.
-/
theorem placesSplit : ∀ {R : Ranks} (H : Host R) (l : ℕ), SplitRowPrime H l → PlacesSplit H l := by
  intro R H l ⟨hl, h5, _, hd, _, hc⟩ w hw
  have hl2 : l ≠ 2 := by omega
  obtain ⟨hN, hj⟩ := (primeClass_eq_splitK_iff' (H := H.toHostRaw) hl).1 hc
  refine ⟨GlobalTheory.HubLoc.ramIdx_eq_one H hl hN w hw, exists_conjPl H l w hw, ?_⟩
  rintro w' h rfl
  exact not_isConjPl_self H hl hl2 hd hj _ hw h

end GlobalTheory.SplitPlaces
