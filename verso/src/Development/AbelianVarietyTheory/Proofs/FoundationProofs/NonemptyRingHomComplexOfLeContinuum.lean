import Mathlib
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataRRMetric
import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair

set_option autoImplicit false

open Formalism.BasicNotions NumberField

namespace GlobalTheory.WittFracComplex

open Cardinal in

/- English proof (translation)
Set `F` to `FractionRing (MvPolynomial ℝ K)`. Set `L` to `AlgebraicClosure F`. Establish `hF : #F = 𝔠`. Rewrite using `[Cardinal.mk_fractionRing, MvPolynomial.cardinalMk_eq_max, Cardinal.mk_real, max_eq_right hK, max_eq_left Cardinal.aleph0_le_continuum]`. Establish `hL : #L = 𝔠`.

Use `le_antisymm ?_ (hF ▸ Cardinal.mk_le_of_injective (algebraMap F L).injective)` and prove the remaining obligations. Use `Algebra.IsAlgebraic.cardinalMk_le_max F L` as an intermediate fact. Rewrite `this` using `[hF, max_eq_left Cardinal.aleph0_le_continuum]`. Then use the resulting hypothesis. Set `j : K →+* L` to `(algebraMap F L).comp ((algebraMap (MvPolynomial ℝ K) F).comp MvPolynomial.C)`. Establish `: CharZero L` using `(RingHom.charZero_iff j.injective).1 inferInstance`.

Take `⟨e⟩` from `IsAlgClosed.ringEquiv_of_equiv_of_charZero (K := L) (L := ℂ) (hL ▸ Cardinal.aleph0_lt_continuum) (Cardinal.eq.1 (hL.trans Cardinal.mk_complex.symm))`. Conclude with `⟨e.toRingHom.comp j⟩`.
-/
theorem nonempty_ringHom_complex_of_le_continuum (K : Type) [Field K] [CharZero K] (hK : #K ≤ 𝔠) :
    Nonempty (K →+* ℂ) := by
  let F := FractionRing (MvPolynomial ℝ K)
  let L := AlgebraicClosure F
  have hF : #F = 𝔠 := by
    rw [Cardinal.mk_fractionRing, MvPolynomial.cardinalMk_eq_max, Cardinal.mk_real, max_eq_right hK,
      max_eq_left Cardinal.aleph0_le_continuum]
  have hL : #L = 𝔠 := by
    refine le_antisymm ?_ (hF ▸ Cardinal.mk_le_of_injective (algebraMap F L).injective)
    have := Algebra.IsAlgebraic.cardinalMk_le_max F L
    rwa [hF, max_eq_left Cardinal.aleph0_le_continuum] at this
  let j : K →+* L := (algebraMap F L).comp ((algebraMap (MvPolynomial ℝ K) F).comp MvPolynomial.C)
  have : CharZero L := (RingHom.charZero_iff j.injective).1 inferInstance
  obtain ⟨e⟩ := IsAlgClosed.ringEquiv_of_equiv_of_charZero (K := L) (L := ℂ)
    (hL ▸ Cardinal.aleph0_lt_continuum) (Cardinal.eq.1 (hL.trans Cardinal.mk_complex.symm))
  exact ⟨e.toRingHom.comp j⟩

/- English proof (translation)
Take `⟨q, hq⟩` from `CharP.exists (WittVector p k)`. Establish `h1 : ((q : ℕ) : k) = 0`. Use `congrArg (WittVector.constantCoeff : WittVector p k →+* k) (CharP.cast_eq_zero (WittVector p k) q)` as an intermediate fact. Rewrite `this` using `[map_natCast, map_zero]`. Then use the resulting hypothesis. Establish `h2 : p ∣ q` using `(CharP.cast_eq_zero_iff k p q).1 h1`.

Break down `CharP.char_is_prime_or_zero (WittVector p k) q with h | h` into its components or cases. Establish `h3 : p = q` using `(Nat.prime_dvd_prime_iff_eq hp.out h).1 h2`. Substitute `h3` using the available equality. Conclude with `absurd (CharP.cast_eq_zero (WittVector p k) p) (WittVector.p_nonzero p k)`. Substitute `h` using the available equality.

Conclude with `CharP.charP_to_charZero _`.
-/
theorem charZero_wittVector (p : ℕ) [hp : Fact p.Prime] (k : Type) [Field k] [CharP k p] :
    CharZero (WittVector p k) := by
  obtain ⟨q, hq⟩ := CharP.exists (WittVector p k)
  have h1 : ((q : ℕ) : k) = 0 := by
    have := congrArg (WittVector.constantCoeff : WittVector p k →+* k) (CharP.cast_eq_zero (WittVector p k) q)
    rwa [map_natCast, map_zero] at this
  have h2 : p ∣ q := (CharP.cast_eq_zero_iff k p q).1 h1
  rcases CharP.char_is_prime_or_zero (WittVector p k) q with h | h
  · have h3 : p = q := (Nat.prime_dvd_prime_iff_eq hp.out h).1 h2
    subst h3
    exact absurd (CharP.cast_eq_zero (WittVector p k) p) (WittVector.p_nonzero p k)
  · subst h
    exact CharP.charP_to_charZero _

open Cardinal in

/- English proof (translation)
Establish `h : Function.Injective (WittVector.coeff : WittVector p k → ℕ → k)` using `fun x y h => WittVector.ext (fun n => congrFun h n)`. Use `(Cardinal.mk_le_of_injective h).trans ?_` and prove the remaining obligations. Rewrite using `[← Cardinal.power_def, Cardinal.mk_nat, ← Cardinal.aleph0_power_aleph0]`. Conclude with `Cardinal.power_le_power_right hk`.
-/
theorem mk_wittVector_le (p : ℕ) (k : Type) (hk : #k ≤ ℵ₀) : #(WittVector p k) ≤ 𝔠 := by
  have h : Function.Injective (WittVector.coeff : WittVector p k → ℕ → k) :=
    fun x y h => WittVector.ext (fun n => congrFun h n)
  refine (Cardinal.mk_le_of_injective h).trans ?_
  rw [← Cardinal.power_def, Cardinal.mk_nat, ← Cardinal.aleph0_power_aleph0]
  exact Cardinal.power_le_power_right hk

open Cardinal in

/- English proof (translation)
Introduce `p _`. Establish `hk : #(AlgebraicClosure (ZMod p)) ≤ ℵ₀`. Use `Algebra.IsAlgebraic.cardinalMk_le_max (ZMod p) (AlgebraicClosure (ZMod p))` as an intermediate fact. Rewrite `this` using `[max_eq_right (Cardinal.lt_aleph0_of_finite _).le]`. Then use the resulting hypothesis. Use `charZero_wittVector p (AlgebraicClosure (ZMod p))` as an intermediate fact.

Establish `: CharZero (DV.KW p)` using `(RingHom.charZero_iff (IsFractionRing.injective (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p))).1 this`. Use `nonempty_ringHom_complex_of_le_continuum _ ?_` and prove the remaining obligations. Rewrite using `[Cardinal.mk_fractionRing]`. Conclude with `mk_wittVector_le p _ hk`.
-/
theorem nonempty_ringHom_complex : ∀ (p : ℕ) [Fact p.Prime], Nonempty (DV.KW p →+* ℂ) := by
  intro p _
  have hk : #(AlgebraicClosure (ZMod p)) ≤ ℵ₀ := by
    have := Algebra.IsAlgebraic.cardinalMk_le_max (ZMod p) (AlgebraicClosure (ZMod p))
    rwa [max_eq_right (Cardinal.lt_aleph0_of_finite _).le] at this
  have := charZero_wittVector p (AlgebraicClosure (ZMod p))
  have : CharZero (DV.KW p) :=
    (RingHom.charZero_iff (IsFractionRing.injective (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p))).1 this
  refine nonempty_ringHom_complex_of_le_continuum _ ?_
  rw [Cardinal.mk_fractionRing]
  exact mk_wittVector_le p _ hk

end GlobalTheory.WittFracComplex
