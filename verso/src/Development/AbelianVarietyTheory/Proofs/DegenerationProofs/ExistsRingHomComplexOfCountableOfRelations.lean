import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsRingHomComplexCompEqOfCountable
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ]`. Proceed by induction on `c using MvPolynomial.induction_on with`. Consider the case `C a`. Rewrite using `[MvPolynomial.eval₂Hom_C]`. Simplify using `using isAlgebraic_algebraMap (R := ℚ) (A := ℂ) (a : ℚ)`.

Consider the case `add p q hp hq => rw [map_add]`. Conclude with `hp.add hq`. Consider the case `mul_X p i hp => rw [map_mul, MvPolynomial.eval₂Hom_X']`. Conclude with `hp.mul (hy i)`.
-/
theorem isAlgebraic_int_eval₂Hom_of_isAlgebraic {σ : Type} (y : σ → ℂ)
    (hy : ∀ i, IsAlgebraic ℚ (y i)) (c : MvPolynomial σ ℤ) :
    IsAlgebraic ℤ (MvPolynomial.eval₂Hom (Int.castRingHom ℂ) y c) := by
  rw [IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ]
  induction c using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.eval₂Hom_C]
    simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℂ) (a : ℚ)
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | mul_X p i hp => rw [map_mul, MvPolynomial.eval₂Hom_X']; exact hp.mul (hy i)

/- English proof (translation)
Introduce `F _ _ _ x y hy hrel`. Use `set ey := MvPolynomial.eval₂Hom (Int.castRingHom ℂ) y with hey`. Use `set ex := MvPolynomial.eval₂Hom (Int.castRingHom F) x with hex`. Set `R` to `MvPolynomial (Fin 2) ℤ ⧸ RingHom.ker ey`. Establish `hprime : (RingHom.ker ey).IsPrime` using `RingHom.ker_isPrime ey`.

Establish `: IsDomain R` using `Ideal.Quotient.isDomain _`. Set `em : R →+* ℂ` to `RingHom.kerLift ey`. Establish `hem : Function.Injective em` using `RingHom.kerLift_injective ey`. Set `β : R →+* F` to `Ideal.Quotient.lift _ ex fun c hc => hrel c hc`. Establish `halg : ∀ r : R, IsAlgebraic ℤ r`.

Introduce `r`. Take `⟨c, rfl⟩` from `Ideal.Quotient.mk_surjective r`. Use `(isAlgebraic_algHom_iff em.toIntAlgHom hem).1 ?_` and prove the remaining obligations. Conclude with `isAlgebraic_int_eval₂Hom_of_isAlgebraic y hy c`. Establish `hβ : Function.Injective β`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `r hr`. Assume the negation of the conclusion as `h0`. Use `Ideal.comap_ne_bot_of_algebraic_mem (R := ℤ) (I := RingHom.ker β) h0 hr (halg r) ?_` and prove the remaining obligations. Rewrite using `[eq_bot_iff]`.

Introduce `n hn`. Rewrite `hn` using `[Ideal.mem_comap, RingHom.mem_ker]`. Simplify using `using hn`. Establish `hc : Countable R` using `hβ.countable`. Set `: Algebra R F` to `β.toAlgebra`.

Set `: Algebra R ℂ` to `em.toAlgebra`. Establish `: FaithfulSMul R F` using `(faithfulSMul_iff_algebraMap_injective R F).2 hβ`. Establish `: FaithfulSMul R ℂ` using `(faithfulSMul_iff_algebraMap_injective R ℂ).2 hem`. Take `⟨j⟩` from `nonempty_algHom_complex_of_countable R F`. Use `⟨j.toRingHom, fun i => ?_⟩` and prove the remaining obligations.

Establish `h` using `j.commutes (Ideal.Quotient.mk _ (MvPolynomial.X i))`. Establish `h1 : algebraMap R F (Ideal.Quotient.mk _ (MvPolynomial.X i)) = x i` using `MvPolynomial.eval₂Hom_X' (Int.castRingHom F) x i`. Establish `h2 : algebraMap R ℂ (Ideal.Quotient.mk _ (MvPolynomial.X i)) = y i` using `MvPolynomial.eval₂Hom_X' (Int.castRingHom ℂ) y i`. Rewrite `h` using `[h1, h2]`. Conclude with `h`.
-/
theorem exists_ringHom_complex_of_countable_of_relations :
    ∀ (F : Type) [Field F] [CharZero F] [Countable F] (x : Fin 2 → F) (y : Fin 2 → ℂ), (∀ i, IsAlgebraic ℚ (y i)) → (∀ c : MvPolynomial (Fin 2) ℤ, MvPolynomial.eval₂Hom (Int.castRingHom ℂ) y c = 0 → MvPolynomial.eval₂Hom (Int.castRingHom F) x c = 0) → ∃ f : F →+* ℂ, ∀ i, f (x i) = y i := by
  intro F _ _ _ x y hy hrel
  set ey := MvPolynomial.eval₂Hom (Int.castRingHom ℂ) y with hey
  set ex := MvPolynomial.eval₂Hom (Int.castRingHom F) x with hex
  let R := MvPolynomial (Fin 2) ℤ ⧸ RingHom.ker ey
  have hprime : (RingHom.ker ey).IsPrime := RingHom.ker_isPrime ey
  have : IsDomain R := Ideal.Quotient.isDomain _
  let em : R →+* ℂ := RingHom.kerLift ey
  have hem : Function.Injective em := RingHom.kerLift_injective ey
  let β : R →+* F := Ideal.Quotient.lift _ ex fun c hc => hrel c hc
  have halg : ∀ r : R, IsAlgebraic ℤ r := by
    intro r
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective r
    refine (isAlgebraic_algHom_iff em.toIntAlgHom hem).1 ?_
    exact isAlgebraic_int_eval₂Hom_of_isAlgebraic y hy c
  have hβ : Function.Injective β := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra h0
    refine Ideal.comap_ne_bot_of_algebraic_mem (R := ℤ) (I := RingHom.ker β) h0 hr (halg r) ?_
    rw [eq_bot_iff]
    intro n hn
    rw [Ideal.mem_comap, RingHom.mem_ker] at hn
    simpa using hn
  have hc : Countable R := hβ.countable
  let : Algebra R F := β.toAlgebra
  let : Algebra R ℂ := em.toAlgebra
  have : FaithfulSMul R F := (faithfulSMul_iff_algebraMap_injective R F).2 hβ
  have : FaithfulSMul R ℂ := (faithfulSMul_iff_algebraMap_injective R ℂ).2 hem
  obtain ⟨j⟩ := nonempty_algHom_complex_of_countable R F
  refine ⟨j.toRingHom, fun i => ?_⟩
  have h := j.commutes (Ideal.Quotient.mk _ (MvPolynomial.X i))
  have h1 : algebraMap R F (Ideal.Quotient.mk _ (MvPolynomial.X i)) = x i :=
    MvPolynomial.eval₂Hom_X' (Int.castRingHom F) x i
  have h2 : algebraMap R ℂ (Ideal.Quotient.mk _ (MvPolynomial.X i)) = y i :=
    MvPolynomial.eval₂Hom_X' (Int.castRingHom ℂ) y i
  rw [h1, h2] at h
  exact h

end GlobalTheory
