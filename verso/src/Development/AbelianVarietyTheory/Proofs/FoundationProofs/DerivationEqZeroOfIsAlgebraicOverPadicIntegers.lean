import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
open GlobalTheory.K5

noncomputable section

namespace GlobalTheory.K5.DerAlg

open Polynomial

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

abbrev phiZ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] : ℤ_[p] →+* Ω :=
  (algebraMap (O0 p) Ω).comp (algebraMap ℤ_[p] (O0 p))

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `c hc`. Assume the negation of the conclusion as `h0`. Rewrite `hc` using `[PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast]`. Establish `hu : IsUnit (phiZ p Ω (PadicInt.unitCoeff h0 : ℤ_[p]))` using `(Units.isUnit _).map _`.

Establish `hp : ((p : Ω)) ^ c.valuation ≠ 0` using `pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)`. Conclude with `mul_ne_zero hu.ne_zero hp hc`.
-/
theorem phiZ_injective [CharZero Ω] : Function.Injective (phiZ p Ω) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  by_contra h0
  rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hc
  have hu : IsUnit (phiZ p Ω (PadicInt.unitCoeff h0 : ℤ_[p])) :=
    (Units.isUnit _).map _
  have hp : ((p : Ω)) ^ c.valuation ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  exact mul_ne_zero hu.ne_zero hp hc

/- English proof (translation)
Proceed by induction on `Q using Polynomial.induction_on' with`. Consider the case `add P Q hP hQ => rw [eval₂_add, map_add, hP, hQ, derivative_add, eval₂_add, add_mul]`. Consider the case `monomial n c`. Establish `hc : E (phiZ p Ω c) = 0` using `hE c`. Rewrite using `[eval₂_monomial, Derivation.leibniz, Derivation.leibniz_pow, hc, smul_zero, add_zero, derivative_monomial, eval₂_monomial]`.

Simplify using `only [smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem der_eval₂ (E : Derivation ℤ Ω Ω)
    (hE : ∀ r : ℤ_[p], E (algebraMap (O0 p) Ω (algebraMap ℤ_[p] (O0 p) r)) = 0)
    (x : Ω) (Q : ℤ_[p][X]) :
    E (eval₂ (phiZ p Ω) x Q) = eval₂ (phiZ p Ω) x (derivative Q) * E x := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ => rw [eval₂_add, map_add, hP, hQ, derivative_add, eval₂_add, add_mul]
  | monomial n c =>
    have hc : E (phiZ p Ω c) = 0 := hE c
    rw [eval₂_monomial, Derivation.leibniz, Derivation.leibniz_pow, hc, smul_zero, add_zero,
      derivative_monomial, eval₂_monomial]
    simp only [smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast]
    ring

/- English proof (translation)
Introduce `p _ Ω _ _ hC E hE x hx`. Use `haveI : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo hC`. Take `⟨P, hP0, hPx⟩` from `hx`. Rewrite `hPx` using `[aeval_def, eval₂_map]`. Express the relevant statement in the definitionally equal form `eval₂ (phiZ p Ω) x P = 0 at hPx`.

Assume the negation of the conclusion as `hEx`. Establish `key : ∀ n, ∀ P : ℤ_[p][X], P.natDegree = n → P ≠ 0 → eval₂ (phiZ p Ω) x P ≠ 0`. Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`.

Introduce `P hn hP hzero`. Distinguish the cases in `hd : P.natDegree = 0`. Rewrite `hzero` using `[eq_C_of_natDegree_eq_zero hd, eval₂_C]`. Use `phiZ_injective (p := p) (Ω := Ω) (hzero.trans (map_zero _).symm)` as an intermediate fact. Conclude with `hP (by rw [eq_C_of_natDegree_eq_zero hd, this, C_0])`.

Establish `hD : derivative P ≠ 0` using `fun h => hd (natDegree_eq_zero_of_derivative_eq_zero h)`. Establish `hlt` using `natDegree_derivative_lt hd`. Use `ih _ (hn ▸ hlt) (derivative P) rfl hD ?_` and prove the remaining obligations. Establish `h1` using `der_eval₂ E hE x P`. Rewrite `h1` using `[hzero, map_zero]`.

Conclude with `(mul_eq_zero.1 h1.symm).resolve_right hEx`. Conclude with `key _ P rfl hP0 hPx`.
-/
theorem der_algZp : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ E : Derivation ℤ Ω Ω, (∀ r : ℤ_[p], E (algebraMap (O0 p) Ω (algebraMap ℤ_[p] (O0 p) r)) = 0) →
    ∀ x : Ω, IsAlgZp p x → E x = 0 := by
  intro p _ Ω _ _ hC E hE x hx
  haveI : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo hC
  obtain ⟨P, hP0, hPx⟩ := hx
  rw [aeval_def, eval₂_map] at hPx
  change eval₂ (phiZ p Ω) x P = 0 at hPx
  by_contra hEx
  have key : ∀ n, ∀ P : ℤ_[p][X], P.natDegree = n → P ≠ 0 → eval₂ (phiZ p Ω) x P ≠ 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro P hn hP hzero
      by_cases hd : P.natDegree = 0
      · rw [eq_C_of_natDegree_eq_zero hd, eval₂_C] at hzero
        have := phiZ_injective (p := p) (Ω := Ω) (hzero.trans (map_zero _).symm)
        exact hP (by rw [eq_C_of_natDegree_eq_zero hd, this, C_0])
      · have hD : derivative P ≠ 0 := fun h => hd (natDegree_eq_zero_of_derivative_eq_zero h)
        have hlt := natDegree_derivative_lt hd
        refine ih _ (hn ▸ hlt) (derivative P) rfl hD ?_
        have h1 := der_eval₂ E hE x P
        rw [hzero, map_zero] at h1
        exact (mul_eq_zero.1 h1.symm).resolve_right hEx
  exact key _ P rfl hP0 hPx

end GlobalTheory.K5.DerAlg
