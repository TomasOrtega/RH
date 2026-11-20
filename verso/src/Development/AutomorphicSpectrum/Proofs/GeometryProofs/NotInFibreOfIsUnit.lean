import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.MemEigSpOfMemHtDual
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

/- English proof (translation)
The claim follows from `IsLocalRing.of_surjective' (genMap ξ q).rangeRestrict (genMap ξ q).rangeRestrict_surjective`.
-/
theorem regAt_isLocalRing (q : Cpt ξ) : IsLocalRing (regAt ξ q) :=
  IsLocalRing.of_surjective' (genMap ξ q).rangeRestrict (genMap ξ q).rangeRestrict_surjective

/- English proof (translation)
Take `⟨v, hv⟩` from `h.exists_right_inv`. Establish `e : (p : Ω) * (v : Ω) = 1`. Use `congrArg (Subtype.val) hv` as an intermediate fact. Simplify using `using this`. Establish `hp : (p : Ω) ≠ 0` using `left_ne_zero_of_mul_eq_one e`.

Establish `hreg : (p : Ω) ∈ regAt ξ q` using `natCast_mem (regAt ξ q) p`. Establish `hinv : (p : Ω)⁻¹ ∈ regAt ξ q`. Rewrite using `[eq_comm.1 (eq_inv_of_mul_eq_one_right e)]`. Conclude with `v.2`. Conclude with `not_not.2 ⟨hp, hreg, hinv⟩`.
-/
theorem not_inFibre_of_isUnit {q : Cpt ξ} {p : ℕ} (h : IsUnit (p : regAt ξ q)) : ¬ InFibre ξ p q := by
  obtain ⟨v, hv⟩ := h.exists_right_inv
  have e : (p : Ω) * (v : Ω) = 1 := by
    have := congrArg (Subtype.val) hv
    simpa using this
  have hp : (p : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one e
  have hreg : (p : Ω) ∈ regAt ξ q := natCast_mem (regAt ξ q) p
  have hinv : (p : Ω)⁻¹ ∈ regAt ξ q := by
    rw [eq_comm.1 (eq_inv_of_mul_eq_one_right e)]
    exact v.2
  exact not_not.2 ⟨hp, hreg, hinv⟩

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `haveI := regAt_isLocalRing (ξ := ξ) q`. Establish `hc : IsCoprime (p : ℤ) (p' : ℤ)` using `Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hp').2 (Ne.symm hne))`. Take `⟨a, b, hab⟩` from `hc.map (Int.castRingHom (regAt ξ q))`. Simplify using `only [eq_intCast, Int.cast_natCast] at hab`.

Break down `IsLocalRing.isUnit_or_isUnit_of_add_one hab with hu | hu` into its components or cases. Conclude with `not_inFibre_of_isUnit (isUnit_of_mul_isUnit_right hu) h`. Conclude with `not_inFibre_of_isUnit (isUnit_of_mul_isUnit_right hu) h'`.
-/
theorem inFibre_unique {q : Cpt ξ} {p p' : ℕ} (hp : p.Prime) (hp' : p'.Prime) (h : InFibre ξ p q)
    (h' : InFibre ξ p' q) : p' = p := by
  by_contra hne
  haveI := regAt_isLocalRing (ξ := ξ) q
  have hc : IsCoprime (p : ℤ) (p' : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hp').2 (Ne.symm hne))
  obtain ⟨a, b, hab⟩ := hc.map (Int.castRingHom (regAt ξ q))
  simp only [eq_intCast, Int.cast_natCast] at hab
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with hu | hu
  · exact not_inFibre_of_isUnit (isUnit_of_mul_isUnit_right hu) h
  · exact not_inFibre_of_isUnit (isUnit_of_mul_isUnit_right hu) h'

end GlobalTheory.CompanionTheory.Ar
