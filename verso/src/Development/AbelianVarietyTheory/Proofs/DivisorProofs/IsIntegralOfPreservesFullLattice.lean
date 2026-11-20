import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMat
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.UnitLemma

/- English proof (translation)
Proceed by induction on `q using Polynomial.induction_on' with`. Consider the case `add a b ha hb => simp only [map_add, LinearMap.add_apply, Submodule.coe_add, ha, hb]`. Consider the case `monomial n a`. Establish `hpow : ∀ (k : ℕ) (y : N), ((((f.restrict h) ^ k) y : N) : M) = (f ^ k) y`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => intro y`. Both sides reduce to the same expression. Consider the case `succ k ih`. Introduce `y`.

Rewrite using `[pow_succ', Module.End.mul_apply, LinearMap.coe_restrict_apply, ih, pow_succ', Module.End.mul_apply]`. Simplify using `only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, Submodule.coe_smul, hpow]`.
-/
theorem aeval_restrict_coe_of_stable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (f : Module.End R M) {N : Submodule R M} (h : ∀ x ∈ N, f x ∈ N) (q : R[X]) (x : N) :
    ((aeval (f.restrict h) q x : N) : M) = aeval f q x := by
  induction q using Polynomial.induction_on' with
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, Submodule.coe_add, ha, hb]
  | monomial n a =>
    have hpow : ∀ (k : ℕ) (y : N), ((((f.restrict h) ^ k) y : N) : M) = (f ^ k) y := by
      intro k
      induction k with
      | zero => intro y; rfl
      | succ k ih =>
        intro y
        rw [pow_succ', Module.End.mul_apply, LinearMap.coe_restrict_apply, ih, pow_succ', Module.End.mul_apply]
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, Submodule.coe_smul, hpow]

/- English proof (translation)
Introduce `K B u L hL hu`. Use `haveI : Module.Finite K.O L := Module.Finite.iff_fg.mpr hL.1`. Set `f : Module.End K.O B.A` to `LinearMap.mulLeft K.O u`. Establish `hf : ∀ x ∈ L, f x ∈ L` using `hu`. Take `⟨p, hpm, hp⟩` from `LinearMap.exists_monic_and_aeval_eq_zero K.O (f.restrict hf)`.

Use `⟨p, hpm, ?_⟩` and prove the remaining obligations. Establish `hlmul : aeval f p = LinearMap.mulLeft K.O (aeval u p)`. Establish `: f = Algebra.lmul K.O B.A u` using `rfl`. Rewrite using `[this, Polynomial.aeval_algHom_apply]`. Both sides reduce to the same expression.

Establish `key : ∀ x ∈ L, aeval u p * x = 0`. Introduce `x hx`. Establish `h1` using `aeval_restrict_coe_of_stable f hf p ⟨x, hx⟩`. Rewrite `h1` using `[hp, hlmul]`. Simplify using `using h1.symm`.

Establish `hall : ∀ a : B.A, aeval u p * a = 0`. Introduce `a`. Establish `ha : a ∈ Submodule.span K.E (L : Set B.A)` using `hL.2 ▸ Submodule.mem_top`. Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem x hx => exact key x hx`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]`. Consider the case `smul c x _ hx => rw [mul_smul_comm, hx, smul_zero]`. Use `hall 1` as an intermediate fact. Rewrite `this` using `[mul_one]`.

Conclude with `this`.
-/
theorem isIntegral_of_lat_stable : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (u : B.A)
    (L : Submodule K.O B.A), GlobalTheory.UnitLemma.IsLat K.O K.E L → (∀ z ∈ L, u * z ∈ L) → IsIntegral K.O u := by
  intro K B u L hL hu
  haveI : Module.Finite K.O L := Module.Finite.iff_fg.mpr hL.1
  let f : Module.End K.O B.A := LinearMap.mulLeft K.O u
  have hf : ∀ x ∈ L, f x ∈ L := hu
  obtain ⟨p, hpm, hp⟩ := LinearMap.exists_monic_and_aeval_eq_zero K.O (f.restrict hf)
  refine ⟨p, hpm, ?_⟩
  have hlmul : aeval f p = LinearMap.mulLeft K.O (aeval u p) := by
    have : f = Algebra.lmul K.O B.A u := rfl
    rw [this, Polynomial.aeval_algHom_apply]
    rfl
  have key : ∀ x ∈ L, aeval u p * x = 0 := by
    intro x hx
    have h1 := aeval_restrict_coe_of_stable f hf p ⟨x, hx⟩
    rw [hp, hlmul] at h1
    simpa using h1.symm
  have hall : ∀ a : B.A, aeval u p * a = 0 := by
    intro a
    have ha : a ∈ Submodule.span K.E (L : Set B.A) := hL.2 ▸ Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem x hx => exact key x hx
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
    | smul c x _ hx => rw [mul_smul_comm, hx, smul_zero]
  have := hall 1
  rw [mul_one] at this
  exact this

end GlobalTheory.UnitLemma
