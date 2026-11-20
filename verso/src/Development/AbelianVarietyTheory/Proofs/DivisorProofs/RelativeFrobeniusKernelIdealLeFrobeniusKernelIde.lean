import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal

set_option autoImplicit false

noncomputable section

open Coalgebra Bialgebra

namespace GlobalTheory.PDiv

open GlobalTheory.PDivGroup

/- English proof (translation)
Establish `h0` using `natCast_eq_zero_of_algebra h H`. Establish `e : a ^ p - algebraMap R H (counit (R` using `R) (a ^ p)) = (a - algebraMap R H (counit (R := R) a)) ^ p := by`. Rewrite using `[← frobRing_apply h0 (a - _), map_sub, frobRing_apply, frobRing_apply, counit_pow, map_pow]`. Rewrite using `[e]`. Conclude with `pow_mem_frobKerIdeal (by simp [RingHom.mem_ker])`.
-/
theorem pow_sub_counit_mem_frobKerIdeal {p : ℕ} [Fact p.Prime] {R H : Type} [CommRing R]
    [CommRing H] [Bialgebra R H] (h : (p : R) = 0) (a : H) :
    a ^ p - algebraMap R H (counit (R := R) (a ^ p)) ∈ frobKerIdeal p R H := by
  have h0 := natCast_eq_zero_of_algebra h H
  have e : a ^ p - algebraMap R H (counit (R := R) (a ^ p)) =
      (a - algebraMap R H (counit (R := R) a)) ^ p := by
    rw [← frobRing_apply h0 (a - _), map_sub, frobRing_apply, frobRing_apply, counit_pow, map_pow]
  rw [e]
  exact pow_mem_frobKerIdeal (by simp [RingHom.mem_ker])

/- English proof (translation)
Establish `key : ∀ x : (frobTwist h G).A n, (relFrob h G).app n x - algebraMap R (G.A n) (counit (R` using `R) ((relFrob h G).app n x)) ∈ frobKerIdeal p R (G.A n) := by`. Introduce `x`. Proceed by induction on `x using frobTwist_induction h n with`. Consider the case `h0 => simp`. Consider the case `h1 r a`.

Rewrite using `[map_smul, relFrob_app_frobProj, map_smul, smul_eq_mul, map_mul, Algebra.smul_def, ← mul_sub]`. Conclude with `Ideal.mul_mem_left _ _ (pow_sub_counit_mem_frobKerIdeal h a)`. Consider the case `h2 x y hx hy`. Rewrite using `[map_add, map_add, map_add, add_sub_add_comm]`. Conclude with `add_mem hx hy`.

Use `Ideal.map_le_iff_le_comap.2 fun x hx => ?_` and prove the remaining obligations. Establish `hx' : counit (R` using `R) x = 0 := hx`. Use `key x` as an intermediate fact. Rewrite `this` using `[CoalgHomClass.counit_comp_apply, hx', map_zero, sub_zero]`. Conclude with `this`.
-/
theorem kerIdeal_relFrob_le_frobKerIdeal (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (h : (p : R) = 0) (G : PDivGroup p R) (n : ℕ) :
    kerIdeal ((relFrob h G).app n) ≤ frobKerIdeal p R (G.A n) := by
  have key : ∀ x : (frobTwist h G).A n, (relFrob h G).app n x -
      algebraMap R (G.A n) (counit (R := R) ((relFrob h G).app n x)) ∈
        frobKerIdeal p R (G.A n) := by
    intro x
    induction x using frobTwist_induction h n with
    | h0 => simp
    | h1 r a =>
      rw [map_smul, relFrob_app_frobProj, map_smul, smul_eq_mul, map_mul, Algebra.smul_def,
        ← mul_sub]
      exact Ideal.mul_mem_left _ _ (pow_sub_counit_mem_frobKerIdeal h a)
    | h2 x y hx hy =>
      rw [map_add, map_add, map_add, add_sub_add_comm]
      exact add_mem hx hy
  refine Ideal.map_le_iff_le_comap.2 fun x hx => ?_
  have hx' : counit (R := R) x = 0 := hx
  have := key x
  rw [CoalgHomClass.counit_comp_apply, hx', map_zero, sub_zero] at this
  exact this

end GlobalTheory.PDiv
