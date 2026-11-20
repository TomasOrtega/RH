import Mathlib

namespace GlobalTheory

open Polynomial

/- English proof (translation)
Set `ψ : F →+* R` to `(TrivSqZeroExt.fstHom R R R).toRingHom.comp φ`. Establish `hψ : ∀ x, ψ x = (φ x).fst` using `fun x => rfl`. Establish `hcomp : φ.comp (algebraMap ℚ F) = (TrivSqZeroExt.inlHom R R).comp (ψ.comp (algebraMap ℚ F))` using `RingHom.ext_rat _ _`. Establish `hint : IsIntegral ℚ a` using `Algebra.IsIntegral.isIntegral a`. Establish `hsep : (minpoly ℚ a).Separable` using `(minpoly.irreducible hint).separable`.

Establish `hf0 : aeval a (minpoly ℚ a) = 0` using `minpoly.aeval ℚ a`. Establish `hd : aeval a (derivative (minpoly ℚ a)) ≠ 0` using `hsep.aeval_derivative_ne_zero hf0`. Establish `hu : IsUnit (ψ (aeval a (derivative (minpoly ℚ a))))` using `(isUnit_iff_ne_zero.mpr hd).map ψ`. Establish `hsplit : φ a = TrivSqZeroExt.inl (φ a).fst + TrivSqZeroExt.inr (φ a).snd` using `(TrivSqZeroExt.inl_fst_add_inr_snd_eq _).symm`. Establish `hsq : (TrivSqZeroExt.inr (φ a).snd : DualNumber R) ^ 2 = 0`.

Rewrite using `[sq, TrivSqZeroExt.inr_mul_inr]`. Establish `hev : ∀ p : ℚ[X], (p.map (φ.comp (algebraMap ℚ F))).eval (TrivSqZeroExt.inl (φ a).fst) = TrivSqZeroExt.inl (ψ (aeval a p))`. Introduce `p`. Rewrite using `[hcomp, eval_map, aeval_def, ← hψ, Polynomial.hom_eval₂]`. Express the relevant statement in the definitionally equal form `eval₂ _ (TrivSqZeroExt.inlHom R R (ψ a)) p = TrivSqZeroExt.inlHom R R _`.

Rewrite using `[Polynomial.hom_eval₂]`. Establish `hlhs : ((minpoly ℚ a).map (φ.comp (algebraMap ℚ F))).eval (φ a) = 0`. Rewrite using `[eval_map, ← Polynomial.hom_eval₂, ← aeval_def, hf0, map_zero]`. Establish `key` using `eval_add_of_sq_eq_zero ((minpoly ℚ a).map (φ.comp (algebraMap ℚ F))) (TrivSqZeroExt.inl (φ a).fst) (TrivSqZeroExt.inr (φ a).snd) hsq`. Rewrite `key` using `[← hsplit, hlhs, derivative_map, hev, hev, hf0, map_zero]`.

Establish `h2` using `congrArg TrivSqZeroExt.snd key`. Simplify using `only [TrivSqZeroExt.snd_zero, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, DualNumber.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_inr, mul_zero, zero_add, add_zero] at h2`. Conclude with `(hu.mul_right_eq_zero).mp h2.symm`.
-/
theorem ringHom_dualNumber_snd_eq_zero (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F]
    {R : Type} [CommRing R] (φ : F →+* DualNumber R) (a : F) : (φ a).snd = 0 := by
  classical
  let ψ : F →+* R := (TrivSqZeroExt.fstHom R R R).toRingHom.comp φ
  have hψ : ∀ x, ψ x = (φ x).fst := fun x => rfl
  have hcomp : φ.comp (algebraMap ℚ F) =
      (TrivSqZeroExt.inlHom R R).comp (ψ.comp (algebraMap ℚ F)) := RingHom.ext_rat _ _
  have hint : IsIntegral ℚ a := Algebra.IsIntegral.isIntegral a
  have hsep : (minpoly ℚ a).Separable := (minpoly.irreducible hint).separable
  have hf0 : aeval a (minpoly ℚ a) = 0 := minpoly.aeval ℚ a
  have hd : aeval a (derivative (minpoly ℚ a)) ≠ 0 := hsep.aeval_derivative_ne_zero hf0
  have hu : IsUnit (ψ (aeval a (derivative (minpoly ℚ a)))) := (isUnit_iff_ne_zero.mpr hd).map ψ
  have hsplit : φ a = TrivSqZeroExt.inl (φ a).fst + TrivSqZeroExt.inr (φ a).snd :=
    (TrivSqZeroExt.inl_fst_add_inr_snd_eq _).symm
  have hsq : (TrivSqZeroExt.inr (φ a).snd : DualNumber R) ^ 2 = 0 := by
    rw [sq, TrivSqZeroExt.inr_mul_inr]
  have hev : ∀ p : ℚ[X], (p.map (φ.comp (algebraMap ℚ F))).eval (TrivSqZeroExt.inl (φ a).fst) =
      TrivSqZeroExt.inl (ψ (aeval a p)) := by
    intro p
    rw [hcomp, eval_map, aeval_def, ← hψ, Polynomial.hom_eval₂]
    change eval₂ _ (TrivSqZeroExt.inlHom R R (ψ a)) p = TrivSqZeroExt.inlHom R R _
    rw [Polynomial.hom_eval₂]
  have hlhs : ((minpoly ℚ a).map (φ.comp (algebraMap ℚ F))).eval (φ a) = 0 := by
    rw [eval_map, ← Polynomial.hom_eval₂, ← aeval_def, hf0, map_zero]
  have key := eval_add_of_sq_eq_zero ((minpoly ℚ a).map (φ.comp (algebraMap ℚ F)))
    (TrivSqZeroExt.inl (φ a).fst) (TrivSqZeroExt.inr (φ a).snd) hsq
  rw [← hsplit, hlhs, derivative_map, hev, hev, hf0, map_zero] at key
  have h2 := congrArg TrivSqZeroExt.snd key
  simp only [TrivSqZeroExt.snd_zero, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
    DualNumber.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_inr,
    mul_zero, zero_add, add_zero] at h2
  exact (hu.mul_right_eq_zero).mp h2.symm

end GlobalTheory
