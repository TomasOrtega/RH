import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.RootSumWOff

open NumberField

namespace UpperTheory.Gal.W2

/- English proof (translation)
Introduce `F _ _ φ`. Establish `hker : RingHom.ker φ = ⊥`. Apply `Ideal.eq_bot_of_comap_eq_bot (R := ℤ)` to reduce the goal to its premises. Rewrite using `[eq_bot_iff]`. Introduce `n hn`.

Rewrite `hn` using `[Ideal.mem_comap, RingHom.mem_ker, eq_intCast, map_intCast]`. Rewrite using `[Ideal.mem_bot]`. Conclude with `hn` after adjusting the coercions. Establish `hinj : Function.Injective φ` using `(RingHom.injective_iff_ker_eq_bot φ).2 hker`. Use `⟨IsFractionRing.lift (K := F) hinj, fun c => ?_⟩` and prove the remaining obligations.

Conclude with `(IsFractionRing.lift_algebraMap (K := F) hinj c).symm`.
-/
theorem extendEmb_of : ExtendEmb := by
  intro F _ _ φ
  have hker : RingHom.ker φ = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    rw [eq_bot_iff]
    intro n hn
    rw [Ideal.mem_comap, RingHom.mem_ker, eq_intCast, map_intCast] at hn
    rw [Ideal.mem_bot]
    exact_mod_cast hn
  have hinj : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).2 hker
  refine ⟨IsFractionRing.lift (K := F) hinj, fun c => ?_⟩
  exact (IsFractionRing.lift_algebraMap (K := F) hinj c).symm

end UpperTheory.Gal.W2
