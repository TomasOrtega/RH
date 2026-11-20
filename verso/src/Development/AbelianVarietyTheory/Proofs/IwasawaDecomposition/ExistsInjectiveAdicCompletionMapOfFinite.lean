import Mathlib
open IsLocalRing

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[← AdicCompletion.factor_eval_eq_evalₐ I x (by simp), AdicCompletion.eval_apply]`. Use `erw [hd]`. Both sides reduce to the same expression.
-/
theorem adicCompletion_evalₐ_of_val {R : Type} [CommRing R] (I : Ideal R) (x : AdicCompletion I R)
    {n : ℕ} (d : R) (hd : x.val n = Submodule.Quotient.mk d) :
    AdicCompletion.evalₐ I n x = Ideal.Quotient.mk (I ^ n) d := by
  rw [← AdicCompletion.factor_eval_eq_evalₐ I x (by simp), AdicCompletion.eval_apply]
  erw [hd]
  rfl

/- English proof (translation)
Rewrite using `[← x.prop hmn, hd]`. Both sides reduce to the same expression.
-/
theorem adicCompletion_val_of_le {R : Type} [CommRing R] (I : Ideal R) (x : AdicCompletion I R)
    {m n : ℕ} (hmn : m ≤ n) (d : R) (hd : x.val n = Submodule.Quotient.mk d) :
    x.val m = Submodule.Quotient.mk d := by
  rw [← x.prop hmn, hd]
  rfl

/- English proof (translation)
Use `set φ := algebraMap D N with hφ`. Establish `hle : ∀ n : ℕ, J ^ n ≤ ((J.map φ) ^ n).comap φ` using `fun n => by`. Rewrite using `[← Ideal.map_pow]`. Conclude with `Ideal.le_comap_map`. Set `g : (n : ℕ) → AdicCompletion J D →+* N ⧸ (J.map φ) ^ n` to `fun n => (Ideal.quotientMap ((J.map φ) ^ n) φ (hle n)).comp (AdicCompletion.evalₐ J n).toRingHom`.

Establish `hg : ∀ {m n : ℕ} (hmn : m ≤ n), (Ideal.Quotient.factorPow (J.map φ) hmn).comp (g n) = g m`. Introduce `m n hmn`. Use extensionality with `x`. Take `⟨d, hd⟩` from `Submodule.Quotient.mk_surjective _ (x.val n)`. Establish `hn` using `adicCompletion_evalₐ_of_val J x d hd.symm`.

Establish `hm` using `adicCompletion_evalₐ_of_val J x d (adicCompletion_val_of_le J x hmn d hd.symm)`. Simplify using `only [g, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hn, hm, Ideal.quotientMap_mk]`. Both sides reduce to the same expression. Use `⟨AdicCompletion.liftRingHom _ g hg, ?_⟩` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `x hx`. Establish `hmap` using `AdicCompletion.map_injective J (f := Algebra.linearMap D N) hinj`. Apply `hmap` to reduce the goal to its premises. Rewrite using `[map_zero]`. Apply `AdicCompletion.ext` to reduce the goal to its premises.

Introduce `n`. Take `⟨d, hd⟩` from `Submodule.Quotient.mk_surjective _ (x.val n)`. Establish `h1` using `adicCompletion_evalₐ_of_val J x d hd.symm`. Establish `h2` using `congrArg (AdicCompletion.evalₐ (J.map φ) n) hx`. Rewrite `h2` using `[AdicCompletion.evalₐ_liftRingHom, map_zero]`.

Simplify using `only [g, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, h1, Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem] at h2`. Rewrite using `[AdicCompletion.map_val_apply]`. Use `erw [← hd]`. Rewrite using `[LinearMap.reduceModIdeal_apply]`. Use `((Submodule.Quotient.mk_eq_zero _).2 ?_).trans rfl` and prove the remaining obligations.

Rewrite using `[Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_pow]`. Conclude with `h2`.
-/
theorem adicCompletion_injective_ringHom_of_finite
    (D N : Type) [CommRing D] [CommRing N] [IsNoetherianRing D] [Algebra D N]
    [Module.Finite D N] (hinj : Function.Injective (algebraMap D N)) (J : Ideal D) :
    ∃ f : AdicCompletion J D →+* AdicCompletion (J.map (algebraMap D N)) N,
      Function.Injective f := by
  set φ := algebraMap D N with hφ
  have hle : ∀ n : ℕ, J ^ n ≤ ((J.map φ) ^ n).comap φ := fun n => by
    rw [← Ideal.map_pow]; exact Ideal.le_comap_map
  let g : (n : ℕ) → AdicCompletion J D →+* N ⧸ (J.map φ) ^ n := fun n =>
    (Ideal.quotientMap ((J.map φ) ^ n) φ (hle n)).comp (AdicCompletion.evalₐ J n).toRingHom
  have hg : ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorPow (J.map φ) hmn).comp (g n) = g m := by
    intro m n hmn
    ext x
    obtain ⟨d, hd⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
    have hn := adicCompletion_evalₐ_of_val J x d hd.symm
    have hm := adicCompletion_evalₐ_of_val J x d (adicCompletion_val_of_le J x hmn d hd.symm)
    simp only [g, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hn, hm,
      Ideal.quotientMap_mk]
    rfl
  refine ⟨AdicCompletion.liftRingHom _ g hg, ?_⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hmap := AdicCompletion.map_injective J (f := Algebra.linearMap D N) hinj
  apply hmap
  rw [map_zero]
  apply AdicCompletion.ext
  intro n
  obtain ⟨d, hd⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
  have h1 := adicCompletion_evalₐ_of_val J x d hd.symm
  have h2 := congrArg (AdicCompletion.evalₐ (J.map φ) n) hx
  rw [AdicCompletion.evalₐ_liftRingHom, map_zero] at h2
  simp only [g, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, h1,
    Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem] at h2
  rw [AdicCompletion.map_val_apply]
  erw [← hd]
  rw [LinearMap.reduceModIdeal_apply]
  refine ((Submodule.Quotient.mk_eq_zero _).2 ?_).trans rfl
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_pow]
  exact h2

end GlobalTheory
