import Mathlib

set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace GlobalTheory.LocalCompletion

/- English proof (translation)
Introduce `A R _ _ _ _ _ hR φ hφ`. Set `I : Ideal A` to `maximalIdeal A`. Set `J : Ideal R` to `maximalIdeal R`. Establish `hmap : I.map φ ≤ J` using `((IsLocalRing.local_hom_TFAE φ).out 0 2).1 hφ`. Establish `hle : ∀ n : ℕ, I ^ n ≤ (J ^ n).comap φ` using `fun n => by`.

Rewrite using `[← Ideal.map_le_iff_le_comap, Ideal.map_pow]`. Conclude with `Ideal.pow_right_mono hmap n`. Set `g : ∀ n : ℕ, AdicCompletion I A →+* R ⧸ J ^ n` to `fun n => (Ideal.quotientMap (J ^ n) φ (hle n)).comp (AdicCompletion.evalₐ I n : AdicCompletion I A →+* A ⧸ I ^ n)`. Establish `hg : ∀ {m n : ℕ} (h : m ≤ n), (Ideal.Quotient.factorPow J h).comp (g n) = g m`. Introduce `m n h`.

Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `AdicCompletion.mk_surjective I A x`. Simplify using `only [g, RingHom.comp_apply, RingHom.coe_coe]`. Rewrite using `[AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, ← AdicCompletion.Ideal.mk_eq_mk I h x]`. Both sides reduce to the same expression.

Set `e : R ≃ₐ[R] AdicCompletion J R` to `AdicCompletion.ofAlgEquiv J`. Set `ψ : AdicCompletion I A →+* R` to `(e.symm : AdicCompletion J R →+* R).comp (AdicCompletion.liftRingHom J g hg)`. Establish `hψ : ψ.comp (algebraMap A (AdicCompletion I A)) = φ`. Use `RingHom.ext fun b => e.injective ?_` and prove the remaining obligations. Use `AdicCompletion.ext_evalₐ fun n => ?_` and prove the remaining obligations.

Simplify using `only [ψ, RingHom.comp_apply, RingHom.coe_coe, AlgEquiv.apply_symm_apply]`. Rewrite using `[AdicCompletion.evalₐ_liftRingHom]`. Express the relevant statement in the definitionally equal form `Ideal.quotientMap (J ^ n) φ (hle n) (AdicCompletion.evalₐ I n (algebraMap A _ b)) = _`. Rewrite using `[AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]`. Rewrite using `[show e (φ b) = algebraMap R (AdicCompletion J R) (φ b) from e.commutes (φ b), AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]`.

Both sides reduce to the same expression. Use `⟨ψ, ?_, hψ⟩` and prove the remaining obligations. Use `((IsLocalRing.local_hom_TFAE ψ).out 0 2).2 ?_` and prove the remaining obligations. Rewrite using `[AdicCompletion.maximalIdeal_eq_map, Ideal.map_map, hψ]`. Conclude with `hmap`.
-/
theorem exists_localHom_adicCompletion_extend :
    ∀ (A R : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing R] [IsLocalRing R],
      IsAdicComplete (maximalIdeal R) R → ∀ (φ : A →+* R), IsLocalHom φ →
      ∃ ψ : AdicCompletion (maximalIdeal A) A →+* R,
        IsLocalHom ψ ∧ ψ.comp (algebraMap A (AdicCompletion (maximalIdeal A) A)) = φ := by
  intro A R _ _ _ _ _ hR φ hφ
  let I : Ideal A := maximalIdeal A
  let J : Ideal R := maximalIdeal R
  have hmap : I.map φ ≤ J := ((IsLocalRing.local_hom_TFAE φ).out 0 2).1 hφ
  have hle : ∀ n : ℕ, I ^ n ≤ (J ^ n).comap φ := fun n => by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hmap n
  let g : ∀ n : ℕ, AdicCompletion I A →+* R ⧸ J ^ n := fun n =>
    (Ideal.quotientMap (J ^ n) φ (hle n)).comp (AdicCompletion.evalₐ I n : AdicCompletion I A →+* A ⧸ I ^ n)
  have hg : ∀ {m n : ℕ} (h : m ≤ n), (Ideal.Quotient.factorPow J h).comp (g n) = g m := by
    intro m n h
    refine RingHom.ext fun x => ?_
    obtain ⟨x, rfl⟩ := AdicCompletion.mk_surjective I A x
    simp only [g, RingHom.comp_apply, RingHom.coe_coe]
    rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, ← AdicCompletion.Ideal.mk_eq_mk I h x]
    rfl
  let e : R ≃ₐ[R] AdicCompletion J R := AdicCompletion.ofAlgEquiv J
  let ψ : AdicCompletion I A →+* R := (e.symm : AdicCompletion J R →+* R).comp (AdicCompletion.liftRingHom J g hg)
  have hψ : ψ.comp (algebraMap A (AdicCompletion I A)) = φ := by
    refine RingHom.ext fun b => e.injective ?_
    refine AdicCompletion.ext_evalₐ fun n => ?_
    simp only [ψ, RingHom.comp_apply, RingHom.coe_coe, AlgEquiv.apply_symm_apply]
    rw [AdicCompletion.evalₐ_liftRingHom]
    change Ideal.quotientMap (J ^ n) φ (hle n) (AdicCompletion.evalₐ I n (algebraMap A _ b)) = _
    rw [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
    rw [show e (φ b) = algebraMap R (AdicCompletion J R) (φ b) from e.commutes (φ b),
      AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
    rfl
  refine ⟨ψ, ?_, hψ⟩
  refine ((IsLocalRing.local_hom_TFAE ψ).out 0 2).2 ?_
  rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map, hψ]
  exact hmap

end GlobalTheory.LocalCompletion
