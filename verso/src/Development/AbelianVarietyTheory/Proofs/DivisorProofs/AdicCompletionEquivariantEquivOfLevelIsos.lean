import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorPowCompAdicCompletionMapToQuotientPow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.InvAlg.Levels

abbrev red {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (I : Ideal A) {k n : ℕ} (h : k ≤ n) :
    A ⧸ I ^ n →ₐ[R] A ⧸ I ^ k :=
  Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right h)

/- English proof (translation)
Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Both sides reduce to the same expression.
-/
theorem red_red {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (I : Ideal A) {k l n : ℕ} (h₁ : k ≤ l)
    (h₂ : l ≤ n) (z : A ⧸ I ^ n) : red (R := R) I h₁ (red (R := R) I h₂ z) = red (R := R) I (h₁.trans h₂) z := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  rfl

/- English proof (translation)
Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Both sides reduce to the same expression.
-/
theorem red_refl {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (I : Ideal A) {n : ℕ}
    (z : A ⧸ I ^ n) : red (R := R) I (le_refl n) z = z := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  rfl

/- English proof (translation)
The claim follows from `GlobalTheory.InvAlg.factorPow_evalₐ I h x`.
-/
theorem red_evalₐ {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (I : Ideal A) {k n : ℕ} (h : k ≤ n)
    (x : AdicCompletion I A) :
    red (R := R) I h (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I k x :=
  GlobalTheory.InvAlg.factorPow_evalₐ I h x

/- English proof (translation)
Proceed by induction on `n, h using Nat.le_induction with`. Consider the case `base => rw [red_refl, red_refl]`. Consider the case `succ n hkn ih`. Rewrite using `[← red_red (R := R) J (Nat.succ_le_succ hkn) (Nat.le_succ (n + 1)), hβ, ih, red_red]`.
-/
theorem compat_le {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (I : Ideal A) (J : Ideal B) (β : ∀ n : ℕ, A ⧸ I ^ (n + 1) →ₐ[R] B ⧸ J ^ (n + 1))
    (hβ : ∀ n z, red (R := R) J (Nat.le_succ (n + 1)) (β (n + 1) z) = β n (red (R := R) I (Nat.le_succ (n + 1)) z))
    {k n : ℕ} (h : k ≤ n) (z : A ⧸ I ^ (n + 1)) :
    red (R := R) J (Nat.succ_le_succ h) (β n z) = β k (red (R := R) I (Nat.succ_le_succ h) z) := by
  induction n, h using Nat.le_induction with
  | base => rw [red_refl, red_refl]
  | succ n hkn ih =>
    rw [← red_red (R := R) J (Nat.succ_le_succ hkn) (Nat.le_succ (n + 1)), hβ, ih, red_red]

/- English proof (translation)
Establish `hβ' : ∀ n z, red (R` using `R) I (Nat.le_succ (n + 1)) ((β (n + 1)).symm z) = (β n).symm (red (R := R) J (Nat.le_succ (n + 1)) z) := by`. Introduce `n z`. Apply `(β n).injective` to reduce the goal to its premises. Rewrite using `[AlgEquiv.apply_symm_apply, ← hβ, AlgEquiv.apply_symm_apply]`. Establish `key : ∀ {A B : Type} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (I : Ideal A) (J : Ideal B) (β : ∀ n : ℕ, A ⧸ I ^ (n + 1) →ₐ[R] B ⧸ J ^ (n + 1)) (hβ : ∀ n z, red (R` using `R) J (Nat.le_succ (n + 1)) (β (n + 1) z) = β n (red (R := R) I (Nat.le_succ (n + 1)) z)), ∃ Φ : AdicCompletion I A →ₐ[R] AdicCompletion J B, ∀ n y, AdicCompletion.evalₐ J (n + 1) (Φ y) = β n (AdicCompletion.evalₐ I (n + 1) y) := by`.

Introduce `A B _ _ _ _ I J β hβ`. Set `f : ∀ n, AdicCompletion I A →ₐ[R] B ⧸ J ^ n` to `fun n => (red (R := R) J (Nat.le_succ n)).comp ((β n).comp ((AdicCompletion.evalₐ I (n + 1)).restrictScalars R))`. Establish `hf : ∀ {k n : ℕ} (hle : k ≤ n), (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hle)).comp (f n) = f k`. Introduce `k n hle`. Use `AlgHom.ext fun y => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `red (R := R) J hle (red (R := R) J (Nat.le_succ n) (β n (AdicCompletion.evalₐ I (n + 1) y))) = red (R := R) J (Nat.le_succ k) (β k (AdicCompletion.evalₐ I (k + 1) y))`. Rewrite using `[red_red, ← red_red (R := R) J (Nat.le_succ k) (Nat.succ_le_succ hle), compat_le I J β hβ hle, red_evalₐ]`. Use `⟨AdicCompletion.liftAlgHom J f hf, fun n y => ?_⟩` and prove the remaining obligations. Rewrite using `[AdicCompletion.evalₐ_liftAlgHom]`. Express the relevant statement in the definitionally equal form `red (R := R) J (Nat.le_succ (n + 1)) (β (n + 1) (AdicCompletion.evalₐ I (n + 1 + 1) y)) = _`.

Rewrite using `[hβ, red_evalₐ]`. Take `⟨Φ, hΦ⟩` from `key I J (fun n => (β n).toAlgHom) hβ`. Take `⟨Φ', hΦ'⟩` from `key J I (fun n => (β n).symm.toAlgHom) hβ'`. Establish `ev : ∀ {A : Type} [CommRing A] [Algebra R A] (I : Ideal A) (x y : AdicCompletion I A), (∀ n, AdicCompletion.evalₐ I (n + 1) x = AdicCompletion.evalₐ I (n + 1) y) → x = y`. Introduce `A _ _ I x y h`.

Use `AdicCompletion.ext_evalₐ fun n => ?_` and prove the remaining obligations. Rewrite using `[← red_evalₐ (R := R) I (Nat.le_succ n) x, ← red_evalₐ (R := R) I (Nat.le_succ n) y, h]`. Use `⟨AlgEquiv.ofAlgHom Φ Φ' ?_ ?_, hΦ⟩` and prove the remaining obligations. Use `AlgHom.ext fun y => ?_` and prove the remaining obligations. Use `ev J _ _ fun n => ?_` and prove the remaining obligations.

Simplify using `only [AlgHom.comp_apply, AlgHom.id_apply]`. Rewrite using `[hΦ, hΦ']`. Conclude with `AlgEquiv.apply_symm_apply _ _`. Use `AlgHom.ext fun y => ?_` and prove the remaining obligations. Use `ev I _ _ fun n => ?_` and prove the remaining obligations.

Simplify using `only [AlgHom.comp_apply, AlgHom.id_apply]`. Rewrite using `[hΦ', hΦ]`. Conclude with `AlgEquiv.symm_apply_apply _ _`.
-/
theorem exists_equiv {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (I : Ideal A) (J : Ideal B) (β : ∀ n : ℕ, (A ⧸ I ^ (n + 1)) ≃ₐ[R] (B ⧸ J ^ (n + 1)))
    (hβ : ∀ n z, red (R := R) J (Nat.le_succ (n + 1)) (β (n + 1) z) = β n (red (R := R) I (Nat.le_succ (n + 1)) z)) :
    ∃ Ψ : AdicCompletion I A ≃ₐ[R] AdicCompletion J B,
      ∀ n y, AdicCompletion.evalₐ J (n + 1) (Ψ y) = β n (AdicCompletion.evalₐ I (n + 1) y) := by
  have hβ' : ∀ n z, red (R := R) I (Nat.le_succ (n + 1)) ((β (n + 1)).symm z) =
      (β n).symm (red (R := R) J (Nat.le_succ (n + 1)) z) := by
    intro n z
    apply (β n).injective
    rw [AlgEquiv.apply_symm_apply, ← hβ, AlgEquiv.apply_symm_apply]
  have key : ∀ {A B : Type} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (I : Ideal A) (J : Ideal B)
      (β : ∀ n : ℕ, A ⧸ I ^ (n + 1) →ₐ[R] B ⧸ J ^ (n + 1))
      (hβ : ∀ n z, red (R := R) J (Nat.le_succ (n + 1)) (β (n + 1) z) = β n (red (R := R) I (Nat.le_succ (n + 1)) z)),
      ∃ Φ : AdicCompletion I A →ₐ[R] AdicCompletion J B,
        ∀ n y, AdicCompletion.evalₐ J (n + 1) (Φ y) = β n (AdicCompletion.evalₐ I (n + 1) y) := by
    intro A B _ _ _ _ I J β hβ
    let f : ∀ n, AdicCompletion I A →ₐ[R] B ⧸ J ^ n := fun n =>
      (red (R := R) J (Nat.le_succ n)).comp ((β n).comp ((AdicCompletion.evalₐ I (n + 1)).restrictScalars R))
    have hf : ∀ {k n : ℕ} (hle : k ≤ n), (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hle)).comp (f n) = f k := by
      intro k n hle
      refine AlgHom.ext fun y => ?_
      change red (R := R) J hle (red (R := R) J (Nat.le_succ n) (β n (AdicCompletion.evalₐ I (n + 1) y))) =
        red (R := R) J (Nat.le_succ k) (β k (AdicCompletion.evalₐ I (k + 1) y))
      rw [red_red, ← red_red (R := R) J (Nat.le_succ k) (Nat.succ_le_succ hle), compat_le I J β hβ hle, red_evalₐ]
    refine ⟨AdicCompletion.liftAlgHom J f hf, fun n y => ?_⟩
    rw [AdicCompletion.evalₐ_liftAlgHom]
    change red (R := R) J (Nat.le_succ (n + 1)) (β (n + 1) (AdicCompletion.evalₐ I (n + 1 + 1) y)) = _
    rw [hβ, red_evalₐ]
  obtain ⟨Φ, hΦ⟩ := key I J (fun n => (β n).toAlgHom) hβ
  obtain ⟨Φ', hΦ'⟩ := key J I (fun n => (β n).symm.toAlgHom) hβ'
  have ev : ∀ {A : Type} [CommRing A] [Algebra R A] (I : Ideal A) (x y : AdicCompletion I A),
      (∀ n, AdicCompletion.evalₐ I (n + 1) x = AdicCompletion.evalₐ I (n + 1) y) → x = y := by
    intro A _ _ I x y h
    refine AdicCompletion.ext_evalₐ fun n => ?_
    rw [← red_evalₐ (R := R) I (Nat.le_succ n) x, ← red_evalₐ (R := R) I (Nat.le_succ n) y, h]
  refine ⟨AlgEquiv.ofAlgHom Φ Φ' ?_ ?_, hΦ⟩
  · refine AlgHom.ext fun y => ?_
    refine ev J _ _ fun n => ?_
    simp only [AlgHom.comp_apply, AlgHom.id_apply]
    rw [hΦ, hΦ']
    exact AlgEquiv.apply_symm_apply _ _
  · refine AlgHom.ext fun y => ?_
    refine ev I _ _ fun n => ?_
    simp only [AlgHom.comp_apply, AlgHom.id_apply]
    rw [hΦ', hΦ]
    exact AlgEquiv.symm_apply_apply _ _

end GlobalTheory.InvAlg.Levels

namespace GlobalTheory.InvAlg.Levels

/- English proof (translation)
Introduce `R _ m R' _ _ C' _ _ _ _ act hact O _ _ i hi1 hi2 hi3 IT IC hIT hIC hT hC`. Substitute `hIT hIC` using the available equality. Set `L : ∀ e, TensorProduct R O R' →ₐ[R] C' ⧸ (m ^ (e + 1)).map (algebraMap R C')` to `fun e => Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _`. Establish `hCpow : ∀ e, (m ^ (e + 1)).map (algebraMap R C') = (m.map (algebraMap R C')) ^ (e + 1)` using `fun e => Ideal.map_pow _ _ _`. Establish `hTpow : ∀ e, (m ^ (e + 1)).map (algebraMap R (TensorProduct R O R')) = (m.map (algebraMap R (TensorProduct R O R'))) ^ (e + 1)` using `fun e => Ideal.map_pow _ _ _`.

Set `E : ∀ e, (C' ⧸ (m ^ (e + 1)).map (algebraMap R C')) ≃ₐ[R] (C' ⧸ (m.map (algebraMap R C')) ^ (e + 1))` to `fun e => Ideal.quotientEquivAlgOfEq R (hCpow e)`. Set `L' : ∀ e, TensorProduct R O R' →ₐ[R] C' ⧸ (m.map (algebraMap R C')) ^ (e + 1)` to `fun e => (E e).toAlgHom.comp (L e)`. Establish `hsurj : ∀ e, Function.Surjective (L' e)` using `fun e => (E e).surjective.comp (hi3 e).1`. Establish `hker : ∀ e, RingHom.ker (L' e) = (m.map (algebraMap R (TensorProduct R O R'))) ^ (e + 1)`. Introduce `e`.

Use extensionality with `t`. Rewrite using `[RingHom.mem_ker, ← hTpow, ← (hi3 e).2, RingHom.mem_ker]`. Conclude with `map_eq_zero_iff (E e) (E e).injective`. Set `β : ∀ e, (TensorProduct R O R' ⧸ (m.map (algebraMap R (TensorProduct R O R'))) ^ (e + 1)) ≃ₐ[R] (C' ⧸ (m.map (algebraMap R C')) ^ (e + 1))` to `fun e => (Ideal.quotientEquivAlgOfEq R (hker e).symm).trans (Ideal.quotientKerAlgEquivOfSurjective (hsurj e))`. Establish `hβmk : ∀ e t, β e (Ideal.Quotient.mk _ t) = L' e t` using `fun e t => rfl`.

Establish `hL : ∀ e x r y, Ideal.Quotient.mk _ y = i e x → L' e (x ⊗ₜ[R] r) = Ideal.Quotient.mk _ (y * algebraMap R' C' r)`. Introduce `e x r y hy`. Express the relevant statement in the definitionally equal form `E e (L e (x ⊗ₜ[R] r)) = _`. Rewrite using `[Algebra.TensorProduct.lift_tmul, ← hy]`. Express the relevant statement in the definitionally equal form `E e (Ideal.Quotient.mk _ y * Ideal.Quotient.mk _ (algebraMap R' C' r)) = _`.

Rewrite using `[← map_mul]`. Conclude with `Ideal.quotientEquivAlgOfEq_mk _ _ _`. Establish `hred : ∀ n z, red (R` using `R) (m.map (algebraMap R C')) (Nat.le_succ (n + 1)) (β (n + 1) z) = β n (red (R := R) (m.map (algebraMap R (TensorProduct R O R'))) (Nat.le_succ (n + 1)) z) := by`. Introduce `n z`. Take `⟨t, rfl⟩` from `Ideal.Quotient.mk_surjective z`.

Express the relevant statement in the definitionally equal form `red (R := R) (m.map (algebraMap R C')) (Nat.le_succ (n + 1)) (L' (n + 1) t) = L' n t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `tmul x r`. Take `⟨y, hy⟩` from `Ideal.Quotient.mk_surjective (i (n + 1) x)`.

Rewrite using `[hL (n + 1) x r y hy, hL n x r y (hi1 n x y hy)]`. Both sides reduce to the same expression. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Take `⟨Ψ, hΨ⟩` from `exists_equiv _ _ β hred`. Establish `ev : ∀ {A : Type} [CommRing A] (I : Ideal A) (x y : AdicCompletion I A), (∀ n, AdicCompletion.evalₐ I (n + 1) x = AdicCompletion.evalₐ I (n + 1) y) → x = y`.

Introduce `A _ I x y h`. Use `AdicCompletion.ext_evalₐ fun n => ?_` and prove the remaining obligations. Rewrite using `[← GlobalTheory.InvAlg.factorPow_evalₐ I (Nat.le_succ n) x, ← GlobalTheory.InvAlg.factorPow_evalₐ I (Nat.le_succ n) y, h]`. Use `⟨Ψ, fun σ y => ev _ _ _ fun n => ?_, fun e x y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[hΨ, GlobalTheory.InvAlg.evalₐ_cmap, GlobalTheory.InvAlg.evalₐ_cmap, hΨ]`.

Take `⟨t, ht⟩` from `Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ _ (n + 1) y)`. Rewrite using `[← ht, Ideal.quotientMap_mk, hβmk, hβmk]`. Use `clear ht`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`.

Consider the case `tmul x r`. Take `⟨y, hy⟩` from `Ideal.Quotient.mk_surjective (i n x)`. Establish `h1 : (GlobalTheory.InvAlg.galTensor O σ).toRingHom (x ⊗ₜ[R] r) = x ⊗ₜ[R] σ.1 r` using `rfl`. Rewrite using `[h1, hL n x _ y hy, hL n x r y hy, Ideal.quotientMap_mk]`. Express the relevant statement in the definitionally equal form `_ = Ideal.Quotient.mk _ (act σ (y * algebraMap R' C' r))`.

Rewrite using `[map_mul (act σ), hact, map_mul (Ideal.Quotient.mk _), map_mul (Ideal.Quotient.mk _)]`. Use `congr 1`. Establish `h2` using `hi2 n σ x y hy`. Rewrite `h2` using `[← hy, Ideal.Quotient.eq, hCpow]`. Rewrite using `[Ideal.Quotient.eq, ← neg_sub]`.

Conclude with `neg_mem h2`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Rewrite using `[hΨ, AdicCompletion.evalₐ_of, hβmk, hL e x 1 y hy, map_one, _root_.mul_one]`.
-/
theorem levels_equiv : ∀ (R : Type) [CommRing R] (m : Ideal R) (R' : Type) [CommRing R'] [Algebra R R'] (C' : Type) [CommRing C']
    [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] (act : GlobalTheory.Mum.Gal (algebraMap R R') →* (C' ≃ₐ[R] C')),
    (∀ σ r, act σ (algebraMap R' C' r) = algebraMap R' C' (σ.1 r)) →
    ∀ (O : Type) [CommRing O] [Algebra R O] (i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (m ^ (e + 1)).map (algebraMap R C')),
    (∀ e x y, Ideal.Quotient.mk _ y = i (e + 1) x → Ideal.Quotient.mk _ y = i e x) →
    (∀ e σ x y, Ideal.Quotient.mk _ y = i e x → Ideal.Quotient.mk _ (act σ y) = i e x) →
    (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i e)
        ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧
      RingHom.ker (Algebra.TensorProduct.lift (i e)
        ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) =
        (m ^ (e + 1)).map (algebraMap R (TensorProduct R O R'))) →
    ∀ (IT : Ideal (TensorProduct R O R')) (IC : Ideal C'), IT = m.map (algebraMap R (TensorProduct R O R')) →
      IC = m.map (algebraMap R C') →
    ∀ (hT : ∀ σ, IT.map (GlobalTheory.InvAlg.galTensor O σ).toRingHom ≤ IT)
      (hC : ∀ σ, IC.map (act σ).toRingEquiv.toRingHom ≤ IC),
    ∃ Ψ : AdicCompletion IT (TensorProduct R O R') ≃ₐ[R] AdicCompletion IC C',
      (∀ σ y, Ψ (GlobalTheory.InvAlg.cmap (GlobalTheory.InvAlg.galTensor O σ).toRingHom
          IT IT (hT σ) y) = GlobalTheory.InvAlg.cmap (act σ).toRingEquiv.toRingHom IC IC (hC σ) (Ψ y)) ∧
      ∀ e (x : O) (y : C'), Ideal.Quotient.mk ((m ^ (e + 1)).map (algebraMap R C')) y = i e x →
        AdicCompletion.evalₐ IC (e + 1) (Ψ (AdicCompletion.of IT _ (x ⊗ₜ[R] (1 : R')))) =
          Ideal.Quotient.mk (IC ^ (e + 1)) y := by
  intro R _ m R' _ _ C' _ _ _ _ act hact O _ _ i hi1 hi2 hi3 IT IC hIT hIC hT hC
  subst hIT hIC
  let L : ∀ e, TensorProduct R O R' →ₐ[R] C' ⧸ (m ^ (e + 1)).map (algebraMap R C') := fun e =>
    Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C'))
      fun _ _ => Commute.all _ _
  have hCpow : ∀ e, (m ^ (e + 1)).map (algebraMap R C') = (m.map (algebraMap R C')) ^ (e + 1) :=
    fun e => Ideal.map_pow _ _ _
  have hTpow : ∀ e, (m ^ (e + 1)).map (algebraMap R (TensorProduct R O R')) =
      (m.map (algebraMap R (TensorProduct R O R'))) ^ (e + 1) :=
    fun e => Ideal.map_pow _ _ _
  let E : ∀ e, (C' ⧸ (m ^ (e + 1)).map (algebraMap R C')) ≃ₐ[R] (C' ⧸ (m.map (algebraMap R C')) ^ (e + 1)) :=
    fun e => Ideal.quotientEquivAlgOfEq R (hCpow e)
  let L' : ∀ e, TensorProduct R O R' →ₐ[R] C' ⧸ (m.map (algebraMap R C')) ^ (e + 1) := fun e =>
    (E e).toAlgHom.comp (L e)
  have hsurj : ∀ e, Function.Surjective (L' e) := fun e => (E e).surjective.comp (hi3 e).1
  have hker : ∀ e, RingHom.ker (L' e) = (m.map (algebraMap R (TensorProduct R O R'))) ^ (e + 1) := by
    intro e
    ext t
    rw [RingHom.mem_ker, ← hTpow, ← (hi3 e).2, RingHom.mem_ker]
    exact map_eq_zero_iff (E e) (E e).injective
  let β : ∀ e, (TensorProduct R O R' ⧸ (m.map (algebraMap R (TensorProduct R O R'))) ^ (e + 1)) ≃ₐ[R]
      (C' ⧸ (m.map (algebraMap R C')) ^ (e + 1)) := fun e =>
    (Ideal.quotientEquivAlgOfEq R (hker e).symm).trans (Ideal.quotientKerAlgEquivOfSurjective (hsurj e))
  have hβmk : ∀ e t, β e (Ideal.Quotient.mk _ t) = L' e t := fun e t => rfl
  have hL : ∀ e x r y, Ideal.Quotient.mk _ y = i e x →
      L' e (x ⊗ₜ[R] r) = Ideal.Quotient.mk _ (y * algebraMap R' C' r) := by
    intro e x r y hy
    change E e (L e (x ⊗ₜ[R] r)) = _
    rw [Algebra.TensorProduct.lift_tmul, ← hy]
    change E e (Ideal.Quotient.mk _ y * Ideal.Quotient.mk _ (algebraMap R' C' r)) = _
    rw [← map_mul]
    exact Ideal.quotientEquivAlgOfEq_mk _ _ _
  have hred : ∀ n z, red (R := R) (m.map (algebraMap R C')) (Nat.le_succ (n + 1)) (β (n + 1) z) =
      β n (red (R := R) (m.map (algebraMap R (TensorProduct R O R'))) (Nat.le_succ (n + 1)) z) := by
    intro n z
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective z
    change red (R := R) (m.map (algebraMap R C')) (Nat.le_succ (n + 1)) (L' (n + 1) t) = L' n t
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x r =>
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (i (n + 1) x)
      rw [hL (n + 1) x r y hy, hL n x r y (hi1 n x y hy)]
      rfl
    | add a b ha hb => simp only [map_add, ha, hb]
  obtain ⟨Ψ, hΨ⟩ := exists_equiv _ _ β hred
  have ev : ∀ {A : Type} [CommRing A] (I : Ideal A) (x y : AdicCompletion I A),
      (∀ n, AdicCompletion.evalₐ I (n + 1) x = AdicCompletion.evalₐ I (n + 1) y) → x = y := by
    intro A _ I x y h
    refine AdicCompletion.ext_evalₐ fun n => ?_
    rw [← GlobalTheory.InvAlg.factorPow_evalₐ I (Nat.le_succ n) x, ← GlobalTheory.InvAlg.factorPow_evalₐ I (Nat.le_succ n) y, h]
  refine ⟨Ψ, fun σ y => ev _ _ _ fun n => ?_, fun e x y hy => ?_⟩
  · rw [hΨ, GlobalTheory.InvAlg.evalₐ_cmap, GlobalTheory.InvAlg.evalₐ_cmap, hΨ]
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ _ (n + 1) y)
    rw [← ht, Ideal.quotientMap_mk, hβmk, hβmk]
    clear ht
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x r =>
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (i n x)
      have h1 : (GlobalTheory.InvAlg.galTensor O σ).toRingHom (x ⊗ₜ[R] r) = x ⊗ₜ[R] σ.1 r := rfl
      rw [h1, hL n x _ y hy, hL n x r y hy, Ideal.quotientMap_mk]
      change _ = Ideal.Quotient.mk _ (act σ (y * algebraMap R' C' r))
      rw [map_mul (act σ), hact, map_mul (Ideal.Quotient.mk _), map_mul (Ideal.Quotient.mk _)]
      congr 1
      have h2 := hi2 n σ x y hy
      rw [← hy, Ideal.Quotient.eq, hCpow] at h2
      rw [Ideal.Quotient.eq, ← neg_sub]
      exact neg_mem h2
    | add a b ha hb => simp only [map_add, ha, hb]
  · rw [hΨ, AdicCompletion.evalₐ_of, hβmk, hL e x 1 y hy, map_one, _root_.mul_one]

end GlobalTheory.InvAlg.Levels
