import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericFreeness
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericNoetherNormalisation
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGenericFreenessLoc
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

universe u v w

namespace GenericFreeness

/- English proof (translation)
Use `IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime R (M := M) inferInstance (motive := fun N _ _ _ ↦ ∀ (_ : Module A N) (_ : IsScalarTower A R N), IsGenericallyFree A N) ?_ ?_ ?_ ‹Module A M› ‹IsScalarTower A R M›` and prove the remaining obligations. Introduce `N _ _ _ _ _ _`. Conclude with `⟨1, one_ne_zero, inferInstance⟩`. Introduce `N _ _ _ p e _ _`. Conclude with `(hq p).of_linearEquiv (e.restrictScalars A).symm`.

Introduce `N₁ _ _ _ N₂ _ _ _ N₃ _ _ _ f g hf hg hfg h₁ h₃ _ _`. Use `letI : Module A N₁ := Module.compHom N₁ (algebraMap A R)`. Use `letI : Module A N₃ := Module.compHom N₃ (algebraMap A R)`. Establish `t₁ : IsScalarTower A R N₁` using `⟨fun a r n ↦ by show (a • r) • n = algebraMap A R a • r • n`. Rewrite using `[Algebra.smul_def, mul_smul]⟩`.

Establish `t₃ : IsScalarTower A R N₃` using `⟨fun a r n ↦ by show (a • r) • n = algebraMap A R a • r • n`. Rewrite using `[Algebra.smul_def, mul_smul]⟩`. Conclude with `IsGenericallyFree.of_exact (f.restrictScalars A) (g.restrictScalars A) hf hg hfg (h₁ inferInstance t₁) (h₃ inferInstance t₃)`.
-/
theorem isGenericallyFree_of_primes {A : Type u} [CommRing A] [IsDomain A] {R : Type u} [CommRing R]
    [IsNoetherianRing R] [Algebra A R] (hq : ∀ p : PrimeSpectrum R, IsGenericallyFree A (R ⧸ p.asIdeal))
    (M : Type w) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower A R M] [Module.Finite R M] :
    IsGenericallyFree A M := by
  refine IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime R (M := M) inferInstance
    (motive := fun N _ _ _ ↦ ∀ (_ : Module A N) (_ : IsScalarTower A R N), IsGenericallyFree A N)
    ?_ ?_ ?_ ‹Module A M› ‹IsScalarTower A R M›
  · intro N _ _ _ _ _ _
    exact ⟨1, one_ne_zero, inferInstance⟩
  · intro N _ _ _ p e _ _
    exact (hq p).of_linearEquiv (e.restrictScalars A).symm
  · intro N₁ _ _ _ N₂ _ _ _ N₃ _ _ _ f g hf hg hfg h₁ h₃ _ _
    letI : Module A N₁ := Module.compHom N₁ (algebraMap A R)
    letI : Module A N₃ := Module.compHom N₃ (algebraMap A R)
    have t₁ : IsScalarTower A R N₁ := ⟨fun a r n ↦ by
      show (a • r) • n = algebraMap A R a • r • n
      rw [Algebra.smul_def, mul_smul]⟩
    have t₃ : IsScalarTower A R N₃ := ⟨fun a r n ↦ by
      show (a • r) • n = algebraMap A R a • r • n
      rw [Algebra.smul_def, mul_smul]⟩
    exact IsGenericallyFree.of_exact (f.restrictScalars A) (g.restrictScalars A) hf hg hfg
      (h₁ inferInstance t₁) (h₃ inferInstance t₃)

/- English proof (translation)
Take `⟨a, ha, ha0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot h`. Use `isGenericallyFree_of_smul_eq_zero a ha0 fun d ↦ ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective d`. Establish `e : a • Ideal.Quotient.mk q x = Ideal.Quotient.mk q (a • x)` using `(map_smul (Ideal.Quotient.mkₐ A q) a x).symm`. Rewrite using `[e, Ideal.Quotient.eq_zero_iff_mem, smul_eq_C_mul]`.

Conclude with `q.mul_mem_right x ha`.
-/
theorem isGenericallyFree_of_comap_ne_bot {A : Type u} [CommRing A] {σ : Type*} (q : Ideal (MvPolynomial σ A))
    (h : q.comap (C : A →+* MvPolynomial σ A) ≠ ⊥) : IsGenericallyFree A (MvPolynomial σ A ⧸ q) := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  refine isGenericallyFree_of_smul_eq_zero a ha0 fun d ↦ ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective d
  have e : a • Ideal.Quotient.mk q x = Ideal.Quotient.mk q (a • x) :=
    (map_smul (Ideal.Quotient.mkₐ A q) a x).symm
  rw [e, Ideal.Quotient.eq_zero_iff_mem, smul_eq_C_mul]
  exact q.mul_mem_right x ha

/- English proof (translation)
The claim follows from `(isGenericallyFree_of_free (M := MvPolynomial σ A)).of_linearEquiv (AlgEquiv.quotientBot A (MvPolynomial σ A)).toLinearEquiv.symm`.
-/
theorem isGenericallyFree_quotient_bot {A : Type u} [CommRing A] [IsDomain A] (σ : Type*) :
    IsGenericallyFree A (MvPolynomial σ A ⧸ (⊥ : Ideal (MvPolynomial σ A))) :=
  (isGenericallyFree_of_free (M := MvPolynomial σ A)).of_linearEquiv
    (AlgEquiv.quotientBot A (MvPolynomial σ A)).toLinearEquiv.symm

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `A _ _ _ q _`. Distinguish the cases in `hc : q.comap (C : A →+* MvPolynomial (Fin 0) A) = ⊥`. Establish `hq : q = ⊥`.

Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Establish `hx' : C (coeff 0 x) ∈ q` using `by rwa [← eq_C_of_isEmpty x]`. Establish `: coeff 0 x ∈ q.comap (C : A →+* MvPolynomial (Fin 0) A)` using `hx'`. Rewrite `this` using `[hc, Ideal.mem_bot]`.

Rewrite using `[Ideal.mem_bot, eq_C_of_isEmpty x, this, map_zero]`. Substitute `hq` using the available equality. Conclude with `isGenericallyFree_quotient_bot _`. Conclude with `isGenericallyFree_of_comap_ne_bot q hc`. Consider the case `succ n ih`.

Introduce `A _ _ _ q hqp`. Distinguish the cases in `hc : q.comap (C : A →+* MvPolynomial (Fin (n + 1)) A) = ⊥`. Distinguish the cases in `hq : q = ⊥`. Substitute `hq` using the available equality. Conclude with `isGenericallyFree_quotient_bot _`.

Take `⟨a, ha, z, s, hspan⟩` from `hNN A n q hqp hq hc`. Set `D` to `MvPolynomial (Fin (n + 1)) A ⧸ q`. Set `Rn` to `MvPolynomial (Fin n) A`. Use `letI : Algebra Rn D := (aeval z : Rn →ₐ[A] D).toRingHom.toAlgebra`. Establish `: IsScalarTower A Rn D` using `IsScalarTower.of_algebraMap_eq fun x ↦ ((aeval z).commutes x).symm`.

Set `N : Submodule Rn D` to `Submodule.span Rn (s : Set D)`. Establish `hN : IsGenericallyFree A N` using `isGenericallyFree_of_primes (R := Rn) (fun p ↦ ih A p.asIdeal p.isPrime) N`. Use `hN.of_injective (N.subtype.restrictScalars A) Subtype.val_injective a ha fun d ↦ ?_` and prove the remaining obligations. Take `⟨k, c, hk⟩` from `hspan d`. Use `⟨k, ⟨⟨a ^ k • d, ?_⟩, rfl⟩⟩` and prove the remaining obligations.

Rewrite using `[hk]`. Conclude with `Submodule.sum_mem _ fun t ht ↦ Submodule.smul_mem _ (c t) (Submodule.subset_span ht)`. Conclude with `isGenericallyFree_of_comap_ne_bot q hc`.
-/
theorem isGenericallyFree_quotient (hNN : GenericNoetherNormalisation.Statement.{u}) (n : ℕ) :
    ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] (q : Ideal (MvPolynomial (Fin n) A)),
      q.IsPrime → IsGenericallyFree A (MvPolynomial (Fin n) A ⧸ q) := by
  induction n with
  | zero =>
    intro A _ _ _ q _
    by_cases hc : q.comap (C : A →+* MvPolynomial (Fin 0) A) = ⊥
    · have hq : q = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have hx' : C (coeff 0 x) ∈ q := by rwa [← eq_C_of_isEmpty x]
        have : coeff 0 x ∈ q.comap (C : A →+* MvPolynomial (Fin 0) A) := hx'
        rw [hc, Ideal.mem_bot] at this
        rw [Ideal.mem_bot, eq_C_of_isEmpty x, this, map_zero]
      subst hq
      exact isGenericallyFree_quotient_bot _
    · exact isGenericallyFree_of_comap_ne_bot q hc
  | succ n ih =>
    intro A _ _ _ q hqp
    by_cases hc : q.comap (C : A →+* MvPolynomial (Fin (n + 1)) A) = ⊥
    · by_cases hq : q = ⊥
      · subst hq
        exact isGenericallyFree_quotient_bot _
      obtain ⟨a, ha, z, s, hspan⟩ := hNN A n q hqp hq hc
      let D := MvPolynomial (Fin (n + 1)) A ⧸ q
      let Rn := MvPolynomial (Fin n) A
      letI : Algebra Rn D := (aeval z : Rn →ₐ[A] D).toRingHom.toAlgebra
      have : IsScalarTower A Rn D := IsScalarTower.of_algebraMap_eq fun x ↦ ((aeval z).commutes x).symm
      let N : Submodule Rn D := Submodule.span Rn (s : Set D)
      have hN : IsGenericallyFree A N :=
        isGenericallyFree_of_primes (R := Rn) (fun p ↦ ih A p.asIdeal p.isPrime) N
      refine hN.of_injective (N.subtype.restrictScalars A) Subtype.val_injective a ha fun d ↦ ?_
      obtain ⟨k, c, hk⟩ := hspan d
      refine ⟨k, ⟨⟨a ^ k • d, ?_⟩, rfl⟩⟩
      rw [hk]
      exact Submodule.sum_mem _ fun t ht ↦ Submodule.smul_mem _ (c t) (Submodule.subset_span ht)
    · exact isGenericallyFree_of_comap_ne_bot q hc

end GenericFreeness

/- English proof (translation)
Introduce `A _ _ _ B _ _ _ M _ _ _ _ _`. Take `⟨n, g, hg⟩` from `Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType A B›`. Use `letI : Algebra (MvPolynomial (Fin n) A) B := g.toRingHom.toAlgebra`. Use `letI : Module (MvPolynomial (Fin n) A) M := Module.compHom M (algebraMap (MvPolynomial (Fin n) A) B)`. Establish `: IsScalarTower (MvPolynomial (Fin n) A) B M` using `⟨fun x b m ↦ by show (g x * b) • m = g x • b • m`.

Rewrite using `[mul_smul]⟩`. Establish `: IsScalarTower A (MvPolynomial (Fin n) A) M` using `⟨fun a x m ↦ by show g (a • x) • m = a • g x • m`. Rewrite using `[map_smul, smul_assoc]⟩`. Establish `: Module.Finite (MvPolynomial (Fin n) A) B` using `RingHom.Finite.of_surjective g.toRingHom hg`. Establish `: Module.Finite (MvPolynomial (Fin n) A) M` using `Module.Finite.trans B M`.

Conclude with `GenericFreeness.isGenericallyFree_of_primes (R := MvPolynomial (Fin n) A) (fun p ↦ GenericFreeness.isGenericallyFree_quotient hNN n A p.asIdeal p.isPrime) M`.
-/
theorem GenericFreeness.proof (hNN : GenericNoetherNormalisation.Statement.{u}) :
    GenericFreeness.Statement.{u, v, w} := by
  intro A _ _ _ B _ _ _ M _ _ _ _ _
  obtain ⟨n, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType A B›
  letI : Algebra (MvPolynomial (Fin n) A) B := g.toRingHom.toAlgebra
  letI : Module (MvPolynomial (Fin n) A) M := Module.compHom M (algebraMap (MvPolynomial (Fin n) A) B)
  have : IsScalarTower (MvPolynomial (Fin n) A) B M := ⟨fun x b m ↦ by
    show (g x * b) • m = g x • b • m
    rw [mul_smul]⟩
  have : IsScalarTower A (MvPolynomial (Fin n) A) M := ⟨fun a x m ↦ by
    show g (a • x) • m = a • g x • m
    rw [map_smul, smul_assoc]⟩
  have : Module.Finite (MvPolynomial (Fin n) A) B := RingHom.Finite.of_surjective g.toRingHom hg
  have : Module.Finite (MvPolynomial (Fin n) A) M := Module.Finite.trans B M
  exact GenericFreeness.isGenericallyFree_of_primes (R := MvPolynomial (Fin n) A)
    (fun p ↦ GenericFreeness.isGenericallyFree_quotient hNN n A p.asIdeal p.isPrime) M

end GroundTheory.Heights₂.Heights
