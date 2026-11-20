import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.C1FieldNormSurjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TsenLangRatFunc
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.C1FiniteExtensionLang

open Polynomial

namespace GlobalTheory

/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap k[X] A)` using `FaithfulSMul.algebraMap_injective k[X] A`. Establish `hle : Algebra.algebraMapSubmonoid A (nonZeroDivisors k[X]) ≤ nonZeroDivisors A`. Introduce and unpack `_ ⟨p, hp, rfl⟩`. Conclude with `mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero hp))`. Use `{ map_units := fun y => IsLocalization.map_units (FractionRing A) ⟨y.1, hle y.2⟩ surj := fun z => ?_ exists_of_eq := fun {x y} hxy => ⟨1, by rw [IsFractionRing.injective A (FractionRing A) hxy]⟩ }` and prove the remaining obligations.

Take `⟨⟨a, b⟩, hab⟩` from `IsLocalization.surj (nonZeroDivisors A) z`. Establish `hb0 : (b : A) ≠ 0` using `nonZeroDivisors.ne_zero b.2`. Establish `hne` using `Ideal.comap_ne_bot_of_integral_mem (R := k[X]) hb0 (Ideal.mem_span_singleton_self (b : A)) (Algebra.IsIntegral.isIntegral _)`. Take `⟨p, hpI, hp0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.mp hpI`.

Use `⟨⟨c * a, ⟨_, ⟨p, mem_nonZeroDivisors_of_ne_zero hp0, rfl⟩⟩⟩, ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[← hc, map_mul, map_mul, ← hab]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isLocalization_fractionRing_of_finite_polynomial (k A : Type) [Field k] [CommRing A] [IsDomain A]
    [Algebra k[X] A] [Module.Finite k[X] A] [FaithfulSMul k[X] A] :
    IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors k[X])) (FractionRing A) := by
  have hinj : Function.Injective (algebraMap k[X] A) := FaithfulSMul.algebraMap_injective k[X] A
  have hle : Algebra.algebraMapSubmonoid A (nonZeroDivisors k[X]) ≤ nonZeroDivisors A := by
    rintro _ ⟨p, hp, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero hp))
  refine
    { map_units := fun y => IsLocalization.map_units (FractionRing A) ⟨y.1, hle y.2⟩
      surj := fun z => ?_
      exists_of_eq := fun {x y} hxy => ⟨1, by rw [IsFractionRing.injective A (FractionRing A) hxy]⟩ }
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors A) z
  have hb0 : (b : A) ≠ 0 := nonZeroDivisors.ne_zero b.2
  have hne := Ideal.comap_ne_bot_of_integral_mem (R := k[X]) hb0 (Ideal.mem_span_singleton_self (b : A))
    (Algebra.IsIntegral.isIntegral _)
  obtain ⟨p, hpI, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hpI
  refine ⟨⟨c * a, ⟨_, ⟨p, mem_nonZeroDivisors_of_ne_zero hp0, rfl⟩⟩⟩, ?_⟩
  simp only
  rw [← hc, map_mul, map_mul, ← hab]
  ring

end GlobalTheory

namespace GlobalTheory

/- English proof (translation)
Introduce `k A _ _ _ _ _ _ _ _ _ N hN`. Establish `: FaithfulSMul k[X] A` using `inferInstance`. Establish `hinjA : Function.Injective (algebraMap k[X] A)` using `FaithfulSMul.algebraMap_injective k[X] A`. Use `set L := FractionRing A`. Establish `hinjL : Function.Injective (algebraMap k[X] L)`.

Rewrite using `[IsScalarTower.algebraMap_eq k[X] A L]`. Conclude with `(IsFractionRing.injective A L).comp hinjA`. Establish `: FaithfulSMul k[X] L` using `(faithfulSMul_iff_algebraMap_injective _ _).mpr hinjL`. Use `letI : Algebra (RatFunc k) L := RatFunc.liftAlgebra k L`. Establish `: IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors k[X])) L` using `isLocalization_fractionRing_of_finite_polynomial k A`.

Establish `: Module.Finite (RatFunc k) L` using `Module.Finite.of_isLocalization k[X] A (Rₚ := RatFunc k) (Sₚ := L) (nonZeroDivisors k[X])`. Establish `hC1 : GlobalTheory.NeedB.IsFirstChernClassOfLineBundle (RatFunc k)` using `GlobalTheory.is_c1_of_finite_of_tsen_lang_systems (RatFunc k) (RatFunc k) (GlobalTheory.tsenLang_ratFunc k)`. Take `⟨h, hh⟩` from `GlobalTheory.norm_surjective_of_is_c1 (RatFunc k) L hC1 RatFunc.X RatFunc.X_ne_zero`. Take `⟨⟨x, ⟨_, ⟨m, hm0, rfl⟩⟩⟩, hx⟩` from `IsLocalization.surj (Algebra.algebraMapSubmonoid A (nonZeroDivisors k[X])) h`. Establish `hm0' : m ≠ 0` using `nonZeroDivisors.ne_zero hm0`.

Take `⟨M, rfl⟩ : ∃ M, N = M + 1` from `⟨N - 1, by omega⟩`. Use `set g : A := x * algebraMap k[X] A (m ^ M) with hg`. Establish `hgL : algebraMap A L g = h * algebraMap (RatFunc k) L (algebraMap k[X] (RatFunc k) (m ^ (M + 1)))`. Simplify using `only at hx`. Rewrite using `[hg, map_mul, ← hx, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, pow_succ, map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hnorm : Algebra.norm k[X] g = X * (m ^ (M + 1)) ^ Module.finrank (RatFunc k) L`. Apply `IsFractionRing.injective k[X] (RatFunc k)` to reduce the goal to its premises. Rewrite using `[← Algebra.norm_localization k[X] (Rₘ := RatFunc k) (Sₘ := L) (nonZeroDivisors k[X]) g, hgL, map_mul, hh, Algebra.norm_algebraMap, map_mul, RatFunc.algebraMap_X, ← map_pow]`. Establish `hp : (m ^ (M + 1)) ^ Module.finrank (RatFunc k) L ≠ 0` using `pow_ne_zero _ (pow_ne_zero _ hm0')`.

Establish `hg0 : g ≠ 0`. Introduce `h0`. Rewrite `hnorm` using `[h0, Algebra.norm_zero]`. Conclude with `mul_ne_zero X_ne_zero hp hnorm.symm`. Use `⟨g, hg0, ?_⟩` and prove the remaining obligations.

Rewrite using `[finrank_quotient_span_eq_natDegree_norm (Module.Free.chooseBasis k[X] A) hg0, hnorm, natDegree_mul X_ne_zero hp, natDegree_X, natDegree_pow, natDegree_pow, mul_left_comm, Nat.add_mul_mod_self_left]`.
-/
theorem exists_finrank_quotient_span_mod_eq_one :
    ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra k[X] A]
      [IsScalarTower k k[X] A] [Module.Finite k[X] A] [Module.Free k[X] A] (N : ℕ), 1 ≤ N →
      ∃ f : A, f ≠ 0 ∧ Module.finrank k (A ⧸ Ideal.span {f}) % N = 1 % N := by
  intro k A _ _ _ _ _ _ _ _ _ N hN
  have : FaithfulSMul k[X] A := inferInstance
  have hinjA : Function.Injective (algebraMap k[X] A) := FaithfulSMul.algebraMap_injective k[X] A
  set L := FractionRing A
  have hinjL : Function.Injective (algebraMap k[X] L) := by
    rw [IsScalarTower.algebraMap_eq k[X] A L]
    exact (IsFractionRing.injective A L).comp hinjA
  have : FaithfulSMul k[X] L := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinjL
  letI : Algebra (RatFunc k) L := RatFunc.liftAlgebra k L
  have : IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors k[X])) L :=
    isLocalization_fractionRing_of_finite_polynomial k A
  have : Module.Finite (RatFunc k) L :=
    Module.Finite.of_isLocalization k[X] A (Rₚ := RatFunc k) (Sₚ := L) (nonZeroDivisors k[X])
  have hC1 : GlobalTheory.NeedB.IsFirstChernClassOfLineBundle (RatFunc k) :=
    GlobalTheory.is_c1_of_finite_of_tsen_lang_systems (RatFunc k) (RatFunc k) (GlobalTheory.tsenLang_ratFunc k)
  obtain ⟨h, hh⟩ := GlobalTheory.norm_surjective_of_is_c1 (RatFunc k) L hC1 RatFunc.X RatFunc.X_ne_zero
  obtain ⟨⟨x, ⟨_, ⟨m, hm0, rfl⟩⟩⟩, hx⟩ :=
    IsLocalization.surj (Algebra.algebraMapSubmonoid A (nonZeroDivisors k[X])) h
  have hm0' : m ≠ 0 := nonZeroDivisors.ne_zero hm0
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  set g : A := x * algebraMap k[X] A (m ^ M) with hg
  have hgL : algebraMap A L g
      = h * algebraMap (RatFunc k) L (algebraMap k[X] (RatFunc k) (m ^ (M + 1))) := by
    simp only at hx
    rw [hg, map_mul, ← hx, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply, pow_succ, map_mul]
    ring
  have hnorm : Algebra.norm k[X] g = X * (m ^ (M + 1)) ^ Module.finrank (RatFunc k) L := by
    apply IsFractionRing.injective k[X] (RatFunc k)
    rw [← Algebra.norm_localization k[X] (Rₘ := RatFunc k) (Sₘ := L) (nonZeroDivisors k[X]) g, hgL, map_mul, hh,
      Algebra.norm_algebraMap, map_mul, RatFunc.algebraMap_X, ← map_pow]
  have hp : (m ^ (M + 1)) ^ Module.finrank (RatFunc k) L ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hm0')
  have hg0 : g ≠ 0 := by
    intro h0
    rw [h0, Algebra.norm_zero] at hnorm
    exact mul_ne_zero X_ne_zero hp hnorm.symm
  refine ⟨g, hg0, ?_⟩
  rw [finrank_quotient_span_eq_natDegree_norm (Module.Free.chooseBasis k[X] A) hg0, hnorm,
    natDegree_mul X_ne_zero hp, natDegree_X, natDegree_pow, natDegree_pow, mul_left_comm,
    Nat.add_mul_mod_self_left]

end GlobalTheory
