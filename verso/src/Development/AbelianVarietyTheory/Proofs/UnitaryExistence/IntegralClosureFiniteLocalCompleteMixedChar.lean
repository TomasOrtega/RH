import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CohenStructureFiniteOverNormalCompleteSubring

open IsLocalRing

namespace GlobalTheory

open IsLocalRing in

/- English proof (translation)
Use `haveI : FaithfulSMul A (FractionRing S) := (faithfulSMul_iff_algebraMap_injective A _).2 (by`. Rewrite using `[IsScalarTower.algebraMap_eq A S (FractionRing S)]`. Conclude with `(IsFractionRing.injective S _).comp (FaithfulSMul.algebraMap_injective A S))`. Use `letI : Algebra (FractionRing A) (FractionRing S) := FractionRing.liftAlgebra A _`. Use `haveI := FractionRing.isScalarTower_liftAlgebra A (FractionRing S)`.

Use `haveI : CharZero (FractionRing S) := charZero_of_injective_algebraMap (IsFractionRing.injective S _)`. Use `haveI : CharZero (FractionRing A) := (algebraMap (FractionRing A) (FractionRing S)).charZero`. Use `haveI : FiniteDimensional (FractionRing A) (FractionRing S) := inferInstance`. Use `haveI : IsIntegralClosure (integralClosure S (FractionRing S)) A (FractionRing S) := by`. Use `⟨Subtype.val_injective, fun {x} => ⟨fun h => ⟨⟨x, h.tower_top⟩, rfl⟩, ?_⟩⟩` and prove the remaining obligations.

Introduce and unpack `⟨y, rfl⟩`. Conclude with `isIntegral_trans (R := A) (A := S) (y : FractionRing S) y.2`. Use `haveI : Module.Finite A (integralClosure S (FractionRing S)) := IsIntegralClosure.finite A (FractionRing A) (FractionRing S) _`. Conclude with `Module.Finite.of_restrictScalars_finite A S _`.
-/
theorem _root_.GlobalTheory.finite_normalisation_of_finite_over_normal (A S : Type) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsIntegrallyClosed A] [CommRing S] [IsDomain S] [CharZero S]
    [Algebra A S] [FaithfulSMul A S] [Module.Finite A S] :
    Module.Finite S (integralClosure S (FractionRing S)) := by
  haveI : FaithfulSMul A (FractionRing S) := (faithfulSMul_iff_algebraMap_injective A _).2 (by
    rw [IsScalarTower.algebraMap_eq A S (FractionRing S)]
    exact (IsFractionRing.injective S _).comp (FaithfulSMul.algebraMap_injective A S))
  letI : Algebra (FractionRing A) (FractionRing S) := FractionRing.liftAlgebra A _
  haveI := FractionRing.isScalarTower_liftAlgebra A (FractionRing S)
  haveI : CharZero (FractionRing S) := charZero_of_injective_algebraMap (IsFractionRing.injective S _)
  haveI : CharZero (FractionRing A) := (algebraMap (FractionRing A) (FractionRing S)).charZero
  haveI : FiniteDimensional (FractionRing A) (FractionRing S) := inferInstance
  haveI : IsIntegralClosure (integralClosure S (FractionRing S)) A (FractionRing S) := by
    refine ⟨Subtype.val_injective, fun {x} => ⟨fun h => ⟨⟨x, h.tower_top⟩, rfl⟩, ?_⟩⟩
    rintro ⟨y, rfl⟩
    exact isIntegral_trans (R := A) (A := S) (y : FractionRing S) y.2
  haveI : Module.Finite A (integralClosure S (FractionRing S)) :=
    IsIntegralClosure.finite A (FractionRing A) (FractionRing S) _
  exact Module.Finite.of_restrictScalars_finite A S _

open IsLocalRing in
/- English proof (translation)
Take `⟨k, g, hg⟩` from `Module.Finite.exists_fin (R := R) (M := M)`. Establish `hpow : ∀ n, (I ^ n • ⊤ : Submodule R R) = I ^ n` using `fun n => by`. Rewrite using `[Ideal.smul_eq_mul, Ideal.mul_top]`. Establish `key : ∀ n (x : M), x ∈ (I ^ n • ⊤ : Submodule R M) → ∃ c : Fin k → R, (∀ j, c j ∈ I ^ n) ∧ ∑ j, c j • g j = x`. Introduce `n x hx`.

Rewrite `hx` using `[← hg, Submodule.mem_ideal_smul_span_iff_exists_sum]`. Take `⟨a, ha, rfl⟩` from `hx`. Conclude with `⟨a, ha, by simp [Finsupp.sum_fintype]⟩`. Use `⟨fun {f} hf => ?_⟩` and prove the remaining obligations. Establish `hd : ∀ n, f (n + 1) - f n ∈ (I ^ n • ⊤ : Submodule R M)` using `fun n => by`.

Use `(hf (Nat.le_succ n))` as an intermediate fact. Rewrite `this` using `[SModEq.sub_mem]`. Simplify using `using neg_mem this`. Use `choose c hcI hcsum using fun n => key n _ (hd n)`. Establish `hs : ∀ j, ∃ a : R, ∀ n, (∑ i ∈ Finset.range n, c i j) ≡ a [SMOD (I ^ n • ⊤ : Submodule R R)]`.

Introduce `j`. Use `hR.prec' _ fun {m n} hmn => ?_` and prove the remaining obligations. Rewrite using `[SModEq.sub_mem, hpow]`. Establish `: ∑ i ∈ Finset.range m, c i j - ∑ i ∈ Finset.range n, c i j = -∑ i ∈ Finset.Ico m n, c i j`. Rewrite using `[← Finset.sum_range_add_sum_Ico _ hmn]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `neg_mem (Ideal.sum_mem _ fun i hi => Ideal.pow_le_pow_right (Finset.mem_Ico.1 hi).1 (hcI i j))`. Use `choose a ha using hs`. Use `⟨f 0 + ∑ j, a j • g j, fun n => ?_⟩` and prove the remaining obligations.

Establish `hfn : f n = f 0 + ∑ j, (∑ i ∈ Finset.range n, c i j) • g j`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Simplify using `only [Finset.sum_range_succ, add_smul, Finset.sum_add_distrib, hcsum n]`.

Rewrite using `[← add_assoc, ← ih]`. Normalize the expressions using the abelian group laws. Rewrite using `[SModEq.sub_mem, hfn, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← sub_smul]`.

Use `(SModEq.sub_mem.1 (ha j n))` as an intermediate fact. Rewrite `this` using `[hpow]`. Conclude with `Submodule.smul_mem_smul this Submodule.mem_top`.
-/
private theorem isPrecomplete_of_finite_module {R M : Type*} [CommRing R] {I : Ideal R} [hR : IsPrecomplete I R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] : IsPrecomplete I M := by
  obtain ⟨k, g, hg⟩ := Module.Finite.exists_fin (R := R) (M := M)
  have hpow : ∀ n, (I ^ n • ⊤ : Submodule R R) = I ^ n := fun n => by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  have key : ∀ n (x : M), x ∈ (I ^ n • ⊤ : Submodule R M) →
      ∃ c : Fin k → R, (∀ j, c j ∈ I ^ n) ∧ ∑ j, c j • g j = x := by
    intro n x hx
    rw [← hg, Submodule.mem_ideal_smul_span_iff_exists_sum] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨a, ha, by simp [Finsupp.sum_fintype]⟩
  refine ⟨fun {f} hf => ?_⟩
  have hd : ∀ n, f (n + 1) - f n ∈ (I ^ n • ⊤ : Submodule R M) := fun n => by
    have := (hf (Nat.le_succ n))
    rw [SModEq.sub_mem] at this
    simpa using neg_mem this
  choose c hcI hcsum using fun n => key n _ (hd n)
  have hs : ∀ j, ∃ a : R, ∀ n, (∑ i ∈ Finset.range n, c i j) ≡ a [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    intro j
    refine hR.prec' _ fun {m n} hmn => ?_
    rw [SModEq.sub_mem, hpow]
    have : ∑ i ∈ Finset.range m, c i j - ∑ i ∈ Finset.range n, c i j =
        -∑ i ∈ Finset.Ico m n, c i j := by
      rw [← Finset.sum_range_add_sum_Ico _ hmn]; ring
    rw [this]
    exact neg_mem (Ideal.sum_mem _ fun i hi =>
      Ideal.pow_le_pow_right (Finset.mem_Ico.1 hi).1 (hcI i j))
  choose a ha using hs
  refine ⟨f 0 + ∑ j, a j • g j, fun n => ?_⟩
  have hfn : f n = f 0 + ∑ j, (∑ i ∈ Finset.range n, c i j) • g j := by
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [Finset.sum_range_succ, add_smul, Finset.sum_add_distrib, hcsum n]
      rw [← add_assoc, ← ih]
      abel
  rw [SModEq.sub_mem, hfn, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [← sub_smul]
  have := (SModEq.sub_mem.1 (ha j n))
  rw [hpow] at this
  exact Submodule.smul_mem_smul this Submodule.mem_top

open IsLocalRing in
open Polynomial in
/- English proof (translation)
Use `set I : Ideal C := (maximalIdeal S).map (algebraMap S C) with hI`. Use `haveI : IsPrecomplete (maximalIdeal S) C := isPrecomplete_of_finite_module`. Use `haveI : IsAdicComplete (maximalIdeal S) C := {}`. Use `haveI : IsAdicComplete I C := (IsAdicComplete.map_algebraMap_iff _ _).2 inferInstance`. Establish `hIM : ∀ M : Ideal C, M.IsMaximal → I ≤ M`.

Introduce `M hM`. Rewrite using `[hI, Ideal.map_le_iff_le_comap]`. Conclude with `(IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := S) M)).ge`. Use `haveI : IsArtinianRing (C ⧸ I) := by`. Use `letI := Ideal.Quotient.field (maximalIdeal S)`.

Use `haveI : Module.Finite (S ⧸ maximalIdeal S) (C ⧸ I) := Module.Finite.of_restrictScalars_finite S _ _`. Conclude with `IsArtinianRing.of_finite (S ⧸ maximalIdeal S) _`. Use `IsLocalRing.of_unique_max_ideal ?_` and prove the remaining obligations. Take `⟨M₁, hM₁⟩` from `Ideal.exists_maximal C`. Use `⟨M₁, hM₁, fun M₂ hM₂ => ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hne`. Take `⟨x, hx₂, hx₁⟩ : ∃ x ∈ M₂, x ∉ M₁` from `by by_contra! h`. Conclude with `hne (hM₂.eq_of_le hM₁.ne_top h)`. Use `set u := Ideal.Quotient.mk I x with hu`. Take `⟨N, hN⟩` from `IsArtinian.monotone_stabilizes (R := C ⧸ I) (M := C ⧸ I) ⟨fun n => OrderDual.toDual (Ideal.span {u ^ n}), fun a b hab => Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow u hab)⟩`.

Use `set m := N + 1 with hmdef`. Establish `hm : u ^ m ∈ Ideal.span {u ^ (m + 1)}`. Establish `h₁` using `hN m (by omega)`. Establish `h₂` using `hN (m + 1) (by omega)`. Establish `: Ideal.span {u ^ m} = Ideal.span {u ^ (m + 1)}`.

Conclude with `congrArg OrderDual.ofDual (h₁.symm.trans h₂)`. Rewrite using `[← this]`. Conclude with `Ideal.mem_span_singleton_self _`. Take `⟨v, hv⟩` from `Ideal.mem_span_singleton'.1 hm`. Establish `hpow : ∀ j, u ^ m = u ^ (m + j) * v ^ j`.

Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih`. Rewrite using `[ih, pow_add u m j, ← hv]`.

Expand and normalize the polynomial expressions, which then agree. Establish `he : (u ^ m * v ^ m) * (u ^ m * v ^ m) = u ^ m * v ^ m`. Combine the equalities or inequalities in the displayed calculation. Establish `hue : u ^ m = u ^ m * (u ^ m * v ^ m)`. Combine the equalities or inequalities in the displayed calculation.

Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective v`. Use `set a₀ := x ^ m * y ^ m with ha₀def`. Establish `hmk : Ideal.Quotient.mk I a₀ = u ^ m * Ideal.Quotient.mk I y ^ m`. Simplify using `[ha₀def, hu]`. Establish `hmon : (X ^ 2 - X : C[X]).Monic` using `by monicity!`.

Establish `heval : (X ^ 2 - X : C[X]).eval a₀ ∈ I`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Simplify using `only [eval_sub, eval_pow, eval_X, map_sub, map_pow, hmk]`. Rewrite using `[sq, he, sub_self]`. Establish `hder : (derivative (X ^ 2 - X : C[X])).eval a₀ = 2 * a₀ - 1`.

Simplify using `only [derivative_sub, derivative_X_pow, derivative_X, eval_sub, eval_mul, eval_C, eval_pow, eval_X, eval_one]`. Evaluate the numerical expressions. Establish `hunit : IsUnit (Ideal.Quotient.mk I ((derivative (X ^ 2 - X : C[X])).eval a₀))`. Rewrite using `[hder, map_sub, map_mul, hmk, map_one, map_ofNat]`. Conclude with `(Units.mkOfMulEqOne _ (2 * (u ^ m * Ideal.Quotient.mk I y ^ m) - 1) (by linear_combination 4 * he)).isUnit`.

Take `⟨a, ha, haa₀⟩` from `HenselianRing.is_henselian (I := I) _ hmon a₀ heval hunit`. Establish `ha' : a * (a - 1) = 0`. Establish `: a ^ 2 - a = 0` using `by simpa using ha`. Take the linear combination `this`. Establish `hx₂m : a₀ ∈ M₂` using `M₂.mul_mem_right _ (M₂.pow_mem_of_mem hx₂ m (by omega))`.

Break down `mul_eq_zero.1 ha' with h0 | h1` into its components or cases. Substitute `h0` using the available equality. Establish `ha₀I : a₀ ∈ I` using `by simpa using neg_mem haa₀`. Establish `hxm : x ^ m - x ^ m * a₀ ∈ I`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hmk, map_pow, ← hu, ← hue, sub_self]`.

Establish `: x ^ m ∈ M₁`. Establish `h` using `hIM M₁ hM₁ hxm`. Establish `h'` using `M₁.mul_mem_left (x ^ m) (hIM M₁ hM₁ ha₀I)`. Simplify using `using M₁.add_mem h h'`. Conclude with `hx₁ (hM₁.isPrime.mem_of_pow_mem m this)`.

Establish `h1' : a = 1` using `sub_eq_zero.1 h1`. Substitute `h1'` using the available equality. Establish `: (1 : C) ∈ M₂`. Establish `h` using `hIM M₂ hM₂ haa₀`. Simplify using `using M₂.add_mem h hx₂m`.

Conclude with `hM₂.ne_top ((Ideal.eq_top_iff_one _).2 this)`.
-/
private theorem isLocalRing_of_finite_domain_over_complete (S C : Type) [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    [IsAdicComplete (maximalIdeal S) S] [CommRing C] [IsDomain C] [Algebra S C]
    [Module.Finite S C] : IsLocalRing C := by
  set I : Ideal C := (maximalIdeal S).map (algebraMap S C) with hI
  haveI : IsPrecomplete (maximalIdeal S) C := isPrecomplete_of_finite_module
  haveI : IsAdicComplete (maximalIdeal S) C := {}
  haveI : IsAdicComplete I C := (IsAdicComplete.map_algebraMap_iff _ _).2 inferInstance
  have hIM : ∀ M : Ideal C, M.IsMaximal → I ≤ M := by
    intro M hM
    rw [hI, Ideal.map_le_iff_le_comap]
    exact (IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := S) M)).ge
  haveI : IsArtinianRing (C ⧸ I) := by
    letI := Ideal.Quotient.field (maximalIdeal S)
    haveI : Module.Finite (S ⧸ maximalIdeal S) (C ⧸ I) :=
      Module.Finite.of_restrictScalars_finite S _ _
    exact IsArtinianRing.of_finite (S ⧸ maximalIdeal S) _
  refine IsLocalRing.of_unique_max_ideal ?_
  obtain ⟨M₁, hM₁⟩ := Ideal.exists_maximal C
  refine ⟨M₁, hM₁, fun M₂ hM₂ => ?_⟩
  by_contra hne
  obtain ⟨x, hx₂, hx₁⟩ : ∃ x ∈ M₂, x ∉ M₁ := by
    by_contra! h
    exact hne (hM₂.eq_of_le hM₁.ne_top h)
  set u := Ideal.Quotient.mk I x with hu
  obtain ⟨N, hN⟩ := IsArtinian.monotone_stabilizes (R := C ⧸ I) (M := C ⧸ I)
    ⟨fun n => OrderDual.toDual (Ideal.span {u ^ n}),
      fun a b hab => Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow u hab)⟩
  set m := N + 1 with hmdef
  have hm : u ^ m ∈ Ideal.span {u ^ (m + 1)} := by
    have h₁ := hN m (by omega)
    have h₂ := hN (m + 1) (by omega)
    have : Ideal.span {u ^ m} = Ideal.span {u ^ (m + 1)} := by
      exact congrArg OrderDual.ofDual (h₁.symm.trans h₂)
    rw [← this]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 hm
  have hpow : ∀ j, u ^ m = u ^ (m + j) * v ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [ih, pow_add u m j, ← hv]
      ring
  have he : (u ^ m * v ^ m) * (u ^ m * v ^ m) = u ^ m * v ^ m := by
    calc (u ^ m * v ^ m) * (u ^ m * v ^ m) = (u ^ (m + m) * v ^ m) * v ^ m := by ring
      _ = u ^ m * v ^ m := by rw [← hpow m]
  have hue : u ^ m = u ^ m * (u ^ m * v ^ m) := by
    calc u ^ m = u ^ (m + m) * v ^ m := hpow m
      _ = u ^ m * (u ^ m * v ^ m) := by ring
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective v
  set a₀ := x ^ m * y ^ m with ha₀def
  have hmk : Ideal.Quotient.mk I a₀ = u ^ m * Ideal.Quotient.mk I y ^ m := by
    simp [ha₀def, hu]
  have hmon : (X ^ 2 - X : C[X]).Monic := by monicity!
  have heval : (X ^ 2 - X : C[X]).eval a₀ ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp only [eval_sub, eval_pow, eval_X, map_sub, map_pow, hmk]
    rw [sq, he, sub_self]
  have hder : (derivative (X ^ 2 - X : C[X])).eval a₀ = 2 * a₀ - 1 := by
    simp only [derivative_sub, derivative_X_pow, derivative_X, eval_sub, eval_mul, eval_C,
      eval_pow, eval_X, eval_one]
    norm_num
  have hunit : IsUnit (Ideal.Quotient.mk I ((derivative (X ^ 2 - X : C[X])).eval a₀)) := by
    rw [hder, map_sub, map_mul, hmk, map_one, map_ofNat]
    exact (Units.mkOfMulEqOne _ (2 * (u ^ m * Ideal.Quotient.mk I y ^ m) - 1)
      (by linear_combination 4 * he)).isUnit
  obtain ⟨a, ha, haa₀⟩ := HenselianRing.is_henselian (I := I) _ hmon a₀ heval hunit
  have ha' : a * (a - 1) = 0 := by
    have : a ^ 2 - a = 0 := by simpa using ha
    linear_combination this
  have hx₂m : a₀ ∈ M₂ := M₂.mul_mem_right _ (M₂.pow_mem_of_mem hx₂ m (by omega))
  rcases mul_eq_zero.1 ha' with h0 | h1
  · subst h0
    have ha₀I : a₀ ∈ I := by simpa using neg_mem haa₀
    have hxm : x ^ m - x ^ m * a₀ ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hmk, map_pow, ← hu, ← hue,
        sub_self]
    have : x ^ m ∈ M₁ := by
      have h := hIM M₁ hM₁ hxm
      have h' := M₁.mul_mem_left (x ^ m) (hIM M₁ hM₁ ha₀I)
      simpa using M₁.add_mem h h'
    exact hx₁ (hM₁.isPrime.mem_of_pow_mem m this)
  · have h1' : a = 1 := sub_eq_zero.1 h1
    subst h1'
    have : (1 : C) ∈ M₂ := by
      have h := hIM M₂ hM₂ haa₀
      simpa using M₂.add_mem h hx₂m
    exact hM₂.ne_top ((Ideal.eq_top_iff_one _).2 this)

open IsLocalRing in
/- English proof (translation)
Introduce `S _ _ _ _ p hp hpm hS hSc`. Take `⟨A, _, _, _, i, hi, hfin, hAn, hAic, hAc⟩` from `_root_.GlobalTheory.CohenStructure.exists_finite_injective_of_isAdicComplete S p hp hpm hS hSc`. Use `letI : Algebra A S := i.toAlgebra`. Use `haveI : FaithfulSMul A S := (faithfulSMul_iff_algebraMap_injective A S).2 hi`. Use `haveI : Module.Finite A S := hfin`.

Use `haveI := hAn`. Use `haveI := hAic`. Use `haveI := hS`. Use `haveI := hSc`. Use `haveI hC : Module.Finite S (integralClosure S (FractionRing S)) := _root_.GlobalTheory.finite_normalisation_of_finite_over_normal A S`.

Use `haveI : IsLocalRing (integralClosure S (FractionRing S)) := isLocalRing_of_finite_domain_over_complete S _`. Use `haveI : IsNoetherianRing (integralClosure S (FractionRing S)) := isNoetherian_of_tower S inferInstance`. Conclude with `⟨hC, inferInstance, inferInstance, _root_.GlobalTheory.FormalIsogeny.isAdicComplete_maximalIdeal_of_finite S _⟩`.
-/
theorem _root_.GlobalTheory.normalisation_finite_local_complete_of_mixedChar :
    ∀ (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S] [CharZero S] (p : ℕ), p.Prime →
      (p : S) ∈ maximalIdeal S → IsNoetherianRing S → IsAdicComplete (maximalIdeal S) S →
      Module.Finite S (integralClosure S (FractionRing S)) ∧
        ∃ _ : IsLocalRing (integralClosure S (FractionRing S)),
          IsNoetherianRing (integralClosure S (FractionRing S)) ∧
          IsAdicComplete (maximalIdeal (integralClosure S (FractionRing S)))
            (integralClosure S (FractionRing S)) := by
  intro S _ _ _ _ p hp hpm hS hSc
  obtain ⟨A, _, _, _, i, hi, hfin, hAn, hAic, hAc⟩ :=
    _root_.GlobalTheory.CohenStructure.exists_finite_injective_of_isAdicComplete S p hp hpm hS hSc
  letI : Algebra A S := i.toAlgebra
  haveI : FaithfulSMul A S := (faithfulSMul_iff_algebraMap_injective A S).2 hi
  haveI : Module.Finite A S := hfin
  haveI := hAn
  haveI := hAic
  haveI := hS
  haveI := hSc
  haveI hC : Module.Finite S (integralClosure S (FractionRing S)) := _root_.GlobalTheory.finite_normalisation_of_finite_over_normal A S
  haveI : IsLocalRing (integralClosure S (FractionRing S)) := isLocalRing_of_finite_domain_over_complete S _
  haveI : IsNoetherianRing (integralClosure S (FractionRing S)) := isNoetherian_of_tower S inferInstance
  exact ⟨hC, inferInstance, inferInstance,
    _root_.GlobalTheory.FormalIsogeny.isAdicComplete_maximalIdeal_of_finite S _⟩

end GlobalTheory
