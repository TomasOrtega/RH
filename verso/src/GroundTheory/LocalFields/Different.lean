import Mathlib
import GroundTheory.LocalFields.Monogenic
import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits
import GroundTheory.LocalFields.Unramified

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Polynomial

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

attribute [local instance high] FaithfulSMul.to_isTorsionFree

section DVR

open IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `exists_irreducible R`. Take `⟨m, u, rfl⟩` from `eq_unit_mul_pow_irreducible ha hϖ`. Establish `hm : m = n`. Rewrite `hn` using `[addVal_mul, addVal_pow, addVal_uniformizer hϖ, addVal_eq_zero_of_unit, zero_add, nsmul_eq_mul, mul_one]`. Conclude with `hn` after adjusting the coercions.

Rewrite using `[← hm, Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow, hϖ.maximalIdeal_eq]`.
-/
theorem span_singleton_eq_maximalIdeal_pow {a : R} (ha : a ≠ 0) {n : ℕ} (hn : addVal R a = n) :
    Ideal.span {a} = IsLocalRing.maximalIdeal R ^ n := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  obtain ⟨m, u, rfl⟩ := eq_unit_mul_pow_irreducible ha hϖ
  have hm : m = n := by
    rw [addVal_mul, addVal_pow, addVal_uniformizer hϖ, addVal_eq_zero_of_unit, zero_add,
      nsmul_eq_mul, mul_one] at hn
    exact_mod_cast hn
  rw [← hm, Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
    hϖ.maximalIdeal_eq]

/- English proof (translation)
The claim follows from `Ideal.prime_of_isPrime (IsDiscreteValuationRing.not_a_field R) inferInstance`.
-/
theorem prime_maximalIdeal : Prime (IsLocalRing.maximalIdeal R) :=
  Ideal.prime_of_isPrime (IsDiscreteValuationRing.not_a_field R) inferInstance

/- English proof (translation)
The claim follows from `pow_dvd_pow_iff (prime_maximalIdeal (R := R)).ne_zero (prime_maximalIdeal (R := R)).not_isUnit`.
-/
theorem maximalIdeal_pow_dvd_pow_iff {m n : ℕ} :
    IsLocalRing.maximalIdeal R ^ m ∣ IsLocalRing.maximalIdeal R ^ n ↔ m ≤ n :=
  pow_dvd_pow_iff (prime_maximalIdeal (R := R)).ne_zero (prime_maximalIdeal (R := R)).not_isUnit

/- English proof (translation)
Introduce `m n h`. Conclude with `le_antisymm (maximalIdeal_pow_dvd_pow_iff.mp (dvd_of_eq h)) (maximalIdeal_pow_dvd_pow_iff.mp (dvd_of_eq h.symm))`.
-/
theorem maximalIdeal_pow_injective :
    Function.Injective (fun n : ℕ ↦ IsLocalRing.maximalIdeal R ^ n) := by
  intro m n h
  exact le_antisymm (maximalIdeal_pow_dvd_pow_iff.mp (dvd_of_eq h))
    (maximalIdeal_pow_dvd_pow_iff.mp (dvd_of_eq h.symm))

end DVR

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]

instance isSeparable_fractionRing_integer [Algebra.IsSeparable K L] :
    Algebra.IsSeparable (FractionRing 𝒪[K]) (FractionRing 𝒪[L]) := by
  have H : RingHom.comp (algebraMap (FractionRing 𝒪[K]) (FractionRing 𝒪[L]))
      ↑(FractionRing.algEquiv 𝒪[K] K).symm.toRingEquiv =
        RingHom.comp ↑(FractionRing.algEquiv 𝒪[L] L).symm.toRingEquiv (algebraMap K L) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors 𝒪[K])
    ext
    simp only [RingHom.coe_comp, RingHom.coe_coe,
      AlgEquiv.coe_ringEquiv, Function.comp_apply, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply 𝒪[K] 𝒪[L] L, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
  exact Algebra.IsSeparable.of_equiv_equiv _ _ H

def differentExponent : ℕ := multiplicity (𝓂[L]) (differentIdeal 𝒪[K] 𝒪[L])

variable [FiniteDimensional K L]

section Separable

variable [Algebra.IsSeparable K L]

/- English proof (translation)
Take `⟨n, hn⟩` from `exists_maximalIdeal_pow_eq_of_principal 𝒪[L] (IsPrincipalIdealRing.principal _) _ (differentIdeal_ne_bot (A := 𝒪[K]) (B := 𝒪[L]))`. Rewrite using `[differentExponent, hn, multiplicity_pow_self_of_prime prime_maximalIdeal]`.
-/
theorem differentIdeal_eq_maximalIdeal_pow :
    differentIdeal 𝒪[K] 𝒪[L] = 𝓂[L] ^ differentExponent K L := by
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_eq_of_principal 𝒪[L]
    (IsPrincipalIdealRing.principal _) _ (differentIdeal_ne_bot (A := 𝒪[K]) (B := 𝒪[L]))
  rw [differentExponent, hn, multiplicity_pow_self_of_prime prime_maximalIdeal]

/- English proof (translation)
Rewrite using `[differentIdeal_eq_maximalIdeal_pow]`. Conclude with `⟨fun h ↦ by rw [h], fun h ↦ maximalIdeal_pow_injective h⟩`.
-/
theorem differentExponent_eq_iff {d : ℕ} :
    differentExponent K L = d ↔ differentIdeal 𝒪[K] 𝒪[L] = 𝓂[L] ^ d := by
  rw [differentIdeal_eq_maximalIdeal_pow]
  exact ⟨fun h ↦ by rw [h], fun h ↦ maximalIdeal_pow_injective h⟩

end Separable

variable {K L}

/- English proof (translation)
Establish `hle : ∀ z : 𝒪[L], (z : L) ∈ Algebra.adjoin K {algebraMap 𝒪[L] L x}`. Introduce `z`. Establish `hz : z ∈ Algebra.adjoin 𝒪[K] {x}` using `by rw [hx]; trivial`. Proceed by induction on `hz using Algebra.adjoin_induction with`. Consider the case `mem y hy`.

Rewrite using `[Set.mem_singleton_iff.mp hy]`. Conclude with `Algebra.subset_adjoin rfl`. Consider the case `algebraMap r`. Rewrite using `[coe_algebraMap_integer]`. Conclude with `Subalgebra.algebraMap_mem _ _`.

Consider the case `add y z _ _ hy hz`. Rewrite using `[Subring.coe_add]`. Conclude with `add_mem hy hz`. Consider the case `mul y z _ _ hy hz`. Rewrite using `[Subring.coe_mul]`.

Conclude with `mul_mem hy hz`. Use `isLocalization_integer K L` as an intermediate fact. Rewrite using `[eq_top_iff]`. Introduce `y _`. Take `⟨⟨z, s⟩, hzs⟩` from `IsLocalization.surj (Algebra.algebraMapSubmonoid 𝒪[L] (nonZeroDivisors 𝒪[K])) y`.

Take `⟨c, hc, hcs⟩` from `s.2`. Establish `hc0 : (c : K) ≠ 0`. Establish `: c ≠ 0` using `nonZeroDivisors.ne_zero hc`. Conclude with `this` after adjusting the coercions. Establish `hy : y = (c : K)⁻¹ • (z : L)`.

Establish `h2 : ((s : 𝒪[L]) : L) = algebraMap K L c`. Rewrite using `[← hcs]`. Both sides reduce to the same expression. Simplify using `only at hzs`. Rewrite using `[Algebra.smul_def, map_inv₀, ← h2, eq_inv_mul_iff_mul_eq₀]`.

Rewrite using `[mul_comm]`. Conclude with `hzs`. Rewrite using `[h2]`. Conclude with `(_root_.map_ne_zero _).mpr hc0`. Rewrite using `[hy]`.

Conclude with `Subalgebra.smul_mem _ (hle z) _`.
-/
theorem adjoin_eq_top_of_integer_adjoin_eq_top {x : 𝒪[L]} (hx : Algebra.adjoin 𝒪[K] {x} = ⊤) :
    Algebra.adjoin K {algebraMap 𝒪[L] L x} = ⊤ := by
  have hle : ∀ z : 𝒪[L], (z : L) ∈ Algebra.adjoin K {algebraMap 𝒪[L] L x} := by
    intro z
    have hz : z ∈ Algebra.adjoin 𝒪[K] {x} := by rw [hx]; trivial
    induction hz using Algebra.adjoin_induction with
    | mem y hy =>
      rw [Set.mem_singleton_iff.mp hy]
      exact Algebra.subset_adjoin rfl
    | algebraMap r =>
      rw [coe_algebraMap_integer]
      exact Subalgebra.algebraMap_mem _ _
    | add y z _ _ hy hz =>
      rw [Subring.coe_add]
      exact add_mem hy hz
    | mul y z _ _ hy hz =>
      rw [Subring.coe_mul]
      exact mul_mem hy hz
  have := isLocalization_integer K L
  rw [eq_top_iff]
  intro y _
  obtain ⟨⟨z, s⟩, hzs⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid 𝒪[L]
    (nonZeroDivisors 𝒪[K])) y
  obtain ⟨c, hc, hcs⟩ := s.2
  have hc0 : (c : K) ≠ 0 := by
    have : c ≠ 0 := nonZeroDivisors.ne_zero hc
    exact_mod_cast this
  have hy : y = (c : K)⁻¹ • (z : L) := by
    have h2 : ((s : 𝒪[L]) : L) = algebraMap K L c := by
      rw [← hcs]
      rfl
    simp only at hzs
    rw [Algebra.smul_def, map_inv₀, ← h2, eq_inv_mul_iff_mul_eq₀]
    · rw [mul_comm]; exact hzs
    · rw [h2]; exact (_root_.map_ne_zero _).mpr hc0
  rw [hy]
  exact Subalgebra.smul_mem _ (hle z) _

section Separable

variable [Algebra.IsSeparable K L]

/- English proof (translation)
Rewrite using `[← conductor_mul_differentIdeal 𝒪[K] K L x (adjoin_eq_top_of_integer_adjoin_eq_top hx), conductor_eq_top_of_adjoin_eq_top hx, Ideal.top_mul]`.
-/
theorem differentIdeal_eq_span_aeval_derivative {x : 𝒪[L]} (hx : Algebra.adjoin 𝒪[K] {x} = ⊤) :
    differentIdeal 𝒪[K] 𝒪[L] = Ideal.span {aeval x (derivative (minpoly 𝒪[K] x))} := by
  rw [← conductor_mul_differentIdeal 𝒪[K] K L x (adjoin_eq_top_of_integer_adjoin_eq_top hx),
    conductor_eq_top_of_adjoin_eq_top hx, Ideal.top_mul]

/- English proof (translation)
Introduce `h`. Use `differentIdeal_eq_span_aeval_derivative hx` as an intermediate fact. Rewrite `this` using `[h, Ideal.span_singleton_eq_bot.mpr rfl]`. Conclude with `differentIdeal_ne_bot this`.
-/
theorem aeval_derivative_ne_zero {x : 𝒪[L]} (hx : Algebra.adjoin 𝒪[K] {x} = ⊤) :
    aeval x (derivative (minpoly 𝒪[K] x)) ≠ 0 := by
  intro h
  have := differentIdeal_eq_span_aeval_derivative hx
  rw [h, Ideal.span_singleton_eq_bot.mpr rfl] at this
  exact differentIdeal_ne_bot this

/- English proof (translation)
Establish `h0` using `aeval_derivative_ne_zero hx`. Take `⟨k, hk⟩` from `exists_addVal_eq_coe h0`. Rewrite using `[hk, Nat.cast_inj, differentExponent_eq_iff, differentIdeal_eq_span_aeval_derivative hx]`. Conclude with `span_singleton_eq_maximalIdeal_pow h0 hk`.
-/
theorem differentExponent_eq_addVal {x : 𝒪[L]} (hx : Algebra.adjoin 𝒪[K] {x} = ⊤) :
    (differentExponent K L : ℕ∞) = IsDiscreteValuationRing.addVal 𝒪[L] (aeval x (derivative (minpoly 𝒪[K] x))) := by
  have h0 := aeval_derivative_ne_zero hx
  obtain ⟨k, hk⟩ := exists_addVal_eq_coe h0
  rw [hk, Nat.cast_inj, differentExponent_eq_iff, differentIdeal_eq_span_aeval_derivative hx]
  exact span_singleton_eq_maximalIdeal_pow h0 hk

variable (K L)

instance finite_quotient_maximalIdeal : Finite (𝒪[K] ⧸ 𝓂[K]) :=
  inferInstanceAs (Finite 𝓀[K])

/- English proof (translation)
Establish `h` using `pow_sub_one_dvd_differentIdeal 𝒪[K] (p := 𝓂[K]) (𝓂[L]) (ramificationIndex K L) (maximalIdeal_ne_bot K) (by rw [map_maximalIdeal])`. Rewrite `h` using `[differentIdeal_eq_maximalIdeal_pow, maximalIdeal_pow_dvd_pow_iff]`. Then use the resulting hypothesis.
-/
theorem ramificationIndex_sub_one_le_differentExponent :
    ramificationIndex K L - 1 ≤ differentExponent K L := by
  have h := pow_sub_one_dvd_differentIdeal 𝒪[K] (p := 𝓂[K]) (𝓂[L])
    (ramificationIndex K L) (maximalIdeal_ne_bot K) (by rw [map_maximalIdeal])
  rwa [differentIdeal_eq_maximalIdeal_pow, maximalIdeal_pow_dvd_pow_iff] at h

/- English proof (translation)
Rewrite using `[isUnramified_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1` using `ramificationIndex_sub_one_le_differentExponent K L`. Establish `h2` using `ramificationIndex_pos K L`.

Use linear arithmetic over natural numbers and integers. Introduce `he`. Establish `hmap : 𝓂[L] * 1 = (𝓂[K]).map (algebraMap 𝒪[K] 𝒪[L])`. Rewrite using `[map_maximalIdeal, he, pow_one, mul_one]`. Establish `hnd` using `not_dvd_differentIdeal_of_isCoprime 𝒪[K] (p := 𝓂[K]) (𝓂[L]) 1 isCoprime_one_right hmap`.

Rewrite `hnd` using `[differentIdeal_eq_maximalIdeal_pow]`. Assume the negation of the conclusion as `hd`. Conclude with `hnd (dvd_pow_self _ hd)`.
-/
theorem differentExponent_eq_zero_iff : differentExponent K L = 0 ↔ IsUnramified K L := by
  rw [isUnramified_iff]
  constructor
  · intro h
    have h1 := ramificationIndex_sub_one_le_differentExponent K L
    have h2 := ramificationIndex_pos K L
    omega
  · intro he
    have hmap : 𝓂[L] * 1 = (𝓂[K]).map (algebraMap 𝒪[K] 𝒪[L]) := by
      rw [map_maximalIdeal, he, pow_one, mul_one]
    have hnd := not_dvd_differentIdeal_of_isCoprime 𝒪[K] (p := 𝓂[K])
      (𝓂[L]) 1 isCoprime_one_right hmap
    rw [differentIdeal_eq_maximalIdeal_pow] at hnd
    by_contra hd
    exact hnd (dvd_pow_self _ hd)

end Separable

section Tower

variable (K L M : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [ValuativeExtension K L] [ValuativeExtension L M] [ValuativeExtension K M]
  [FiniteDimensional K L] [FiniteDimensional L M] [Algebra.IsSeparable K M]

/- English proof (translation)
Establish `: FiniteDimensional K M` using `Module.Finite.trans L M`. Conclude with `differentIdeal_eq_differentIdeal_mul_differentIdeal 𝒪[K] 𝒪[L] 𝒪[M]`.
-/
theorem differentIdeal_tower :
    differentIdeal 𝒪[K] 𝒪[M] =
      differentIdeal 𝒪[L] 𝒪[M] * (differentIdeal 𝒪[K] 𝒪[L]).map (algebraMap 𝒪[L] 𝒪[M]) := by
  have : FiniteDimensional K M := Module.Finite.trans L M
  exact differentIdeal_eq_differentIdeal_mul_differentIdeal 𝒪[K] 𝒪[L] 𝒪[M]

/- English proof (translation)
Establish `: FiniteDimensional K M` using `Module.Finite.trans L M`. Establish `: Algebra.IsSeparable K L` using `Algebra.isSeparable_tower_bot_of_isSeparable K L M`. Establish `: Algebra.IsSeparable L M` using `Algebra.isSeparable_tower_top_of_isSeparable K L M`. Rewrite using `[differentExponent_eq_iff, differentIdeal_tower K L M, differentIdeal_eq_maximalIdeal_pow L M, differentIdeal_eq_maximalIdeal_pow K L, Ideal.map_pow, map_maximalIdeal L M, ← pow_mul, ← pow_add]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem differentExponent_tower :
    differentExponent K M = ramificationIndex L M * differentExponent K L +
      differentExponent L M := by
  have : FiniteDimensional K M := Module.Finite.trans L M
  have : Algebra.IsSeparable K L := Algebra.isSeparable_tower_bot_of_isSeparable K L M
  have : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  rw [differentExponent_eq_iff, differentIdeal_tower K L M, differentIdeal_eq_maximalIdeal_pow L M,
    differentIdeal_eq_maximalIdeal_pow K L, Ideal.map_pow, map_maximalIdeal L M, ← pow_mul,
    ← pow_add]
  congr 1
  ring

end Tower

section Discriminant

/- English proof (translation)
Set `e : ι ≃ ι'` to `b.indexEquiv b'`. Set `b''` to `b'.reindex e.symm`. Establish `h1 : Algebra.discr A b'' = Algebra.discr A b'`. Use `Algebra.discr_reindex A b' e.symm` as an intermediate fact. Rewrite using `[Module.Basis.coe_reindex]` and apply the resulting hypothesis.

Establish `h2 : Algebra.discr A b = (b''.toMatrix b).det ^ 2 * Algebra.discr A b''`. Use `Algebra.discr_of_matrix_vecMul b'' (b''.toMatrix b)` and compare the differences between its conclusion and the goal. Rewrite using `[Module.Basis.toMatrix_map_vecMul]`. Establish `hdet : IsUnit (b''.toMatrix b).det`. Rewrite using `[← LinearMap.toMatrix_id_eq_basis_toMatrix b b'']`.

Conclude with `LinearEquiv.isUnit_det (LinearEquiv.refl A B) b b''`. Use `⟨(hdet.pow 2).unit, ?_⟩` and prove the remaining obligations. Rewrite using `[IsUnit.unit_spec, h2, h1, mul_comm]`.
-/
theorem associated_discr {A B : Type*} [CommRing A] [Nontrivial A] [CommRing B] [Algebra A B]
    {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']
    (b : Module.Basis ι A B) (b' : Module.Basis ι' A B) :
    Associated (Algebra.discr A b') (Algebra.discr A b) := by
  let e : ι ≃ ι' := b.indexEquiv b'
  let b'' := b'.reindex e.symm
  have h1 : Algebra.discr A b'' = Algebra.discr A b' := by
    have := Algebra.discr_reindex A b' e.symm
    rwa [Module.Basis.coe_reindex]
  have h2 : Algebra.discr A b = (b''.toMatrix b).det ^ 2 * Algebra.discr A b'' := by
    convert Algebra.discr_of_matrix_vecMul b'' (b''.toMatrix b)
    rw [Module.Basis.toMatrix_map_vecMul]
  have hdet : IsUnit (b''.toMatrix b).det := by
    rw [← LinearMap.toMatrix_id_eq_basis_toMatrix b b'']
    exact LinearEquiv.isUnit_det (LinearEquiv.refl A B) b b''
  refine ⟨(hdet.pow 2).unit, ?_⟩
  rw [IsUnit.unit_spec, h2, h1, mul_comm]

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[K]`. Take `⟨m, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ`. Establish `hm : m = n`. Rewrite `hn` using `[IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ, IsDiscreteValuationRing.addVal_eq_zero_of_unit, zero_add, nsmul_eq_mul, mul_one]`. Conclude with `hn` after adjusting the coercions.

Establish `hu0 : ((u : 𝒪[K]) : K) ≠ 0`. Introduce `h`. Conclude with `u.ne_zero (Subtype.ext h)`. Establish `hϖ0 : (ϖ : K) ≠ 0`. Introduce `h`.

Conclude with `hϖ.ne_zero (Subtype.ext h)`. Rewrite using `[Subring.coe_mul, Subring.coe_pow, ord_mul hu0 (pow_ne_zero _ hϖ0), ord_unit, ord_pow hϖ0, ord_uniformizer hϖ, ← hm]`. Simplify using the standard rewrite rules.
-/
theorem ord_eq_of_addVal_eq {a : 𝒪[K]} (ha : a ≠ 0) {n : ℕ}
    (hn : IsDiscreteValuationRing.addVal 𝒪[K] a = n) : ord (a : K) = n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have hm : m = n := by
    rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer hϖ,
      IsDiscreteValuationRing.addVal_eq_zero_of_unit, zero_add, nsmul_eq_mul, mul_one] at hn
    exact_mod_cast hn
  have hu0 : ((u : 𝒪[K]) : K) ≠ 0 := by
    intro h
    exact u.ne_zero (Subtype.ext h)
  have hϖ0 : (ϖ : K) ≠ 0 := by
    intro h
    exact hϖ.ne_zero (Subtype.ext h)
  rw [Subring.coe_mul, Subring.coe_pow, ord_mul hu0 (pow_ne_zero _ hϖ0), ord_unit,
    ord_pow hϖ0, ord_uniformizer hϖ, ← hm]
  simp

variable [Algebra.IsSeparable K L]

/- English proof (translation)
Distinguish the cases in `hy : y = 0`. Substitute `hy` using the available equality. Rewrite using `[Algebra.norm_zero, IsDiscreteValuationRing.addVal_zero, IsDiscreteValuationRing.addVal_zero, nsmul_eq_mul]`. Use `residueDegree_pos K L` as an intermediate fact. Rewrite using `[ENat.mul_top (by exact_mod_cast this.ne')]`.

Establish `hN : Algebra.norm 𝒪[K] y ≠ 0`. Introduce `h`. Establish `h2 : Algebra.norm K (y : L) = 0` using `by rw [← coe_norm_integer, h]; rfl`. Rewrite `h2` using `[Algebra.norm_eq_zero_iff]`. Conclude with `hy (Subtype.ext h2)`.

Take `⟨k, hk⟩` from `exists_addVal_eq_coe hN`. Take `⟨d, hd⟩` from `exists_addVal_eq_coe hy`. Establish `h1` using `ord_eq_of_addVal_eq hN hk`. Establish `h2` using `ord_eq_of_addVal_eq hy hd`. Rewrite `h1` using `[coe_norm_integer, ord_norm, h2]`.

Rewrite using `[hk, hd, nsmul_eq_mul]`. Establish `: k = residueDegree K L * d` using `by exact_mod_cast h1.symm`. Rewrite using `[this]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem addVal_norm_integer (y : 𝒪[L]) :
    IsDiscreteValuationRing.addVal 𝒪[K] (Algebra.norm 𝒪[K] y) =
      residueDegree K L • IsDiscreteValuationRing.addVal 𝒪[L] y := by
  by_cases hy : y = 0
  · subst hy
    rw [Algebra.norm_zero, IsDiscreteValuationRing.addVal_zero, IsDiscreteValuationRing.addVal_zero,
      nsmul_eq_mul]
    have := residueDegree_pos K L
    rw [ENat.mul_top (by exact_mod_cast this.ne')]
  have hN : Algebra.norm 𝒪[K] y ≠ 0 := by
    intro h
    have h2 : Algebra.norm K (y : L) = 0 := by rw [← coe_norm_integer, h]; rfl
    rw [Algebra.norm_eq_zero_iff] at h2
    exact hy (Subtype.ext h2)
  obtain ⟨k, hk⟩ := exists_addVal_eq_coe hN
  obtain ⟨d, hd⟩ := exists_addVal_eq_coe hy
  have h1 := ord_eq_of_addVal_eq hN hk
  have h2 := ord_eq_of_addVal_eq hy hd
  rw [coe_norm_integer, ord_norm, h2] at h1
  rw [hk, hd, nsmul_eq_mul]
  have : k = residueDegree K L * d := by exact_mod_cast h1.symm
  rw [this]
  push_cast
  rfl

/- English proof (translation)
Use `set pb := PowerBasis.ofAdjoinEqTop' hint hx`. Use `isLocalization_integer K L` as an intermediate fact. Set `bK : Module.Basis (Fin pb.dim) K L` to `pb.basis.localizationLocalization K (nonZeroDivisors 𝒪[K]) L`. Set `pb' : PowerBasis K L` to `{ gen := algebraMap 𝒪[L] L x dim := pb.dim basis := bK basis_eq_pow := fun i ↦ by`. Simplify using `only [bK, Module.Basis.localizationLocalization_apply, PowerBasis.coe_basis, map_pow, pb, PowerBasis.ofAdjoinEqTop'_gen] }`.

Establish `hd` using `Algebra.discr_localizationLocalization 𝒪[K] (Rₘ := K) (nonZeroDivisors 𝒪[K]) L pb.basis`. Establish `hn` using `Algebra.discr_powerBasis_eq_norm (K := K) (L := L) pb'`. Use `⟨Module.finrank K L * (Module.finrank K L - 1) / 2, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `algebraMap 𝒪[K] K _ = _`.

Rewrite using `[← hd]`. Express the relevant statement in the definitionally equal form `Algebra.discr K pb'.basis = _`. Rewrite using `[hn, Subring.coe_mul, Subring.coe_pow, coe_norm_integer]`. Use `congr 2`. Establish `hm` using `minpoly.isIntegrallyClosed_eq_field_fractions K L hint`.

Simplify using `only [pb']`. Rewrite using `[hm, derivative_map, aeval_map_algebraMap, aeval_algebraMap_apply]`. Both sides reduce to the same expression.
-/
theorem discr_powerBasis_eq_norm_integer {x : 𝒪[L]} (hint : IsIntegral 𝒪[K] x)
    (hx : Algebra.adjoin 𝒪[K] {x} = ⊤) :
    ∃ s : ℕ, Algebra.discr 𝒪[K] (PowerBasis.ofAdjoinEqTop' hint hx).basis =
      (-1) ^ s * Algebra.norm 𝒪[K] (aeval x (derivative (minpoly 𝒪[K] x))) := by
  classical
  set pb := PowerBasis.ofAdjoinEqTop' hint hx
  have := isLocalization_integer K L
  let bK : Module.Basis (Fin pb.dim) K L :=
    pb.basis.localizationLocalization K (nonZeroDivisors 𝒪[K]) L
  let pb' : PowerBasis K L :=
    { gen := algebraMap 𝒪[L] L x
      dim := pb.dim
      basis := bK
      basis_eq_pow := fun i ↦ by
        simp only [bK, Module.Basis.localizationLocalization_apply, PowerBasis.coe_basis, map_pow,
          pb, PowerBasis.ofAdjoinEqTop'_gen] }
  have hd := Algebra.discr_localizationLocalization 𝒪[K] (Rₘ := K) (nonZeroDivisors 𝒪[K]) L pb.basis
  have hn := Algebra.discr_powerBasis_eq_norm (K := K) (L := L) pb'
  refine ⟨Module.finrank K L * (Module.finrank K L - 1) / 2, ?_⟩
  apply Subtype.ext
  change algebraMap 𝒪[K] K _ = _
  rw [← hd]
  change Algebra.discr K pb'.basis = _
  rw [hn, Subring.coe_mul, Subring.coe_pow, coe_norm_integer]
  congr 2
  have hm := minpoly.isIntegrallyClosed_eq_field_fractions K L hint
  simp only [pb']
  rw [hm, derivative_map, aeval_map_algebraMap, aeval_algebraMap_apply]
  rfl

/- English proof (translation)
Take `⟨x, hx⟩` from `exists_integer_adjoin_eq_top K L`. Establish `hint : IsIntegral 𝒪[K] x` using `Algebra.IsIntegral.isIntegral x`. Rewrite using `[(IsDiscreteValuationRing.addVal_eq_iff_associated _ _).mpr (associated_discr (PowerBasis.ofAdjoinEqTop' hint hx).basis b)]`. Take `⟨s, hs⟩` from `discr_powerBasis_eq_norm_integer hint hx`. Rewrite using `[hs, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_eq_zero_iff.mpr ((isUnit_neg_one).pow s), zero_add, addVal_norm_integer, ← differentExponent_eq_addVal hx]`.

Use `push_cast`. Rewrite using `[nsmul_eq_mul]`.
-/
theorem addVal_discr {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι 𝒪[K] 𝒪[L]) :
    IsDiscreteValuationRing.addVal 𝒪[K] (Algebra.discr 𝒪[K] b) =
      (residueDegree K L * differentExponent K L : ℕ) := by
  obtain ⟨x, hx⟩ := exists_integer_adjoin_eq_top K L
  have hint : IsIntegral 𝒪[K] x := Algebra.IsIntegral.isIntegral x
  rw [(IsDiscreteValuationRing.addVal_eq_iff_associated _ _).mpr
    (associated_discr (PowerBasis.ofAdjoinEqTop' hint hx).basis b)]
  obtain ⟨s, hs⟩ := discr_powerBasis_eq_norm_integer hint hx
  rw [hs, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_eq_zero_iff.mpr
    ((isUnit_neg_one).pow s), zero_add, addVal_norm_integer, ← differentExponent_eq_addVal hx]
  push_cast
  rw [nsmul_eq_mul]

variable (K L)

end Discriminant

end GroundTheory.LocalField
