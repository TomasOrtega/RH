import Formalism.PadicSubsetSums.CentralIdempotents.CentralIdempotentIntegral

namespace Formalism.IrreducibleCountingLemmas.TW

/- English proof (translation)
Introduce `O O' _ _ _ _ _ _ _ ϖ ϖ' u e hϖ hϖ' hmap he X _ _ _`. Establish `hne : algebraMap O O' ϖ ≠ 0`. Rewrite using `[hmap]`. Conclude with `mul_ne_zero u.ne_zero (pow_ne_zero _ hϖ'.ne_zero)`. Establish `hinj : Function.Injective (algebraMap O O')`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Assume the negation of the conclusion as `hx0`. Take `⟨k, v, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ`. Rewrite `hx` using `[map_mul, map_pow]`.

Break down `mul_eq_zero.mp hx with h | h` into its components or cases. Conclude with `((v.isUnit.map (algebraMap O O')).ne_zero) h`. Conclude with `pow_ne_zero k hne h`. Establish `hloc : IsLocalHom (algebraMap O O')`. Use `⟨fun x hx => ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hnu`. Establish `hmem : x ∈ IsLocalRing.maximalIdeal O` using `(IsLocalRing.mem_maximalIdeal x).mpr hnu`. Rewrite `hmem` using `[hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]`. Take `⟨y, rfl⟩` from `hmem`. Rewrite `hx` using `[map_mul]`.

Establish `h1 : IsUnit (algebraMap O O' ϖ)` using `isUnit_of_mul_isUnit_left hx`. Rewrite `h1` using `[hmap]`. Establish `h2 : IsUnit (ϖ' ^ e)` using `isUnit_of_mul_isUnit_right h1`. Conclude with `hϖ'.not_isUnit ((isUnit_pow_iff he.ne').mp h2)`. Establish `: FaithfulSMul O O'` using `(faithfulSMul_iff_algebraMap_injective O O').mpr hinj`.

Establish `: Module.IsTorsionFree O O'` using `inferInstance`. Establish `: Module.Flat O O'` using `inferInstance`. Rewrite using `[IsLocalRing.length_baseChange O O' X, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, hmap]`. Establish `hord : Module.length O' (O' ⧸ Ideal.span {(u : O') * ϖ' ^ e}) = (e : ℕ∞)`. Express the relevant statement in the definitionally equal form `Ring.ord O' ((u : O') * ϖ' ^ e) = _`.

Rewrite using `[Ring.ord_mul_of_isUnit_left u.isUnit, Ring.ord_pow (mem_nonZeroDivisors_of_ne_zero hϖ'.ne_zero), Ring.ord_of_irreducible hϖ']`. Simplify using the standard rewrite rules. Rewrite using `[hord, mul_comm]`.
-/
theorem length_base_change_dvr : LengthBaseChange := by
  intro O O' _ _ _ _ _ _ _ ϖ ϖ' u e hϖ hϖ' hmap he X _ _ _

  have hne : algebraMap O O' ϖ ≠ 0 := by
    rw [hmap]
    exact mul_ne_zero u.ne_zero (pow_ne_zero _ hϖ'.ne_zero)

  have hinj : Function.Injective (algebraMap O O') := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    obtain ⟨k, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
    rw [map_mul, map_pow] at hx
    rcases mul_eq_zero.mp hx with h | h
    · exact ((v.isUnit.map (algebraMap O O')).ne_zero) h
    · exact pow_ne_zero k hne h

  have hloc : IsLocalHom (algebraMap O O') := by
    refine ⟨fun x hx => ?_⟩
    by_contra hnu
    have hmem : x ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal x).mpr hnu
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
    obtain ⟨y, rfl⟩ := hmem
    rw [map_mul] at hx
    have h1 : IsUnit (algebraMap O O' ϖ) := isUnit_of_mul_isUnit_left hx
    rw [hmap] at h1
    have h2 : IsUnit (ϖ' ^ e) := isUnit_of_mul_isUnit_right h1
    exact hϖ'.not_isUnit ((isUnit_pow_iff he.ne').mp h2)
  have : FaithfulSMul O O' := (faithfulSMul_iff_algebraMap_injective O O').mpr hinj
  have : Module.IsTorsionFree O O' := inferInstance
  have : Module.Flat O O' := inferInstance
  rw [IsLocalRing.length_baseChange O O' X, hϖ.maximalIdeal_eq, Ideal.map_span,
    Set.image_singleton, hmap]
  have hord : Module.length O' (O' ⧸ Ideal.span {(u : O') * ϖ' ^ e}) = (e : ℕ∞) := by
    change Ring.ord O' ((u : O') * ϖ' ^ e) = _
    rw [Ring.ord_mul_of_isUnit_left u.isUnit,
      Ring.ord_pow (mem_nonZeroDivisors_of_ne_zero hϖ'.ne_zero), Ring.ord_of_irreducible hϖ']
    simp
  rw [hord, mul_comm]

end Formalism.IrreducibleCountingLemmas.TW
