import Mathlib

open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.CommAlg.SatOfInj

/- English proof (translation)
Rewrite using `[IsDiscreteValuationRing.irreducible_iff_uniformizer π |>.mp hπ, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, -, rfl⟩`. Conclude with `⟨z, rfl⟩`. Introduce and unpack `⟨z, rfl⟩`.

Conclude with `⟨z, trivial, rfl⟩`.
-/
theorem mem_max_smul_top_iff {R M : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup M] [Module R M] {π : R} (hπ : Irreducible π) (x : M) :
    x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ↔ ∃ z : M, x = π • z := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer π |>.mp hπ,
    Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨z, -, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, trivial, rfl⟩

/- English proof (translation)
The claim follows from `(smul_eq_zero.mp h).resolve_left ha`.
-/
theorem eq_zero_of_smul {R M : Type} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.IsTorsionFree R M] {a : R} (ha : a ≠ 0) {z : M} (h : a • z = 0) : z = 0 :=
  (smul_eq_zero.mp h).resolve_left ha

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => intro y hy`. Simplify using `using hy`. Consider the case `succ n ih`. Introduce `y hy`.

Take `⟨x, hx⟩` from `hy`. Establish `hmem : f x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R E)`. Rewrite using `[mem_max_smul_top_iff hπ]`. Conclude with `⟨π ^ n • y, by rw [hx, pow_succ', mul_smul]⟩`. Take `⟨x', rfl⟩` from `(mem_max_smul_top_iff hπ x).mp (hf x hmem)`.

Use `ih y ⟨x', ?_⟩` and prove the remaining obligations. Establish `h0 : π • (f x' - π ^ n • y) = 0`. Rewrite using `[smul_sub, ← map_smul, hx, pow_succ', mul_smul, sub_self]`. Conclude with `sub_eq_zero.mp (eq_zero_of_smul hπ.ne_zero h0)`.
-/
theorem pow_step {R P E : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup P] [Module R P] [AddCommGroup E] [Module R E] [Module.IsTorsionFree R E]
    (f : P →ₗ[R] E) {π : R} (hπ : Irreducible π)
    (hf : ∀ x : P, f x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R E) →
      x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R P))
    (n : ℕ) : ∀ (y : E), π ^ n • y ∈ LinearMap.range f → y ∈ LinearMap.range f := by
  induction n with
  | zero => intro y hy; simpa using hy
  | succ n ih =>
    intro y hy
    obtain ⟨x, hx⟩ := hy
    have hmem : f x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R E) := by
      rw [mem_max_smul_top_iff hπ]
      exact ⟨π ^ n • y, by rw [hx, pow_succ', mul_smul]⟩
    obtain ⟨x', rfl⟩ := (mem_max_smul_top_iff hπ x).mp (hf x hmem)
    refine ih y ⟨x', ?_⟩
    have h0 : π • (f x' - π ^ n • y) = 0 := by
      rw [smul_sub, ← map_smul, hx, pow_succ', mul_smul, sub_self]
    exact sub_eq_zero.mp (eq_zero_of_smul hπ.ne_zero h0)

/- English proof (translation)
Introduce `R P E _ _ _ _ _ _ _ _ _ _ f hf`. Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible R`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← LinearMap.ker_eq_bot]`. Use `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R) _ (IsNoetherian.noetherian _) ?_ (IsLocalRing.maximalIdeal_le_jacobson _)` and prove the remaining obligations.

Introduce `x hx`. Establish `hx0 : f x = 0` using `hx`. Establish `hmem : f x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R E)`. Rewrite using `[hx0]`. Conclude with `Submodule.zero_mem _`.

Take `⟨x', rfl⟩` from `(mem_max_smul_top_iff hπ x).mp (hf x hmem)`. Establish `hx' : f x' = 0`. Rewrite `hx0` using `[map_smul]`. Conclude with `eq_zero_of_smul hπ.ne_zero hx0`. Conclude with `Submodule.smul_mem_smul ((IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ ▸ Ideal.mem_span_singleton_self π) (LinearMap.mem_ker.mpr hx')`.

Introduce `a y ha hy`. Take `⟨n, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ`. Establish `h1 : π ^ n • ((u : R) • y) ∈ LinearMap.range f`. Rewrite using `[smul_smul, mul_comm]`. Conclude with `hy`.

Establish `h2` using `pow_step f hπ hf n _ h1`. Establish `h3` using `Submodule.smul_mem _ ((u⁻¹ : Rˣ) : R) h2`. Rewrite `h3` using `[smul_smul, Units.inv_mul, one_smul]`. Then use the resulting hypothesis.
-/
theorem sat_of_inj_mod : ∀ (R P E : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup P] [Module R P] [Module.Finite R P] [AddCommGroup E] [Module R E]
    [Module.IsTorsionFree R E] [Module.IsTorsionFree R P] (f : P →ₗ[R] E),
    (∀ x : P, f x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R E) →
      x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R P)) →
    Function.Injective f ∧ ∀ (a : R) (y : E), a ≠ 0 → a • y ∈ LinearMap.range f →
      y ∈ LinearMap.range f := by
  intro R P E _ _ _ _ _ _ _ _ _ _ f hf
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot]
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R) _
      (IsNoetherian.noetherian _) ?_ (IsLocalRing.maximalIdeal_le_jacobson _)
    intro x hx
    have hx0 : f x = 0 := hx
    have hmem : f x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R E) := by
      rw [hx0]; exact Submodule.zero_mem _
    obtain ⟨x', rfl⟩ := (mem_max_smul_top_iff hπ x).mp (hf x hmem)
    have hx' : f x' = 0 := by
      rw [map_smul] at hx0
      exact eq_zero_of_smul hπ.ne_zero hx0
    exact Submodule.smul_mem_smul
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ ▸ Ideal.mem_span_singleton_self π)
      (LinearMap.mem_ker.mpr hx')
  · intro a y ha hy
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
    have h1 : π ^ n • ((u : R) • y) ∈ LinearMap.range f := by
      rw [smul_smul, mul_comm]
      exact hy
    have h2 := pow_step f hπ hf n _ h1
    have h3 := Submodule.smul_mem _ ((u⁻¹ : Rˣ) : R) h2
    rwa [smul_smul, Units.inv_mul, one_smul] at h3

end GlobalTheory.CompanionTheory.CommAlg.SatOfInj
