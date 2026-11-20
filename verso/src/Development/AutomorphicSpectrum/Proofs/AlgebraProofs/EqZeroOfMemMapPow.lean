import Mathlib

open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.KrullGroupAlg

/- English proof (translation)
Establish `hx' : x ∈ Submodule.span (AddMonoidAlgebra R M) (algebraMap R (AddMonoidAlgebra R M) '' I)` using `hx`. Use `clear hx`. Use `revert φ`. Proceed by induction on `hx' using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨a, ha, rfl⟩` from `hy`. Introduce `φ`. Rewrite using `[Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul]`. Conclude with `I.mul_mem_right _ ha`. Consider the case `zero`.

Introduce `φ`. Rewrite using `[map_zero]`. Conclude with `I.zero_mem`. Consider the case `add y z _ _ hy hz`. Introduce `φ`.

Rewrite using `[map_add]`. Conclude with `I.add_mem (hy φ) (hz φ)`. Consider the case `smul r y _ hy`. Introduce `φ`. Use `hy (φ ∘ₗ LinearMap.mulLeft R r)` as an intermediate fact.

Simplify `this` using `[smul_eq_mul]`.
-/
theorem coeff_mem_of_mem_map {R M : Type} [CommRing R] [AddCommGroup M] (I : Ideal R)
    (x : AddMonoidAlgebra R M) (hx : x ∈ Ideal.map (algebraMap R (AddMonoidAlgebra R M)) I)
    (φ : AddMonoidAlgebra R M →ₗ[R] R) : φ x ∈ I := by
  have hx' : x ∈ Submodule.span (AddMonoidAlgebra R M) (algebraMap R (AddMonoidAlgebra R M) '' I) := hx
  clear hx
  revert φ
  induction hx' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    intro φ
    rw [Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul]
    exact I.mul_mem_right _ ha
  | zero =>
    intro φ
    rw [map_zero]
    exact I.zero_mem
  | add y z _ _ hy hz =>
    intro φ
    rw [map_add]
    exact I.add_mem (hy φ) (hz φ)
  | smul r y _ hy =>
    intro φ
    have := hy (φ ∘ₗ LinearMap.mulLeft R r)
    simpa [smul_eq_mul] using this

/- English proof (translation)
Introduce `R M _ _ _ _ x hx`. Use extensionality with `m`. Establish `hm : (Finsupp.lapply m ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap) x ∈ ⨅ n : ℕ, IsLocalRing.maximalIdeal R ^ n` using `Ideal.mem_iInf.2 fun n => coeff_mem_of_mem_map _ x (hx n) (Finsupp.lapply m ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap)`. Rewrite `hm` using `[Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal R).ne_top, Ideal.mem_bot]`. Simplify using `using hm`.
-/
theorem eq_zero_of_mem_map_pow : ∀ (R M : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup M] (x : AddMonoidAlgebra R M), (∀ n : ℕ, x ∈ Ideal.map (algebraMap R (AddMonoidAlgebra R M)) (IsLocalRing.maximalIdeal R ^ n)) → x = 0 := by
  intro R M _ _ _ _ x hx
  ext m
  have hm : (Finsupp.lapply m ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap) x ∈ ⨅ n : ℕ, IsLocalRing.maximalIdeal R ^ n :=
    Ideal.mem_iInf.2 fun n =>
      coeff_mem_of_mem_map _ x (hx n) (Finsupp.lapply m ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap)
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal R).ne_top,
    Ideal.mem_bot] at hm
  simpa using hm

end GlobalTheory.CompanionTheory.KrullGroupAlg
