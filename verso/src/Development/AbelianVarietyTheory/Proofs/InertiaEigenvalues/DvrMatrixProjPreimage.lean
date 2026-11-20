import Mathlib
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

/- English proof (translation)
Set `f : (n → O) →ₗ[O] (n → K)` to `LinearMap.compLeft (Algebra.linearMap O K) n`. Set `U : Submodule O (n → O)` to `(S.restrictScalars O).comap f`. Establish `hmem : ∀ v : n → O, v ∈ U ↔ (fun i => algebraMap O K (v i)) ∈ S` using `fun v => Iff.rfl`. Establish `htf : NoZeroSMulDivisors O ((n → O) ⧸ U)`. Prove the components needed by the constructor for the conclusion.

Introduce `c x hcx`. Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective U x`. Distinguish the cases in `hc : c = 0`. Use `left`. Conclude with `hc`.

Use `right`. Rewrite `hcx` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Rewrite `hcx`, the goal using `[hmem]`. Establish `e : (fun i => algebraMap O K ((c • v) i)) = algebraMap O K c • (fun i => algebraMap O K (v i))`.

Use function extensionality and compare the values at `i`. Simplify using `[Algebra.smul_def]`. Rewrite `hcx` using `[e]`. Establish `hc' : algebraMap O K c ≠ 0`. Introduce `h; exact hc ((IsFractionRing.injective O K) (by rw [h, map_zero]))`.

Use `S.smul_mem (algebraMap O K c)⁻¹ hcx` as an intermediate fact. Rewrite `this` using `[smul_smul, inv_mul_cancel₀ hc', one_smul]`. Then use the resulting hypothesis. Use `haveI : Module.Free O ((n → O) ⧸ U) := Module.free_of_finite_type_torsion_free'`. Use `haveI : Module.Projective O ((n → O) ⧸ U) := Module.Projective.of_free`. Take `⟨s, hs⟩` from `Module.projective_lifting_property U.mkQ LinearMap.id (Submodule.mkQ_surjective U)`.

Set `π : (n → O) →ₗ[O] (n → O)` to `LinearMap.id - s ∘ₗ U.mkQ`. Establish `hπU : ∀ v, π v ∈ U`. Introduce `v`. Rewrite using `[← Submodule.Quotient.mk_eq_zero]`. Use `LinearMap.congr_fun hs (U.mkQ v)` as an intermediate fact.

Simplify using `only [LinearMap.comp_apply, LinearMap.id_apply] at this`. Simplify using `only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, Submodule.Quotient.mk_sub]`. Rewrite using `[← Submodule.mkQ_apply U (s _), this, Submodule.mkQ_apply, sub_self]`. Establish `hπfix : ∀ u ∈ U, π u = u`. Introduce `u hu`.

Establish `h0 : U.mkQ u = 0` using `(Submodule.Quotient.mk_eq_zero U).mpr hu`. Simplify using `only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, h0, map_zero, sub_zero]`. Use `⟨LinearMap.toMatrix' π, ?_, ?_⟩` and prove the remaining obligations. Introduce `v`. Rewrite using `[LinearMap.toMatrix'_mulVec]`.

Conclude with `hπU v`. Introduce `u hu`. Rewrite using `[LinearMap.toMatrix'_mulVec]`. Conclude with `hπfix u hu`.
-/
theorem dvr_matrix_proj_preimage (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K] (n : Type) [Fintype n] [DecidableEq n]
    (S : Submodule K (n → K)) :
    ∃ P : Matrix n n O, (∀ v : n → O, (fun i => algebraMap O K ((P.mulVec v) i)) ∈ S) ∧
      ∀ u : n → O, (fun i => algebraMap O K (u i)) ∈ S → P.mulVec u = u := by
  classical
  let f : (n → O) →ₗ[O] (n → K) := LinearMap.compLeft (Algebra.linearMap O K) n
  let U : Submodule O (n → O) := (S.restrictScalars O).comap f
  have hmem : ∀ v : n → O, v ∈ U ↔ (fun i => algebraMap O K (v i)) ∈ S := fun v => Iff.rfl
  have htf : NoZeroSMulDivisors O ((n → O) ⧸ U) := by
    constructor
    intro c x hcx
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective U x
    by_cases hc : c = 0
    · left; exact hc
    right
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hcx
    rw [Submodule.Quotient.mk_eq_zero]
    rw [hmem] at hcx ⊢
    have e : (fun i => algebraMap O K ((c • v) i)) = algebraMap O K c • (fun i => algebraMap O K (v i)) := by
      funext i; simp [Algebra.smul_def]
    rw [e] at hcx
    have hc' : algebraMap O K c ≠ 0 := by
      intro h; exact hc ((IsFractionRing.injective O K) (by rw [h, map_zero]))
    have := S.smul_mem (algebraMap O K c)⁻¹ hcx
    rwa [smul_smul, inv_mul_cancel₀ hc', one_smul] at this
  haveI : Module.Free O ((n → O) ⧸ U) := Module.free_of_finite_type_torsion_free'
  haveI : Module.Projective O ((n → O) ⧸ U) := Module.Projective.of_free
  obtain ⟨s, hs⟩ := Module.projective_lifting_property U.mkQ LinearMap.id (Submodule.mkQ_surjective U)
  let π : (n → O) →ₗ[O] (n → O) := LinearMap.id - s ∘ₗ U.mkQ
  have hπU : ∀ v, π v ∈ U := by
    intro v
    rw [← Submodule.Quotient.mk_eq_zero]
    have := LinearMap.congr_fun hs (U.mkQ v)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, Submodule.Quotient.mk_sub]
    rw [← Submodule.mkQ_apply U (s _), this, Submodule.mkQ_apply, sub_self]
  have hπfix : ∀ u ∈ U, π u = u := by
    intro u hu
    have h0 : U.mkQ u = 0 := (Submodule.Quotient.mk_eq_zero U).mpr hu
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, h0, map_zero, sub_zero]
  refine ⟨LinearMap.toMatrix' π, ?_, ?_⟩
  · intro v
    rw [LinearMap.toMatrix'_mulVec]
    exact hπU v
  · intro u hu
    rw [LinearMap.toMatrix'_mulVec]
    exact hπfix u hu

end GlobalTheory
