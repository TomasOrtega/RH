import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt GlobalTheory.DegCmp Filter
open scoped ENNReal

namespace GlobalTheory.DegCmp

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities.
-/
theorem rank_map_eq_of_ker_iff {K M A B : Type} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] (S : Submodule K M) (f : M →ₗ[K] A) (g : M →ₗ[K] B)
    (h : ∀ x ∈ S, f x = 0 ↔ g x = 0) :
    Module.rank K (S.map f) = Module.rank K (S.map g) := by
  have hk : LinearMap.ker (f.domRestrict S) = LinearMap.ker (g.domRestrict S) := by
    ext x
    simpa using h x x.2
  rw [← LinearMap.range_domRestrict, ← LinearMap.range_domRestrict,
    ← (LinearMap.quotKerEquivRange _).rank_eq, ← (LinearMap.quotKerEquivRange _).rank_eq, hk]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem range_pow_eq_map_homogeneous {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω) {N : ℕ} (b : Module.Basis (Fin N) K V) (τ : ℕ) :
    ((LinearMap.range ev) ^ τ : Submodule K Ω) =
      (homogeneousSubmodule (Fin N) K τ).map (aeval (fun j => ev (b j)) : MvPolynomial (Fin N) K →ₐ[K] Ω).toLinearMap := by
  rw [← homogeneousSubmodule_one_pow, Submodule.map_pow, homogeneousSubmodule_one_eq_span_X, Submodule.map_span,
    LinearMap.range_eq_map, ← b.span_eq, Submodule.map_span, ← Set.range_comp, ← Set.range_comp]
  congr 3
  ext j
  simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem hilb_eq_finrank_quotPiece : ∀ (K V Ω : Type) [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω] (ev : V →ₗ[K] Ω) (N : ℕ) (b : Module.Basis (Fin N) K V) (τ : ℕ), hilb ev τ = ((Module.finrank K (GlobalTheory.quotPiece (imageIdeal ev b) (τ : ℤ)) : ℕ) : ℕ∞) := by
  intro K V Ω _ _ _ _ _ ev N b τ
  rw [hilb, range_pow_eq_map_homogeneous ev b τ, GlobalTheory.quotPiece_natCast,
    rank_map_eq_of_ker_iff _ _ (Ideal.Quotient.mkₐ K (imageIdeal ev b)).toLinearMap, ← Module.finrank_eq_rank]
  · simp
  · intro x hx
    simp only [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact (mem_coneIdeal_of_isHomogeneous _ hx).symm

end GlobalTheory.DegCmp
