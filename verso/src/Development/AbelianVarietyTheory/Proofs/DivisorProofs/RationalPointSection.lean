import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Equip the data with the indicated structure. Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem finiteAlg_fieldPoint_factors_through_base : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A] [Finite (A →ₐ[R] K)], (∀ a : A, (∀ ψ : A →ₐ[R] K, ψ a = 0) → a = 0) → ∀ (k : Type) [Field k] [Algebra R k] (φ : A →ₐ[R] k), ∃ s : A →ₐ[R] R, φ = (Algebra.ofId R k).comp s := by
  intro R K _ _ _ _ _ _ _ _ A _ _ _ _ hsep k _ _ φ
  classical
  letI := Fintype.ofFinite (A →ₐ[R] K)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : A →ₐ[R] K, ∀ a, ψ a = 0 → φ a = 0 := by
    by_contra h
    push_neg at h
    choose f hf using h
    have h0 : (∏ ψ, f ψ) = 0 := by
      apply hsep
      intro ψ
      rw [map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ ψ) (hf ψ).1
    have hne : φ (∏ ψ, f ψ) ≠ 0 := by
      rw [map_prod]
      exact Finset.prod_ne_zero_iff.mpr (fun ψ _ => (hf ψ).2)
    exact hne (by rw [h0, map_zero])
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hrange : ∀ a : A, ψ a ∈ (⊥ : Subalgebra R K) := by
    intro a
    have hint : IsIntegral R (ψ a) := (Algebra.IsIntegral.isIntegral (R := R) a).map ψ
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    exact Algebra.mem_bot.2 ⟨y, hy⟩
  let e := Algebra.botEquivOfInjective hinj
  have he : ∀ x : (⊥ : Subalgebra R K), algebraMap R K (e x) = (x : K) := by
    intro x
    obtain ⟨r, rfl⟩ := e.symm.surjective x
    rw [e.apply_symm_apply]
    exact (congrArg Subtype.val (e.symm.commutes r)).symm
  let s : A →ₐ[R] R := e.toAlgHom.comp (ψ.codRestrict ⊥ hrange)
  have hs : ∀ a, algebraMap R K (s a) = ψ a := fun a => he _
  refine ⟨s, ?_⟩
  ext a
  have h1 : ψ (a - algebraMap R A (s a)) = 0 := by
    rw [map_sub, AlgHom.commutes, hs, sub_self]
  have h2 := hψ _ h1
  rw [map_sub, AlgHom.commutes, sub_eq_zero] at h2
  simpa using h2

end GlobalTheory
