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
Introduce `R K _ _ _ _ _ _ _ _ A _ _ _ _ hsep k _ _ φ`. Use `letI := Fintype.ofFinite (A →ₐ[R] K)`. Choose the witnesses or unpack the hypotheses as in `⟨ψ, hψ⟩ : ∃ ψ : A →ₐ[R] K, ∀ a, ψ a = 0 → φ a = 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Use `choose f hf using h`. Establish `h0 : (∏ ψ, f ψ) = 0`. Apply `hsep` to reduce the goal to its premises. Introduce `ψ`. Rewrite using `[map_prod]`.

Conclude with `Finset.prod_eq_zero (Finset.mem_univ ψ) (hf ψ).1`. Establish `hne : φ (∏ ψ, f ψ) ≠ 0`. Rewrite using `[map_prod]`. Conclude with `Finset.prod_ne_zero_iff.mpr (fun ψ _ => (hf ψ).2)`. Conclude with `hne (by rw [h0, map_zero])`.

Establish `hinj : Function.Injective (algebraMap R K)` using `IsFractionRing.injective R K`. Establish `hrange : ∀ a : A, ψ a ∈ (⊥ : Subalgebra R K)`. Introduce `a`. Establish `hint : IsIntegral R (ψ a)` using `(Algebra.IsIntegral.isIntegral (R := R) a).map ψ`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.mp hint`.

Conclude with `Algebra.mem_bot.2 ⟨y, hy⟩`. Set `e` to `Algebra.botEquivOfInjective hinj`. Establish `he : ∀ x : (⊥ : Subalgebra R K), algebraMap R K (e x) = (x : K)`. Introduce `x`. Take `⟨r, rfl⟩` from `e.symm.surjective x`.

Rewrite using `[e.apply_symm_apply]`. Conclude with `(congrArg Subtype.val (e.symm.commutes r)).symm`. Set `s : A →ₐ[R] R` to `e.toAlgHom.comp (ψ.codRestrict ⊥ hrange)`. Establish `hs : ∀ a, algebraMap R K (s a) = ψ a` using `fun a => he _`. Use `⟨s, ?_⟩` and prove the remaining obligations.

Use extensionality with `a`. Establish `h1 : ψ (a - algebraMap R A (s a)) = 0`. Rewrite using `[map_sub, AlgHom.commutes, hs, sub_self]`. Establish `h2` using `hψ _ h1`. Rewrite `h2` using `[map_sub, AlgHom.commutes, sub_eq_zero]`.

Simplify using `using h2`.
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
