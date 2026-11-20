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

namespace GlobalTheory.HopfPoints

/- English proof (translation)
Introduce `R K _ _ _ _ _ _ _ _ A _ _ _ _ _`. Establish `hRK : Function.Injective (algebraMap R K)` using `IsFractionRing.injective R K`. Use `haveI : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).2 hRK`. Use `haveI : Algebra.Etale K (K ⊗[R] A) := GlobalTheory.etale_of_hopfAlgebra K (K ⊗[R] A)`. Set `e : (A →ₐ[R] K) ≃ (K ⊗[R] A →ₐ[K] K)` to `AlgHom.liftEquiv R K A K`.

Establish `hfin : Finite (A →ₐ[R] K)` using `by haveI : Finite (K ⊗[R] A →ₐ[K] K) := Finite.algHom K (K ⊗[R] A) K`. Conclude with `Finite.of_equiv _ e.symm`. Establish `hcard : Nat.card (A →ₐ[R] K) = Module.finrank R A`. Rewrite using `[Nat.card_congr e, GlobalTheory.natCard_algHom_eq_finrank_of_etale K (K ⊗[R] A) K]`. Conclude with `(TensorProduct.isBaseChange R A K).finrank_eq`.

Use `⟨hfin, fun a ha ↦ ?_, fun q ↦ ?_⟩` and prove the remaining obligations. Take `⟨n, ⟨f⟩⟩` from `Algebra.IsFiniteSplit.nonempty_algEquiv_fun K (K ⊗[R] A)`. Establish `h1 : (1 : K) ⊗ₜ[R] a = 0`. Apply `f.injective` to reduce the goal to its premises. Rewrite using `[map_zero]`.

Use function extensionality and compare the values at `i`. Set `φ : K ⊗[R] A →ₐ[K] K` to `(Pi.evalAlgHom K (fun _ : Fin n ↦ K) i).comp f.toAlgHom`. Use `ha ((φ.restrictScalars R).comp Algebra.TensorProduct.includeRight)` as an intermediate fact. Simplify `this` using `[φ]`. Establish `hinj : Function.Injective ((Algebra.linearMap R K).rTensor A ∘ₗ (TensorProduct.lid R A).symm.toLinearMap)` using `(Module.Flat.rTensor_preserves_injective_linearMap _ hRK).comp (TensorProduct.lid R A).symm.injective`.

Apply `hinj` to reduce the goal to its premises. Simplify using `using h1`. Rewrite using `[hcard, Module.rankAtStalk_eq q]`. Conclude with `Ideal.finrank_fiber_eq_finrank q.asIdeal`.
-/
theorem finite_points_separate_rank : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (A : Type) [CommRing A] [HopfAlgebra R A] [IsCocomm R A] [Module.Finite R A] [Module.Projective R A], Finite (A →ₐ[R] K) ∧ (∀ a : A, (∀ ψ : A →ₐ[R] K, ψ a = 0) → a = 0) ∧ ∀ q : PrimeSpectrum R, Module.rankAtStalk (R := R) A q = Nat.card (A →ₐ[R] K) := by
  intro R K _ _ _ _ _ _ _ _ A _ _ _ _ _
  have hRK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  haveI : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).2 hRK
  haveI : Algebra.Etale K (K ⊗[R] A) := GlobalTheory.etale_of_hopfAlgebra K (K ⊗[R] A)
  let e : (A →ₐ[R] K) ≃ (K ⊗[R] A →ₐ[K] K) := AlgHom.liftEquiv R K A K
  have hfin : Finite (A →ₐ[R] K) := by
    haveI : Finite (K ⊗[R] A →ₐ[K] K) := Finite.algHom K (K ⊗[R] A) K
    exact Finite.of_equiv _ e.symm
  have hcard : Nat.card (A →ₐ[R] K) = Module.finrank R A := by
    rw [Nat.card_congr e, GlobalTheory.natCard_algHom_eq_finrank_of_etale K (K ⊗[R] A) K]
    exact (TensorProduct.isBaseChange R A K).finrank_eq
  refine ⟨hfin, fun a ha ↦ ?_, fun q ↦ ?_⟩
  · obtain ⟨n, ⟨f⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun K (K ⊗[R] A)
    have h1 : (1 : K) ⊗ₜ[R] a = 0 := by
      apply f.injective
      rw [map_zero]
      funext i
      let φ : K ⊗[R] A →ₐ[K] K := (Pi.evalAlgHom K (fun _ : Fin n ↦ K) i).comp f.toAlgHom
      have := ha ((φ.restrictScalars R).comp Algebra.TensorProduct.includeRight)
      simpa [φ] using this
    have hinj : Function.Injective
        ((Algebra.linearMap R K).rTensor A ∘ₗ (TensorProduct.lid R A).symm.toLinearMap) :=
      (Module.Flat.rTensor_preserves_injective_linearMap _ hRK).comp
        (TensorProduct.lid R A).symm.injective
    apply hinj
    simpa using h1
  · rw [hcard, Module.rankAtStalk_eq q]
    exact Ideal.finrank_fiber_eq_finrank q.asIdeal

end GlobalTheory.HopfPoints
