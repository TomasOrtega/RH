import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodCover
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points
open scoped TensorProduct

namespace GlobalTheory.EtaleComplexPoints

/- English proof (translation)
Introduce `A B _ _ f δ hf hfin hfree φ`. Use `letI := f.toAlgebra`. Use `letI := φ.toAlgebra`. Take `⟨hF, hrk⟩` from `hfree`. Establish `hEt : Algebra.Etale A B` using `RingHom.etale_algebraMap.1 hf`.

Establish `hMF : Module.Finite A B` using `hfin`. Establish `hFE : Algebra.FormallyEtale ℂ (ℂ ⊗[A] B)` using `inferInstance`. Establish `hcard` using `GlobalTheory.natCard_algHom_eq_finrank_of_etale_baseChange A B ℂ`. Establish `hto (ψ : {ψ : B →+* ℂ | ψ.comp f = φ}) (a : A) : ψ.1 (algebraMap A B a) = algebraMap A ℂ a`. Use `congrArg (fun g : A →+* ℂ => g a) ψ.2` as an intermediate fact.

Simplify `this` using `[RingHom.algebraMap_toAlgebra]`. Establish `hinv (g : B →ₐ[A] ℂ) : (g : B →+* ℂ).comp f = φ`. Use extensionality with `a`. Simplify `g.commutes a` using `[RingHom.algebraMap_toAlgebra]`. Set `e : {ψ : B →+* ℂ | ψ.comp f = φ} ≃ (B →ₐ[A] ℂ)` to `{ toFun := fun ψ => { ψ.1 with commutes' := hto ψ } invFun := fun g => ⟨g.toRingHom, hinv g⟩ left_inv := fun ψ => rfl right_inv := fun g => rfl }`.

Establish `hfinite : Finite (B →ₐ[A] ℂ)` using `Finite.of_equiv _ (AlgHom.liftEquiv A ℂ B ℂ).symm`. Rewrite using `[Set.encard, ENat.card_congr e, ENat.card_eq_coe_natCard, hcard, hrk]`.
-/
theorem encard_complexPoints_eq_rank : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (δ : ℕ), f.Etale → f.Finite → (letI := f.toAlgebra; Module.Free A B ∧ Module.finrank A B = δ) → ∀ φ : A →+* ℂ, {ψ : B →+* ℂ | ψ.comp f = φ}.encard = (δ : ℕ∞) := by
  intro A B _ _ f δ hf hfin hfree φ
  letI := f.toAlgebra
  letI := φ.toAlgebra
  obtain ⟨hF, hrk⟩ := hfree
  have hEt : Algebra.Etale A B := RingHom.etale_algebraMap.1 hf
  have hMF : Module.Finite A B := hfin
  have hFE : Algebra.FormallyEtale ℂ (ℂ ⊗[A] B) := inferInstance
  have hcard := GlobalTheory.natCard_algHom_eq_finrank_of_etale_baseChange A B ℂ
  have hto (ψ : {ψ : B →+* ℂ | ψ.comp f = φ}) (a : A) : ψ.1 (algebraMap A B a) = algebraMap A ℂ a := by
    have := congrArg (fun g : A →+* ℂ => g a) ψ.2
    simpa [RingHom.algebraMap_toAlgebra] using this
  have hinv (g : B →ₐ[A] ℂ) : (g : B →+* ℂ).comp f = φ := by
    ext a
    simpa [RingHom.algebraMap_toAlgebra] using g.commutes a
  let e : {ψ : B →+* ℂ | ψ.comp f = φ} ≃ (B →ₐ[A] ℂ) :=
    { toFun := fun ψ => { ψ.1 with commutes' := hto ψ }
      invFun := fun g => ⟨g.toRingHom, hinv g⟩
      left_inv := fun ψ => rfl
      right_inv := fun g => rfl }
  have hfinite : Finite (B →ₐ[A] ℂ) :=
    Finite.of_equiv _ (AlgHom.liftEquiv A ℂ B ℂ).symm
  rw [Set.encard, ENat.card_congr e, ENat.card_eq_coe_natCard, hcard, hrk]

end GlobalTheory.EtaleComplexPoints
