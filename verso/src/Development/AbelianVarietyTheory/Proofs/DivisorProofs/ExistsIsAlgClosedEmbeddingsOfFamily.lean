import Mathlib

namespace GlobalTheory

open MvPolynomial

/- English proof (translation)
Introduce `F _ I k _ f`. Set `K` to `FractionRing (MvPolynomial (Σ i, k i) F)`. Set `Ω` to `AlgebraicClosure K`. Establish `key : ∀ i, ∃ g : k i →+* Ω, g.comp (f i) = algebraMap F Ω`. Introduce `i`.

Use `letI : Algebra F (k i) := (f i).toAlgebra`. Take `⟨s, hs⟩` from `exists_isTranscendenceBasis F (k i)`. Set `x : (Σ i, k i) → Ω` to `fun j => algebraMap K Ω (algebraMap (MvPolynomial (Σ i, k i) F) K (X j))`. Establish `hx : AlgebraicIndependent F x`. Establish `h0` using `MvPolynomial.algebraicIndependent_X (Σ i, k i) F`.

Establish `h1 : Function.Injective (IsScalarTower.toAlgHom F (MvPolynomial (Σ i, k i) F) K)` using `IsFractionRing.injective _ _`. Establish `h2 : Function.Injective (IsScalarTower.toAlgHom F K Ω)` using `(algebraMap K Ω).injective`. Use `(h0.map' h1).map' h2` as an intermediate fact. Conclude with `this`. Establish `hv : AlgebraicIndependent F (fun b : s => x ⟨i, b.1⟩)` using `hx.comp (fun b : s => (⟨i, b.1⟩ : Σ i, k i)) (by`.

Introduce `a b hab`. Conclude with `Subtype.ext (by simpa using hab))`. Set `φ0 : IntermediateField.adjoin F (Set.range ((↑) : s → k i)) →ₐ[F] Ω` to `(IntermediateField.val _).comp (hv.aevalEquivField.toAlgHom.comp hs.1.reprField)`. Establish `halg` using `hs.isAlgebraic_field`. Take `⟨φ, -⟩` from `IntermediateField.exists_algHom_of_splits' φ0 (fun (y : k i) => ⟨(Algebra.IsAlgebraic.isAlgebraic (R := IntermediateField.adjoin F (Set.range ((↑) : s → k i))) y).isIntegral, IsAlgClosed.splits _⟩)`.

Use `⟨φ.toRingHom, ?_⟩` and prove the remaining obligations. Use extensionality with `y`. Conclude with `φ.commutes y`. Use `choose g hg using key`. Conclude with `⟨Ω, inferInstance, inferInstance, g, algebraMap F Ω, hg⟩`.
-/
theorem exists_isAlgClosed_embeddings_of_family :
    ∀ (F : Type) [Field F] (I : Type) (k : I → Type) [∀ i, Field (k i)] (f : ∀ i, F →+* k i),
      ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (g : ∀ i, k i →+* L) (h : F →+* L),
        ∀ i, (g i).comp (f i) = h := by
  intro F _ I k _ f
  let K := FractionRing (MvPolynomial (Σ i, k i) F)
  let Ω := AlgebraicClosure K
  have key : ∀ i, ∃ g : k i →+* Ω, g.comp (f i) = algebraMap F Ω := by
    intro i
    letI : Algebra F (k i) := (f i).toAlgebra
    obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F (k i)
    let x : (Σ i, k i) → Ω := fun j => algebraMap K Ω (algebraMap (MvPolynomial (Σ i, k i) F) K (X j))
    have hx : AlgebraicIndependent F x := by
      have h0 := MvPolynomial.algebraicIndependent_X (Σ i, k i) F
      have h1 : Function.Injective (IsScalarTower.toAlgHom F (MvPolynomial (Σ i, k i) F) K) :=
        IsFractionRing.injective _ _
      have h2 : Function.Injective (IsScalarTower.toAlgHom F K Ω) :=
        (algebraMap K Ω).injective
      have := (h0.map' h1).map' h2
      exact this
    have hv : AlgebraicIndependent F (fun b : s => x ⟨i, b.1⟩) :=
      hx.comp (fun b : s => (⟨i, b.1⟩ : Σ i, k i)) (by
        intro a b hab
        exact Subtype.ext (by simpa using hab))
    let φ0 : IntermediateField.adjoin F (Set.range ((↑) : s → k i)) →ₐ[F] Ω :=
      (IntermediateField.val _).comp (hv.aevalEquivField.toAlgHom.comp hs.1.reprField)
    have halg := hs.isAlgebraic_field
    obtain ⟨φ, -⟩ := IntermediateField.exists_algHom_of_splits' φ0
      (fun (y : k i) => ⟨(Algebra.IsAlgebraic.isAlgebraic
        (R := IntermediateField.adjoin F (Set.range ((↑) : s → k i))) y).isIntegral,
        IsAlgClosed.splits _⟩)
    refine ⟨φ.toRingHom, ?_⟩
    ext y
    exact φ.commutes y
  choose g hg using key
  exact ⟨Ω, inferInstance, inferInstance, g, algebraMap F Ω, hg⟩

end GlobalTheory
