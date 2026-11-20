import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.TensorCompl
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NegOneNotSqSqrtTwo

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.QuadFieldP

open QuadraticAlgebra

/- English proof (translation)
Introduce `h`. Set `_` to `(τ.comp (algebraMap (maximalRealSubfield E) K)).toAlgebra`. Set `φ : E →ₐ[maximalRealSubfield E] ℂ` to `IsAlgClosed.lift`. Establish `h1 : (φ s) ^ 2 = τ (algebraMap (maximalRealSubfield E) K d)`. Rewrite using `[← map_pow, ← hd, φ.commutes]`.

Both sides reduce to the same expression. Establish `hu : starRingEnd ℂ (φ s) = - φ s`. Establish `h'` using `IsCMField.complexEmbedding_complexConj E φ.toRingHom s`. Simplify `h'.symm` using `[hs]`. Establish `hu0 : φ s ≠ 0`.

Introduce `h0; exact hs0 (φ.toRingHom.injective (by simpa using h0))`. Rewrite `h` using `[← h1]`. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 h with h2 | h2` into its components or cases. Apply `hu0` to reduce the goal to its premises. Establish `: starRingEnd ℂ (φ s) = φ s` using `by rw [← h2]; exact ht`.

Establish `h3 : (2 : ℂ) * φ s = 0` using `by linear_combination hu - this`. Simplify using `using h3`. Apply `hu0` to reduce the goal to its premises. Establish `: starRingEnd ℂ (φ s) = φ s`. Use `congrArg Neg.neg ht` as an intermediate fact.

Rewrite `this` using `[h2, map_neg, neg_neg, neg_neg]`. Conclude with `this`. Establish `h3 : (2 : ℂ) * φ s = 0` using `by linear_combination hu - this`. Simplify using `using h3`.
-/
theorem not_sq_of_real (E : Type) [Field E] [NumberField E] [IsCMField E] (s : E)
    (d : maximalRealSubfield E) (hs0 : s ≠ 0) (hs : IsCMField.complexConj E s = -s)
    (hd : algebraMap (maximalRealSubfield E) E d = s ^ 2) (K : Type) [Field K]
    [Algebra (maximalRealSubfield E) K] (τ : K →+* ℂ) (t : ℂ) (ht : starRingEnd ℂ t = t) :
    t ^ 2 ≠ τ (algebraMap (maximalRealSubfield E) K d) := by
  intro h
  let _ := (τ.comp (algebraMap (maximalRealSubfield E) K)).toAlgebra
  let φ : E →ₐ[maximalRealSubfield E] ℂ := IsAlgClosed.lift
  have h1 : (φ s) ^ 2 = τ (algebraMap (maximalRealSubfield E) K d) := by
    rw [← map_pow, ← hd, φ.commutes]; rfl
  have hu : starRingEnd ℂ (φ s) = - φ s := by
    have h' := IsCMField.complexEmbedding_complexConj E φ.toRingHom s
    simpa [hs] using h'.symm
  have hu0 : φ s ≠ 0 := by
    intro h0; exact hs0 (φ.toRingHom.injective (by simpa using h0))
  rw [← h1] at h
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h2 | h2
  · apply hu0
    have : starRingEnd ℂ (φ s) = φ s := by rw [← h2]; exact ht
    have h3 : (2 : ℂ) * φ s = 0 := by linear_combination hu - this
    simpa using h3
  · apply hu0
    have : starRingEnd ℂ (φ s) = φ s := by
      have := congrArg Neg.neg ht
      rw [h2, map_neg, neg_neg, neg_neg] at this
      exact this
    have h3 : (2 : ℂ) * φ s = 0 := by linear_combination hu - this
    simpa using h3

end PositivityTheory.Rg.BcB.G3.QuadFieldP

namespace PositivityTheory.Rg.BcB.G3

open QuadFieldP QuadraticAlgebra in
/- English proof (translation)
Introduce `E _ _ _ s d hs0 hs hd K _ _ _ hKr`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero, add_zero, ← IsTotallyReal.finrank, ← IsCMField.card_infinitePlace_eq_card_infinitePlace E, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero …`. Generalize the expression as in `hδ : algebraMap (maximalRealSubfield E) K d = δ`. Establish `hkey : ∀ (τ : K →+* ℂ) (t : ℂ), starRingEnd ℂ t = t → t ^ 2 ≠ τ δ`.

Introduce `τ t ht`. Rewrite using `[← hδ]`. Conclude with `not_sq_of_real E s d hs0 hs hd K τ t ht`. Establish `hns : ∀ r : K, r ^ 2 ≠ δ + 0 * r`. Introduce `r hr`.

Set `τ : K →+* ℂ` to `Classical.choice (inferInstance : Nonempty _)`. Establish `hre` using `ComplexEmbedding.isReal_iff.1 (IsTotallyReal.complexEmbedding_isReal τ)`. Use `hkey τ (τ r) ?_ ?_` and prove the remaining obligations. Rewrite using `[← ComplexEmbedding.conjugate_coe_eq, hre]`. Rewrite using `[← map_pow, hr, zero_mul, add_zero]`.

Establish `: Fact (∀ r : K, r ^ 2 ≠ δ + 0 * r)` using `⟨hns⟩`. Establish `hq` using `GlobalTheory.QuadSymbol.Model.isQuadratic δ`. Establish `hnf` using `GlobalTheory.QuadSymbol.Model.numberField δ`. Establish `: FiniteDimensional K (QuadraticAlgebra K δ 0)` using `Module.Finite.of_basis (QuadraticAlgebra.basis δ 0)`. Use `⟨QuadraticAlgebra K δ 0, inferInstance, hnf, inferInstance, hq, ?_, ?_, ?_⟩` and prove the remaining obligations.

Use `⟨fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]`. Introduce `hre`. Set `e` to `w.embedding`. Use `hkey (e.comp (algebraMap K _)) (e (ω : QuadraticAlgebra K δ 0)) ?_ ?_` and prove the remaining obligations.

Rewrite using `[← ComplexEmbedding.conjugate_coe_eq, hre]`. Rewrite using `[RingHom.comp_apply, ← map_pow, sq, omega_mul_omega_eq_algebraMap]`. Simplify using the standard rewrite rules. Introduce `x`. Rewrite using `[GlobalTheory.QuadSymbol.mem_globalNorms_iff]`.

Establish `key` using `GlobalTheory.QuadSymbol.Model.mem_normGroup_sqrt (A := K) δ (x := x)`. Rewrite `key` using `[GlobalTheory.QuadSymbol.mem_normGroup_iff]`. Simplify using `only [Algebra.algebraMap_self, RingHom.id_apply] at key`. Rewrite using `[← key]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨z, hz⟩`. Use `⟨(Algebra.TensorProduct.lid K _).symm z, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.norm_eq_of_algEquiv, hz]`. Introduce and unpack `⟨z, hz⟩`. Use `⟨Algebra.TensorProduct.lid K _ z, ?_⟩` and prove the remaining obligations.

Rewrite using `[Algebra.norm_eq_of_algEquiv, hz]`. Introduce `u x`. Conclude with `GlobalTheory.QuadSymbol.Model.mem_normGroup_sqrt δ`.
-/
theorem quadField_pf : QuadField := by
  intro E _ _ _ s d hs0 hs hd K _ _ _ hKr
  refine ⟨?_, ?_⟩
  · rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero, add_zero,
      ← IsTotallyReal.finrank, ← IsCMField.card_infinitePlace_eq_card_infinitePlace E,
      InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero, add_zero,
      ← IsTotallyReal.finrank, ← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) K, mul_comm]
  generalize hδ : algebraMap (maximalRealSubfield E) K d = δ
  have hkey : ∀ (τ : K →+* ℂ) (t : ℂ), starRingEnd ℂ t = t → t ^ 2 ≠ τ δ := by
    intro τ t ht
    rw [← hδ]
    exact not_sq_of_real E s d hs0 hs hd K τ t ht
  have hns : ∀ r : K, r ^ 2 ≠ δ + 0 * r := by
    intro r hr
    let τ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
    have hre := ComplexEmbedding.isReal_iff.1 (IsTotallyReal.complexEmbedding_isReal τ)
    refine hkey τ (τ r) ?_ ?_
    · rw [← ComplexEmbedding.conjugate_coe_eq, hre]
    · rw [← map_pow, hr, zero_mul, add_zero]
  have : Fact (∀ r : K, r ^ 2 ≠ δ + 0 * r) := ⟨hns⟩
  have hq := GlobalTheory.QuadSymbol.Model.isQuadratic δ
  have hnf := GlobalTheory.QuadSymbol.Model.numberField δ
  have : FiniteDimensional K (QuadraticAlgebra K δ 0) :=
    Module.Finite.of_basis (QuadraticAlgebra.basis δ 0)
  refine ⟨QuadraticAlgebra K δ 0, inferInstance, hnf, inferInstance, hq, ?_, ?_, ?_⟩
  · refine ⟨fun w => ?_⟩
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    intro hre
    let e := w.embedding
    refine hkey (e.comp (algebraMap K _)) (e (ω : QuadraticAlgebra K δ 0)) ?_ ?_
    · rw [← ComplexEmbedding.conjugate_coe_eq, hre]
    · rw [RingHom.comp_apply, ← map_pow, sq, omega_mul_omega_eq_algebraMap]; simp
  · intro x
    rw [GlobalTheory.QuadSymbol.mem_globalNorms_iff]
    have key := GlobalTheory.QuadSymbol.Model.mem_normGroup_sqrt (A := K) δ (x := x)
    rw [GlobalTheory.QuadSymbol.mem_normGroup_iff] at key
    simp only [Algebra.algebraMap_self, RingHom.id_apply] at key
    rw [← key]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨(Algebra.TensorProduct.lid K _).symm z, ?_⟩
      rw [Algebra.norm_eq_of_algEquiv, hz]
    · rintro ⟨z, hz⟩
      refine ⟨Algebra.TensorProduct.lid K _ z, ?_⟩
      rw [Algebra.norm_eq_of_algEquiv, hz]
  · intro u x
    exact GlobalTheory.QuadSymbol.Model.mem_normGroup_sqrt δ

end PositivityTheory.Rg.BcB.G3

end
