import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableRisingS
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory.CMTypeRealEmb

/- English proof (translation)
Rewrite using `[ComplexEmbedding.isReal_iff]`. Use extensionality with `a`. Simplify using `only [ComplexEmbedding.conjugate_coe_eq, RingHom.coe_comp, Function.comp_apply]`. Rewrite using `[← IsCMField.complexEmbedding_complexConj]`. Use `congr 1`.

Conclude with `IsCMField.complexConj_apply_eq_self E a`.
-/
theorem comp_isReal {E : Type} [Field E] [NumberField E] [IsCMField E] (φ : E →+* ℂ) :
    ComplexEmbedding.IsReal (φ.comp (algebraMap (maximalRealSubfield E) E)) := by
  rw [ComplexEmbedding.isReal_iff]
  ext a
  simp only [ComplexEmbedding.conjugate_coe_eq, RingHom.coe_comp, Function.comp_apply]
  rw [← IsCMField.complexEmbedding_complexConj]
  congr 1
  exact IsCMField.complexConj_apply_eq_self E a

/- English proof (translation)
Use `set F := maximalRealSubfield E`. Set `ψ : I → F →+* ℂ` to `fun i => (φ i).comp (algebraMap F E)`. Establish `hre : ∀ i, ComplexEmbedding.IsReal (ψ i)` using `fun i => comp_isReal (φ i)`. Set `e : I → Emb F` to `fun i => (hre i).embedding`. Establish `he : ∀ i a, ((e i a : ℝ) : ℂ) = φ i (a : E)` using `fun i a => (hre i).coe_embedding_apply a`.

Establish `hplace : ∀ i, (InfinitePlace.mk (φ i)).comap (algebraMap F E) = InfinitePlace.mk (ψ i)` using `fun i => InfinitePlace.comap_mk _ _`. Use `⟨Equiv.ofBijective e ⟨?_, ?_⟩, fun i a => (he i a).symm⟩` and prove the remaining obligations. Introduce `i j hij`. Establish `hψ : ψ i = ψ j`. Use extensionality with `a`.

Use `show φ i (a : E) = φ j (a : E)`. Rewrite using `[← he, ← he, hij]`. Establish `h1 : InfinitePlace.mk (φ i) = InfinitePlace.mk (φ j)`. Apply `(IsCMField.equivInfinitePlace E).injective` to reduce the goal to its premises. Simplify using `only [IsCMField.equivInfinitePlace_apply]`.

Rewrite using `[hplace, hplace, hψ]`. Break down `InfinitePlace.mk_eq_iff.mp h1 with h | h` into its components or cases. Take `⟨k, _, hk⟩` from `hφ (φ j)`. Conclude with `(hk i (Or.inl h.symm)).trans (hk j (Or.inl rfl)).symm`. Take `⟨k, _, hk⟩` from `hφ (φ j)`.

Conclude with `(hk i (Or.inr h.symm)).trans (hk j (Or.inl rfl)).symm`. Introduce `f`. Set `fc : F →+* ℂ` to `Complex.ofRealHom.comp f`. Establish `hfc : ComplexEmbedding.IsReal fc`. Rewrite using `[ComplexEmbedding.isReal_iff]`.

Use extensionality with `a`. Simplify using `[fc]`. Set `w : InfinitePlace E` to `(IsCMField.equivInfinitePlace E).symm (InfinitePlace.mk fc)`. Take `⟨i, hi, _⟩` from `hφ w.embedding`. Establish `hmk : InfinitePlace.mk (φ i) = w`.

Break down `hi with h | h` into its components or cases. Rewrite using `[← h, InfinitePlace.mk_embedding]`. Rewrite using `[← InfinitePlace.mk_conjugate_eq, ← h, InfinitePlace.mk_embedding]`. Establish `h2 : InfinitePlace.mk (ψ i) = InfinitePlace.mk fc`. Rewrite using `[← hplace, hmk]`.

Use `(IsCMField.equivInfinitePlace E).apply_symm_apply (InfinitePlace.mk fc)` as an intermediate fact. Rewrite `this` using `[IsCMField.equivInfinitePlace_apply]`. Conclude with `this`. Establish `h3 : ψ i = fc`. Break down `InfinitePlace.mk_eq_iff.mp h2 with h | h` into its components or cases.

Conclude with `h`. Rewrite using `[← h]`. Conclude with `((ComplexEmbedding.isReal_iff).mp (hre i)).symm`. Use `⟨i, ?_⟩` and prove the remaining obligations. Use extensionality with `a`.

Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[he]`. Use `show ψ i a = fc a`. Rewrite using `[h3]`.
-/
theorem exists_equiv (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I]
    (φ : I → E →+* ℂ) (hφ : IsCMType φ) :
    ∃ e : I ≃ Emb (maximalRealSubfield E), ∀ (i : I) (a : maximalRealSubfield E),
      φ i (a : E) = ((e i a : ℝ) : ℂ) := by
  set F := maximalRealSubfield E
  let ψ : I → F →+* ℂ := fun i => (φ i).comp (algebraMap F E)
  have hre : ∀ i, ComplexEmbedding.IsReal (ψ i) := fun i => comp_isReal (φ i)
  let e : I → Emb F := fun i => (hre i).embedding
  have he : ∀ i a, ((e i a : ℝ) : ℂ) = φ i (a : E) := fun i a =>
    (hre i).coe_embedding_apply a
  have hplace : ∀ i, (InfinitePlace.mk (φ i)).comap (algebraMap F E) = InfinitePlace.mk (ψ i) :=
    fun i => InfinitePlace.comap_mk _ _
  refine ⟨Equiv.ofBijective e ⟨?_, ?_⟩, fun i a => (he i a).symm⟩
  · intro i j hij
    have hψ : ψ i = ψ j := by
      ext a
      show φ i (a : E) = φ j (a : E)
      rw [← he, ← he, hij]
    have h1 : InfinitePlace.mk (φ i) = InfinitePlace.mk (φ j) := by
      apply (IsCMField.equivInfinitePlace E).injective
      simp only [IsCMField.equivInfinitePlace_apply]
      rw [hplace, hplace, hψ]
    rcases InfinitePlace.mk_eq_iff.mp h1 with h | h
    · obtain ⟨k, _, hk⟩ := hφ (φ j)
      exact (hk i (Or.inl h.symm)).trans (hk j (Or.inl rfl)).symm
    · obtain ⟨k, _, hk⟩ := hφ (φ j)
      exact (hk i (Or.inr h.symm)).trans (hk j (Or.inl rfl)).symm
  · intro f
    let fc : F →+* ℂ := Complex.ofRealHom.comp f
    have hfc : ComplexEmbedding.IsReal fc := by
      rw [ComplexEmbedding.isReal_iff]
      ext a
      simp [fc]
    let w : InfinitePlace E := (IsCMField.equivInfinitePlace E).symm (InfinitePlace.mk fc)
    obtain ⟨i, hi, _⟩ := hφ w.embedding
    have hmk : InfinitePlace.mk (φ i) = w := by
      rcases hi with h | h
      · rw [← h, InfinitePlace.mk_embedding]
      · rw [← InfinitePlace.mk_conjugate_eq, ← h, InfinitePlace.mk_embedding]
    have h2 : InfinitePlace.mk (ψ i) = InfinitePlace.mk fc := by
      rw [← hplace, hmk]
      have := (IsCMField.equivInfinitePlace E).apply_symm_apply (InfinitePlace.mk fc)
      rw [IsCMField.equivInfinitePlace_apply] at this
      exact this
    have h3 : ψ i = fc := by
      rcases InfinitePlace.mk_eq_iff.mp h2 with h | h
      · exact h
      · rw [← h]; exact ((ComplexEmbedding.isReal_iff).mp (hre i)).symm
    refine ⟨i, ?_⟩
    ext a
    apply Complex.ofReal_injective
    rw [he]
    show ψ i a = fc a
    rw [h3]

end GlobalTheory.CMTypeRealEmb
