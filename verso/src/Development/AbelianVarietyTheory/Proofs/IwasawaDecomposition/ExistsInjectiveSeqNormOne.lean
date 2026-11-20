import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DisjointSpanPerpLat

namespace GlobalTheory.InjectiveSeqNormOne

/- English proof (translation)
Take `⟨-, hE, -, hσ⟩` from `h`. Set `τ : E →+* ℂ` to `(IsAlgClosed.lift (R := ℚ) (S := E) (M := ℂ)).toRingHom`. Establish `hinv : ∀ x, σ (σ x) = x` using `fun x => τ.injective (by rw [hσ, hσ, star_star])`. Establish `hy : ∃ y, σ y ≠ y`. Assume the negation of the conclusion as `hcon`.

Use `push Not at hcon`. Establish `hc : (NumberField.InfinitePlace.mk τ).IsComplex` using `hE.isComplex _`. Rewrite `hc` using `[NumberField.InfinitePlace.isComplex_mk_iff]`. Apply `hc` to reduce the goal to its premises. Rewrite using `[NumberField.ComplexEmbedding.isReal_iff]`.

Use extensionality with `x`. Use `hσ τ x` as an intermediate fact. Rewrite `this` using `[hcon]`. Rewrite using `[NumberField.ComplexEmbedding.conjugate_coe_eq]`. Conclude with `this.symm`.

Take `⟨y, hy⟩` from `hy`. Establish `h1 : ∀ k : ℕ, (k : E) + y ≠ 0`. Introduce `k hk`. Apply `hy` to reduce the goal to its premises. Establish `: y = -(k : E)` using `by linear_combination hk`.

Rewrite using `[this, map_neg, map_natCast]`. Establish `h2 : ∀ k : ℕ, (k : E) + σ y ≠ 0`. Introduce `k hk`. Apply `h1 k` to reduce the goal to its premises. Use `congrArg σ hk` as an intermediate fact.

Rewrite `this` using `[map_add, map_natCast, hinv, map_zero]`. Then use the resulting hypothesis. Use `⟨fun k => ((k : E) + y) / ((k : E) + σ y), ?_, ?_⟩` and prove the remaining obligations. Introduce `k m hkm`. Establish `hkm'` using `(div_eq_div_iff (h2 k) (h2 m)).1 hkm`. Establish `h3 : ((k : E) - m) * (σ y - y) = 0` using `by linear_combination hkm'`.

Break down `mul_eq_zero.1 h3 with h4 | h4` into its components or cases. Conclude with `sub_eq_zero.1 h4` after adjusting the coercions. Conclude with `absurd (sub_eq_zero.1 h4) hy`. Introduce `k`. Establish `a1` using `h1 k`.

Establish `a2` using `h2 k`. Simplify using `only [map_div₀, map_add, map_natCast, hinv]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_injective_seq_norm_one {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) :
    ∃ a : ℕ → E, Function.Injective a ∧ ∀ k : ℕ, a k * σ (a k) = 1 := by
  obtain ⟨-, hE, -, hσ⟩ := h
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := E) (M := ℂ)).toRingHom
  have hinv : ∀ x, σ (σ x) = x := fun x => τ.injective (by rw [hσ, hσ, star_star])
  have hy : ∃ y, σ y ≠ y := by
    by_contra hcon
    push Not at hcon
    have hc : (NumberField.InfinitePlace.mk τ).IsComplex := hE.isComplex _
    rw [NumberField.InfinitePlace.isComplex_mk_iff] at hc
    apply hc
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    have := hσ τ x
    rw [hcon] at this
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
    exact this.symm
  obtain ⟨y, hy⟩ := hy
  have h1 : ∀ k : ℕ, (k : E) + y ≠ 0 := by
    intro k hk
    apply hy
    have : y = -(k : E) := by linear_combination hk
    rw [this, map_neg, map_natCast]
  have h2 : ∀ k : ℕ, (k : E) + σ y ≠ 0 := by
    intro k hk
    apply h1 k
    have := congrArg σ hk
    rwa [map_add, map_natCast, hinv, map_zero] at this
  refine ⟨fun k => ((k : E) + y) / ((k : E) + σ y), ?_, ?_⟩
  · intro k m hkm
    have hkm' := (div_eq_div_iff (h2 k) (h2 m)).1 hkm
    have h3 : ((k : E) - m) * (σ y - y) = 0 := by linear_combination hkm'
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact_mod_cast sub_eq_zero.1 h4
    · exact absurd (sub_eq_zero.1 h4) hy
  · intro k
    have a1 := h1 k
    have a2 := h2 k
    simp only [map_div₀, map_add, map_natCast, hinv]
    field_simp

end GlobalTheory.InjectiveSeqNormOne
