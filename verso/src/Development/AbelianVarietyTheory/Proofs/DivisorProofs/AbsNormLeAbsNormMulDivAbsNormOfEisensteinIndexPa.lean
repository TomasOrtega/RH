import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

namespace GlobalTheory.NormLe

/- English proof (translation)
Use `set B : FractionalIdeal (𝓞 F)⁰ F := (𝔟 : FractionalIdeal (𝓞 F)⁰ F)`. Use `set S : FractionalIdeal (𝓞 F)⁰ F := FractionalIdeal.spanSingleton (𝓞 F)⁰ b`. Use `set J : FractionalIdeal (𝓞 F)⁰ F := ((𝔟⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) * S`. Establish `hSB : S ≤ B` using `(FractionalIdeal.spanSingleton_le_iff_mem).2 hb`. Establish `hSJ : S = B * J`.

Simplify using `only [J, B, ← mul_assoc, Units.mul_inv, one_mul]`. Establish `hJ1 : J ≤ 1`. Establish `: J ≤ ((𝔟⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) * B`. Simplify using `only [J]`. Use `gcongr`.

Simplify `this` using `[B, Units.inv_mul]`. Take `⟨I₀, hI₀⟩` from `FractionalIdeal.le_one_iff_exists_coeIdeal.1 hJ1`. Establish `hS0 : S ≠ 0`. Rewrite using `[Ne, FractionalIdeal.spanSingleton_eq_zero_iff]`. Conclude with `hb0`.

Establish `hJ0 : J ≠ 0`. Introduce and unpack `h`. Rewrite `hSJ` using `[h, mul_zero]`. Conclude with `hS0 hSJ`. Establish `hN : (1 : ℚ) ≤ FractionalIdeal.absNorm J`.

Rewrite using `[← hI₀, FractionalIdeal.coeIdeal_absNorm]`. Establish `: Ideal.absNorm I₀ ≠ 0`. Introduce `h`. Rewrite `h` using `[Ideal.absNorm_eq_zero_iff]`. Apply `hJ0` to reduce the goal to its premises.

Rewrite using `[← hI₀, h]`. Simplify using the standard rewrite rules. Conclude with `Nat.one_le_iff_ne_zero.2 this` after adjusting the coercions. Establish `key : FractionalIdeal.absNorm S = FractionalIdeal.absNorm B * FractionalIdeal.absNorm J`. Rewrite using `[hSJ, map_mul]`.

Rewrite using `[← FractionalIdeal.absNorm_span_singleton (𝓞 F) b]`. Express the relevant statement in the definitionally equal form `FractionalIdeal.absNorm B ≤ FractionalIdeal.absNorm S`. Rewrite using `[key]`. Use `FractionalIdeal.absNorm_nonneg B` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem absNorm_le_abs_norm {F : Type} [Field F] [NumberField F] (𝔟 : Frac F) {b : F}
    (hb : b ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) (hb0 : b ≠ 0) :
    FractionalIdeal.absNorm (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ≤ |Algebra.norm ℚ b| := by
  set B : FractionalIdeal (𝓞 F)⁰ F := (𝔟 : FractionalIdeal (𝓞 F)⁰ F)
  set S : FractionalIdeal (𝓞 F)⁰ F := FractionalIdeal.spanSingleton (𝓞 F)⁰ b
  set J : FractionalIdeal (𝓞 F)⁰ F := ((𝔟⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) * S
  have hSB : S ≤ B := (FractionalIdeal.spanSingleton_le_iff_mem).2 hb
  have hSJ : S = B * J := by
    simp only [J, B, ← mul_assoc, Units.mul_inv, one_mul]
  have hJ1 : J ≤ 1 := by
    have : J ≤ ((𝔟⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) * B := by
      simp only [J]; gcongr
    simpa [B, Units.inv_mul] using this
  obtain ⟨I₀, hI₀⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hJ1
  have hS0 : S ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact hb0
  have hJ0 : J ≠ 0 := by
    rintro h; rw [h, mul_zero] at hSJ; exact hS0 hSJ
  have hN : (1 : ℚ) ≤ FractionalIdeal.absNorm J := by
    rw [← hI₀, FractionalIdeal.coeIdeal_absNorm]
    have : Ideal.absNorm I₀ ≠ 0 := by
      intro h
      rw [Ideal.absNorm_eq_zero_iff] at h
      apply hJ0; rw [← hI₀, h]; simp
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  have key : FractionalIdeal.absNorm S = FractionalIdeal.absNorm B * FractionalIdeal.absNorm J := by
    rw [hSJ, map_mul]
  rw [← FractionalIdeal.absNorm_span_singleton (𝓞 F) b]
  change FractionalIdeal.absNorm B ≤ FractionalIdeal.absNorm S
  rw [key]
  have := FractionalIdeal.absNorm_nonneg B
  nlinarith

/- English proof (translation)
The claim follows from `|(Algebra.norm ℚ p.1.1 : ℝ)| ≤ |(Algebra.norm ℚ (p.1.1 * p.1.2) : ℝ)| / nrm 𝔟 := by intro F _ _ _ 𝔞 𝔟 p obtain ⟨⟨ν, b⟩, h𝔞, h𝔟, hpos⟩ := p dsimp only at h𝔞 h𝔟 hpos ⊢ obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance have τ : Emb F := w.embedding_of_isReal (IsTotallyReal.is …`.
-/
theorem main : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔞 𝔟 : Frac F) (p : QPair 𝔞 𝔟),
    |(Algebra.norm ℚ p.1.1 : ℝ)| ≤ |(Algebra.norm ℚ (p.1.1 * p.1.2) : ℝ)| / nrm 𝔟 := by
  intro F _ _ _ 𝔞 𝔟 p
  obtain ⟨⟨ν, b⟩, h𝔞, h𝔟, hpos⟩ := p
  dsimp only at h𝔞 h𝔟 hpos ⊢
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have τ : Emb F := w.embedding_of_isReal (IsTotallyReal.isReal w)
  have hνb : ν * b ≠ 0 := fun h => by have := hpos τ; rw [h, map_zero] at this; exact lt_irrefl _ this
  have hb0 : b ≠ 0 := right_ne_zero_of_mul hνb
  have hle := absNorm_le_abs_norm 𝔟 h𝔟 hb0
  have hB0 : (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := 𝔟.ne_zero
  have hnpos : 0 < nrm 𝔟 := by
    unfold nrm
    have h1 := FractionalIdeal.absNorm_nonneg (𝔟 : FractionalIdeal (𝓞 F)⁰ F)
    have h2 : FractionalIdeal.absNorm (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 :=
      fun h => hB0 (FractionalIdeal.absNorm_eq_zero_iff.1 h)
    exact_mod_cast lt_of_le_of_ne h1 (Ne.symm h2)
  have hle' : nrm 𝔟 ≤ |(Algebra.norm ℚ b : ℝ)| := by
    unfold nrm; rw [← Rat.cast_abs]; exact_mod_cast hle
  rw [le_div_iff₀ hnpos, map_mul, Rat.cast_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left hle' (abs_nonneg _)

end GlobalTheory.NormLe
