import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

/- English proof (translation)
Introduce `E _ _ _ A n τ i`. Establish `hcim : ∀ σ : E →+* ℂ, (σ (A.c : E)).im = 0`. Introduce `σ`. Establish `h1 : σ ((A.bar A.c : 𝓞 E) : E) = (starRingEnd ℂ) (σ (A.c : E))`. Rewrite using `[A.bar_eq, IsCMField.complexEmbedding_complexConj]`.

Rewrite `h1` using `[A.c_real]`. Conclude with `Complex.conj_eq_iff_im.mp h1.symm`. Establish `hre : InfinitePlace.mk τ = InfinitePlace.mk A.τ₀ → (τ (A.c : E)).re < 0`. Introduce `h`. Break down `InfinitePlace.mk_eq_iff.mp h with h' | h'` into its components or cases.

Rewrite using `[h']`. Conclude with `A.c_neg`. Establish `h2` using `A.c_neg`. Rewrite `h2` using `[← h', NumberField.ComplexEmbedding.conjugate_coe_eq]`. Simplify using `using h2`.

Establish `hδ : (τ A.δ).re = 0`. Establish `h1 : τ ((IsCMField.complexConj E) A.δ) = (starRingEnd ℂ) (τ A.δ)` using `IsCMField.complexEmbedding_complexConj E τ A.δ`. Rewrite `h1` using `[A.δ_im, map_neg]`. Establish `h2` using `congrArg Complex.re h1`. Simplify using `at h2`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hc` using `hcim τ`. Use `⟨?_, hδ, ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `simp only [Arith.hd, Arith.dg] split_ifs <;> simp [Complex.mul_im, hc]`. Introduce and unpack `⟨h, hi0⟩`.

Establish `hr` using `hre h`. Simplify using `only [Arith.hd, Arith.dg, if_pos hi0]`. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `hn`.

Distinguish the cases in `hp : InfinitePlace.mk τ = InfinitePlace.mk A.τ₀`. Establish `hi : (i : ℕ) ≠ 0` using `fun hi0 => hn ⟨hp, hi0⟩`. Establish `hr` using `hre hp`. Simplify using `only [Arith.hd, Arith.dg, if_neg hi]`. Simplify using `[Complex.mul_re, hc]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hr : 0 < (τ (A.c : E)).re` using `A.c_pos τ hp`. Simplify using `only [Arith.hd, Arith.dg]`. Use `split_ifs`. Simplify using the standard rewrite rules.

Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `[Complex.mul_re, hc]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem UpperTheory.Gal.W2.Seed.pHdSign :
    HdSign := by
  intro E _ _ _ A n τ i
  have hcim : ∀ σ : E →+* ℂ, (σ (A.c : E)).im = 0 := by
    intro σ
    have h1 : σ ((A.bar A.c : 𝓞 E) : E) = (starRingEnd ℂ) (σ (A.c : E)) := by
      rw [A.bar_eq, IsCMField.complexEmbedding_complexConj]
    rw [A.c_real] at h1
    exact Complex.conj_eq_iff_im.mp h1.symm
  have hre : InfinitePlace.mk τ = InfinitePlace.mk A.τ₀ → (τ (A.c : E)).re < 0 := by
    intro h
    rcases InfinitePlace.mk_eq_iff.mp h with h' | h'
    · rw [h']
      exact A.c_neg
    · have h2 := A.c_neg
      rw [← h', NumberField.ComplexEmbedding.conjugate_coe_eq] at h2
      simpa using h2
  have hδ : (τ A.δ).re = 0 := by
    have h1 : τ ((IsCMField.complexConj E) A.δ) = (starRingEnd ℂ) (τ A.δ) :=
      IsCMField.complexEmbedding_complexConj E τ A.δ
    rw [A.δ_im, map_neg] at h1
    have h2 := congrArg Complex.re h1
    simp at h2
    linarith
  have hc := hcim τ
  refine ⟨?_, hδ, ?_, ?_⟩
  · simp only [Arith.hd, Arith.dg]
    split_ifs <;> simp [Complex.mul_im, hc]
  · rintro ⟨h, hi0⟩
    have hr := hre h
    simp only [Arith.hd, Arith.dg, if_pos hi0]
    simp
    linarith
  · intro hn
    by_cases hp : InfinitePlace.mk τ = InfinitePlace.mk A.τ₀
    · have hi : (i : ℕ) ≠ 0 := fun hi0 => hn ⟨hp, hi0⟩
      have hr := hre hp
      simp only [Arith.hd, Arith.dg, if_neg hi]
      simp [Complex.mul_re, hc]
      nlinarith
    · have hr : 0 < (τ (A.c : E)).re := A.c_pos τ hp
      simp only [Arith.hd, Arith.dg]
      split_ifs
      · simp
        linarith
      · simp [Complex.mul_re, hc]
        nlinarith
