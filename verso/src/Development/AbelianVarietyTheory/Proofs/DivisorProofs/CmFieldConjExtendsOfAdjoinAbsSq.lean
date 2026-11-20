import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

/- English proof (translation)
Introduce `F M _ _ _ _ _ _ π c hadj hc hπ`. Establish `gen : ∀ S : Subring M, (∀ x : F, algebraMap F M x ∈ S) → π ∈ S → ∀ y : M, y ∈ S`. Introduce `S hS hpS y`. Set `A : Subalgebra F M` to `{ S with algebraMap_mem' := hS }`. Establish `hle : Algebra.adjoin F {π} ≤ A` using `Algebra.adjoin_le (Set.singleton_subset_iff.mpr (show π ∈ A from hpS))`.

Rewrite `hle` using `[hadj]`. Conclude with `hle (Algebra.mem_top (x := y))`. Establish `hconj : ∀ φ : M →+* ℂ, φ π ≠ 0 ∧ (starRingEnd ℂ) (φ π) = φ ((c : M) / π)`. Introduce `φ`. Establish `hn : Complex.normSq (φ π) = (c : ℝ)` using `by rw [← Complex.sq_norm]; exact hπ φ`.

Establish `hne : φ π ≠ 0`. Introduce `h0`. Rewrite `hn` using `[h0, map_zero]`. Conclude with `hc (by exact_mod_cast hn.symm)`. Use `⟨hne, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_div₀, map_ratCast, eq_div_iff hne, mul_comm, Complex.mul_conj, hn]`. Use `norm_cast`. Take `⟨φ₀⟩ : Nonempty (M →+* ℂ)` from `inferInstance`. Set `ψ : M →+* ℂ` to `(starRingEnd ℂ).comp φ₀`. Establish `hrange : ∀ y : M, ψ y ∈ φ₀.range`.

Use `gen (Subring.comap ψ φ₀.range) ?_ ?_` and prove the remaining obligations. Introduce `x show ψ (algebraMap F M x) ∈ φ₀.range`. Use `⟨algebraMap F M (IsCMField.complexConj F x), ?_⟩` and prove the remaining obligations. Conclude with `(IsCMField.complexEmbedding_complexConj F (φ₀.comp (algebraMap F M)) x)`. Use `show ψ π ∈ φ₀.range`.

Conclude with `⟨(c : M) / π, ((hconj φ₀).2).symm⟩`. Set `e : M ≃+* φ₀.range` to `RingEquiv.ofBijective φ₀.rangeRestrict ⟨fun a b h => φ₀.injective (congrArg Subtype.val h), φ₀.rangeRestrict_surjective⟩`. Set `σ : M →+* M` to `e.symm.toRingHom.comp (ψ.codRestrict φ₀.range hrange)`. Establish `hσ0 : ∀ x : M, φ₀ (σ x) = (starRingEnd ℂ) (φ₀ x)`. Introduce `x`.

Establish `h1 : e (σ x) = ψ.codRestrict φ₀.range hrange x` using `by simp [σ]`. Establish `h2 : ((e (σ x) : φ₀.range) : ℂ) = ((ψ.codRestrict φ₀.range hrange x : φ₀.range) : ℂ)` using `congrArg Subtype.val h1`. Conclude with `h2`. Establish `hσF : ∀ x : F, σ (algebraMap F M x) = algebraMap F M (IsCMField.complexConj F x)`. Introduce `x`.

Apply `φ₀.injective` to reduce the goal to its premises. Rewrite using `[hσ0]`. Conclude with `(IsCMField.complexEmbedding_complexConj F (φ₀.comp (algebraMap F M)) x).symm`. Establish `hσπ : σ π = (c : M) / π`. Apply `φ₀.injective` to reduce the goal to its premises.

Rewrite using `[hσ0]`. Conclude with `(hconj φ₀).2`. Establish `hπ0 : π ≠ 0` using `fun h => (hconj φ₀).1 (by rw [h, map_zero])`. Use `⟨σ, hσF, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hσπ, div_mul_cancel₀ _ hπ0]`.

Introduce `φ`. Use `gen (RingHom.eqLocus (φ.comp σ) ((starRingEnd ℂ).comp φ)) ?_ ?_` as an intermediate fact. Introduce `x`. Conclude with `this x`. Introduce `x show φ (σ (algebraMap F M x)) = (starRingEnd ℂ) (φ (algebraMap F M x))`.

Rewrite using `[hσF]`. Conclude with `IsCMField.complexEmbedding_complexConj F (φ.comp (algebraMap F M)) x`. Use `show φ (σ π) = (starRingEnd ℂ) (φ π)`. Rewrite using `[hσπ]`. Conclude with `((hconj φ).2).symm`.
-/
theorem cm_conj_extends_of_adjoin :
    ∀ (F M : Type) [Field F] [NumberField F] [IsCMField F] [Field M] [NumberField M] [Algebra F M]
      (π : M) (c : ℚ), Algebra.adjoin F {π} = ⊤ → c ≠ 0 → (∀ φ : M →+* ℂ, ‖φ π‖ ^ 2 = (c : ℝ)) →
      ∃ σ : M →+* M, (∀ x : F, σ (algebraMap F M x) = algebraMap F M (IsCMField.complexConj F x)) ∧
        σ π * π = (c : M) ∧ ∀ (φ : M →+* ℂ) (x : M), φ (σ x) = (starRingEnd ℂ) (φ x) := by
  intro F M _ _ _ _ _ _ π c hadj hc hπ

  have gen : ∀ S : Subring M, (∀ x : F, algebraMap F M x ∈ S) → π ∈ S → ∀ y : M, y ∈ S := by
    intro S hS hpS y
    let A : Subalgebra F M := { S with algebraMap_mem' := hS }
    have hle : Algebra.adjoin F {π} ≤ A := Algebra.adjoin_le (Set.singleton_subset_iff.mpr (show π ∈ A from hpS))
    rw [hadj] at hle
    exact hle (Algebra.mem_top (x := y))

  have hconj : ∀ φ : M →+* ℂ, φ π ≠ 0 ∧ (starRingEnd ℂ) (φ π) = φ ((c : M) / π) := by
    intro φ
    have hn : Complex.normSq (φ π) = (c : ℝ) := by rw [← Complex.sq_norm]; exact hπ φ
    have hne : φ π ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hn
      exact hc (by exact_mod_cast hn.symm)
    refine ⟨hne, ?_⟩
    rw [map_div₀, map_ratCast, eq_div_iff hne, mul_comm, Complex.mul_conj, hn]
    norm_cast
  obtain ⟨φ₀⟩ : Nonempty (M →+* ℂ) := inferInstance
  let ψ : M →+* ℂ := (starRingEnd ℂ).comp φ₀
  have hrange : ∀ y : M, ψ y ∈ φ₀.range := by
    refine gen (Subring.comap ψ φ₀.range) ?_ ?_
    · intro x
      show ψ (algebraMap F M x) ∈ φ₀.range
      refine ⟨algebraMap F M (IsCMField.complexConj F x), ?_⟩
      exact (IsCMField.complexEmbedding_complexConj F (φ₀.comp (algebraMap F M)) x)
    · show ψ π ∈ φ₀.range
      exact ⟨(c : M) / π, ((hconj φ₀).2).symm⟩
  let e : M ≃+* φ₀.range := RingEquiv.ofBijective φ₀.rangeRestrict
    ⟨fun a b h => φ₀.injective (congrArg Subtype.val h), φ₀.rangeRestrict_surjective⟩
  let σ : M →+* M := e.symm.toRingHom.comp (ψ.codRestrict φ₀.range hrange)
  have hσ0 : ∀ x : M, φ₀ (σ x) = (starRingEnd ℂ) (φ₀ x) := by
    intro x
    have h1 : e (σ x) = ψ.codRestrict φ₀.range hrange x := by simp [σ]
    have h2 : ((e (σ x) : φ₀.range) : ℂ) = ((ψ.codRestrict φ₀.range hrange x : φ₀.range) : ℂ) := congrArg Subtype.val h1
    exact h2
  have hσF : ∀ x : F, σ (algebraMap F M x) = algebraMap F M (IsCMField.complexConj F x) := by
    intro x
    apply φ₀.injective
    rw [hσ0]
    exact (IsCMField.complexEmbedding_complexConj F (φ₀.comp (algebraMap F M)) x).symm
  have hσπ : σ π = (c : M) / π := by
    apply φ₀.injective
    rw [hσ0]; exact (hconj φ₀).2
  have hπ0 : π ≠ 0 := fun h => (hconj φ₀).1 (by rw [h, map_zero])
  refine ⟨σ, hσF, ?_, ?_⟩
  · rw [hσπ, div_mul_cancel₀ _ hπ0]
  · intro φ
    have := gen (RingHom.eqLocus (φ.comp σ) ((starRingEnd ℂ).comp φ)) ?_ ?_
    · intro x; exact this x
    · intro x
      show φ (σ (algebraMap F M x)) = (starRingEnd ℂ) (φ (algebraMap F M x))
      rw [hσF]
      exact IsCMField.complexEmbedding_complexConj F (φ.comp (algebraMap F M)) x
    · show φ (σ π) = (starRingEnd ℂ) (φ π)
      rw [hσπ]; exact ((hconj φ).2).symm

end GlobalTheory
