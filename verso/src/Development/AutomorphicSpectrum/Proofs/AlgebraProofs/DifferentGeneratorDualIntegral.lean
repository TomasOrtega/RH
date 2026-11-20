import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open Module NumberField
open scoped nonZeroDivisors

section

variable (E : Type) [Field E] [NumberField E]

/- English proof (translation)
Establish `h` using `Submodule.traceDual_span_of_basis ℤ (1 : Submodule (𝓞 E) E) (integralBasis E) (by`. Use extensionality with `x`. Rewrite using `[Submodule.restrictScalars_mem, mem_span_integralBasis, Submodule.mem_one]`. Use the proof step `rfl)`. Establish `h2 : y ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔ y ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E)`.

Rewrite using `[← FractionalIdeal.mem_coe, FractionalIdeal.coe_dual_one]`. Rewrite using `[h2, ← Submodule.restrictScalars_mem ℤ, h]`. Establish `: (⇑(integralBasis E).traceDual) = dualInt E`. Use function extensionality and compare the values at `k`. Unfold `dualInt Module.Basis.traceDual`.

Use `congr!`. Rewrite using `[this]`.
-/
theorem mem_dual_one_iff_span_dualInt (y : E) :
    y ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔
      y ∈ Submodule.span ℤ (Set.range (dualInt E)) := by
  classical
  have h := Submodule.traceDual_span_of_basis ℤ (1 : Submodule (𝓞 E) E) (integralBasis E) (by
    ext x
    rw [Submodule.restrictScalars_mem, mem_span_integralBasis, Submodule.mem_one]
    rfl)
  have h2 : y ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔
      y ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_dual_one]
  rw [h2, ← Submodule.restrictScalars_mem ℤ, h]
  have : (⇑(integralBasis E).traceDual) = dualInt E := by
    funext k
    unfold dualInt Module.Basis.traceDual
    congr!
  rw [this]

/- English proof (translation)
Rewrite using `[coeIdeal_differentIdeal ℤ ℚ, inv_mul_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ (one_ne_zero (α := FractionalIdeal (𝓞 E)⁰ E)))]`.
-/
theorem different_mul_dual_one :
    ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) *
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) = 1 := by
  rw [coeIdeal_differentIdeal ℤ ℚ, inv_mul_cancel₀
    (FractionalIdeal.dual_ne_zero ℤ ℚ (one_ne_zero (α := FractionalIdeal (𝓞 E)⁰ E)))]

/- English proof (translation)
Establish `h1 : dualInt E k ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)` using `(mem_dual_one_iff_span_dualInt E _).2 (Submodule.subset_span ⟨k, rfl⟩)`. Establish `h2 : (x : E) ∈ ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)` using `FractionalIdeal.mem_coeIdeal_of_mem _ hx`. Establish `h3` using `FractionalIdeal.mul_mem_mul h2 h1`. Rewrite `h3` using `[different_mul_dual_one, FractionalIdeal.mem_one_iff]`. Conclude with `h3`.
-/
theorem exists_different_mul_dualInt (x : 𝓞 E) (hx : x ∈ differentIdeal ℤ (𝓞 E))
    (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    ∃ z : 𝓞 E, (z : E) = (x : E) * dualInt E k := by
  have h1 : dualInt E k ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) :=
    (mem_dual_one_iff_span_dualInt E _).2 (Submodule.subset_span ⟨k, rfl⟩)
  have h2 : (x : E) ∈ ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) :=
    FractionalIdeal.mem_coeIdeal_of_mem _ hx
  have h3 := FractionalIdeal.mul_mem_mul h2 h1
  rw [different_mul_dual_one, FractionalIdeal.mem_one_iff] at h3
  exact h3

end

/- English proof (translation)
Introduce `A K _ _ _ _ E _ _ σ d _ hσ hd`. Establish `key : ∃ u : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → A, ∑ k, algebraMap A K (u k) * (algebraMap A K d * σ (dualInt E k)) = 1` using `by set M : Submodule A K := Submodule.span A (Set.range fun k => algebraMap A K d * σ (dualInt E k)) with hM`. Establish `hy : ∀ y ∈ Submodule.span ℤ (Set.range (dualInt E)), algebraMap A K d * σ y ∈ M`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem y hy`. Take `⟨k, rfl⟩` from `hy`. Conclude with `Submodule.subset_span ⟨k, rfl⟩`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [map_add, mul_add]`.

Conclude with `M.add_mem ha hb`. Consider the case `smul n a _ ha`. Rewrite using `[map_zsmul, mul_smul_comm]`. Conclude with `zsmul_mem ha n`. Establish `h1 : (1 : E) ∈ ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) * FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)`.

Rewrite using `[different_mul_dual_one]`. Conclude with `FractionalIdeal.one_mem_one _`. Establish `h2 : σ 1 ∈ M`. Use `FractionalIdeal.mul_induction_on (C := fun z => σ z ∈ M) h1 ?_ ?_` and prove the remaining obligations. Introduce `x hx y hy'`.

Take `⟨x, hx0, rfl⟩` from `(FractionalIdeal.mem_coeIdeal _).1 hx`. Establish `hx' : σ (x : E) ∈ Submodule.span A {algebraMap A K d}`. Rewrite using `[hd]`. Conclude with `Submodule.subset_span ⟨x, hx0, rfl⟩`. Take `⟨a, ha⟩` from `Submodule.mem_span_singleton.1 hx'`.

Express the relevant statement in the definitionally equal form `σ ((x : E) * y) ∈ M`. Rewrite using `[map_mul, ← ha, smul_mul_assoc]`. Conclude with `M.smul_mem a (hy y ((mem_dual_one_iff_span_dualInt E y).1 hy'))`. Introduce `x y hx hy`. Rewrite using `[map_add]`.

Conclude with `M.add_mem hx hy`. Rewrite `h2` using `[map_one, hM, Submodule.mem_span_range_iff_exists_fun]`. Take `⟨u, hu⟩` from `h2`. Conclude with `⟨u, by simpa only [Algebra.smul_def] using hu⟩`. Use `⟨?_, ?_, key⟩` and prove the remaining obligations.

Introduce `h0`. Take `⟨u, hu⟩` from `key`. Simplify using `[h0] at hu`. Introduce `k`. Establish `hy : ∀ y ∈ Submodule.span A {y : K | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)}, y * σ (dualInt E k) ∈ (algebraMap A K).range`.

Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨x, hx, rfl⟩` from `hy`. Take `⟨z, hz⟩` from `exists_different_mul_dualInt E x hx k`.

Rewrite using `[← map_mul, ← hz]`. Conclude with `hσ z`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [add_mul]`. Conclude with `add_mem ha hb`.

Consider the case `smul n a _ ha`. Rewrite using `[smul_mul_assoc, Algebra.smul_def]`. Conclude with `mul_mem ⟨n, rfl⟩ ha`. Conclude with `hy _ (hd ▸ Submodule.mem_span_singleton_self _)`.
-/
theorem different_generator_dualInt :
    ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (E : Type) [Field E]
      [NumberField E] (σ : E →+* K) (d : A), Function.Injective (algebraMap A K) →
      (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) →
      Submodule.span A {algebraMap A K d} =
        Submodule.span A {y : K | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)} →
      algebraMap A K d ≠ 0 ∧
        (∀ k, algebraMap A K d * σ (dualInt E k) ∈ (algebraMap A K).range) ∧
        ∃ u : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → A,
          ∑ k, algebraMap A K (u k) * (algebraMap A K d * σ (dualInt E k)) = 1 := by
  intro A K _ _ _ _ E _ _ σ d _ hσ hd
  have key : ∃ u : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → A,
      ∑ k, algebraMap A K (u k) * (algebraMap A K d * σ (dualInt E k)) = 1 := by
    set M : Submodule A K :=
      Submodule.span A (Set.range fun k => algebraMap A K d * σ (dualInt E k)) with hM
    have hy : ∀ y ∈ Submodule.span ℤ (Set.range (dualInt E)), algebraMap A K d * σ y ∈ M := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨k, rfl⟩ := hy
        exact Submodule.subset_span ⟨k, rfl⟩
      | zero => simp
      | add a b _ _ ha hb => rw [map_add, mul_add]; exact M.add_mem ha hb
      | smul n a _ ha =>
        rw [map_zsmul, mul_smul_comm]
        exact zsmul_mem ha n
    have h1 : (1 : E) ∈ ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) *
        FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
      rw [different_mul_dual_one]
      exact FractionalIdeal.one_mem_one _
    have h2 : σ 1 ∈ M := by
      refine FractionalIdeal.mul_induction_on (C := fun z => σ z ∈ M) h1 ?_ ?_
      · intro x hx y hy'
        obtain ⟨x, hx0, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
        have hx' : σ (x : E) ∈ Submodule.span A {algebraMap A K d} := by
          rw [hd]; exact Submodule.subset_span ⟨x, hx0, rfl⟩
        obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hx'
        change σ ((x : E) * y) ∈ M
        rw [map_mul, ← ha, smul_mul_assoc]
        exact M.smul_mem a (hy y ((mem_dual_one_iff_span_dualInt E y).1 hy'))
      · intro x y hx hy
        rw [map_add]; exact M.add_mem hx hy
    rw [map_one, hM, Submodule.mem_span_range_iff_exists_fun] at h2
    obtain ⟨u, hu⟩ := h2
    exact ⟨u, by simpa only [Algebra.smul_def] using hu⟩
  refine ⟨?_, ?_, key⟩
  · intro h0
    obtain ⟨u, hu⟩ := key
    simp [h0] at hu
  · intro k
    have hy : ∀ y ∈ Submodule.span A {y : K | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)},
        y * σ (dualInt E k) ∈ (algebraMap A K).range := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨x, hx, rfl⟩ := hy
        obtain ⟨z, hz⟩ := exists_different_mul_dualInt E x hx k
        rw [← map_mul, ← hz]
        exact hσ z
      | zero => simp
      | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
      | smul n a _ ha =>
        rw [smul_mul_assoc, Algebra.smul_def]
        exact mul_mem ⟨n, rfl⟩ ha
    exact hy _ (hd ▸ Submodule.mem_span_singleton_self _)

end GlobalTheory.CompanionTheory.Ar.HT
