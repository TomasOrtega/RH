import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

section
variable {F E : Type} [Field F] [Field E] [Algebra F E] {δ : F} {θ : E} {σ : E ≃ₐ[F] E}

/- English proof (translation)
Rewrite using `[map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, h.conj]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem IsQuad.conj_coord (h : IsQuad δ θ σ) (a b : F) :
    σ (algebraMap F E a + algebraMap F E b * θ) = algebraMap F E a - algebraMap F E b * θ := by
  rw [map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, h.conj]; ring

open NumberField IsDedekindDomain in
open scoped WithZero in
variable {F E : Type} [Field F] [Field E] [Algebra F E] {δ : F} {θ : E} {σ : E ≃ₐ[F] E} in
/- English proof (translation)
Establish `hb : b = 0`. Assume the negation of the conclusion as `hb`. Apply `h.nonsq` to reduce the goal to its premises. Use `⟨-a / b, (algebraMap F E).injective ?_⟩` and prove the remaining obligations. Establish `hb' : algebraMap F E b ≠ 0` using `(map_ne_zero _).2 hb`.

Establish `hθ : θ = -algebraMap F E a / algebraMap F E b`. Clear the denominators using the available nonvanishing facts. Take the linear combination `hab`. Rewrite using `[← h.sq, hθ]`. Simplify using `[map_div₀, map_neg]`.

Expand and normalize the polynomial expressions, which then agree. Substitute `hb` using the available equality. Use `⟨(algebraMap F E).injective ?_, rfl⟩` and prove the remaining obligations. Simplify using `using hab`.
-/
theorem _root_.GlobalTheory.QNorm.IsQuad.coord_indep
    (h : _root_.GlobalTheory.QNorm.IsQuad δ θ σ) (a b : F)
    (hab : algebraMap F E a + algebraMap F E b * θ = 0) : a = 0 ∧ b = 0 := by
  have hb : b = 0 := by
    by_contra hb
    apply h.nonsq
    refine ⟨-a / b, (algebraMap F E).injective ?_⟩
    have hb' : algebraMap F E b ≠ 0 := (map_ne_zero _).2 hb
    have hθ : θ = -algebraMap F E a / algebraMap F E b := by
      field_simp
      linear_combination hab
    rw [← h.sq, hθ]
    simp [map_div₀, map_neg]
    ring
  subst hb
  refine ⟨(algebraMap F E).injective ?_, rfl⟩
  simpa using hab

open NumberField IsDedekindDomain in
open scoped WithZero in
variable {F E : Type} [Field F] [Field E] [Algebra F E] {δ : F} {θ : E} {σ : E ≃ₐ[F] E} in
/- English proof (translation)
Introduce `hθ`. Apply `h.nonsq` to reduce the goal to its premises. Use `⟨0, (algebraMap F E).injective ?_⟩` and prove the remaining obligations. Rewrite using `[← h.sq, hθ]`. Simplify using the standard rewrite rules.
-/
theorem _root_.GlobalTheory.QNorm.IsQuad.root_ne_zero (h : _root_.GlobalTheory.QNorm.IsQuad δ θ σ) :
    θ ≠ 0 := by
  intro hθ
  apply h.nonsq
  refine ⟨0, (algebraMap F E).injective ?_⟩
  rw [← h.sq, hθ]
  simp

/- English proof (translation)
Take `⟨a, b, rfl⟩` from `h.span x`. Rewrite using `[h.conj_coord, map_sub, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, h.conj]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem IsQuad.conj_conj (h : IsQuad δ θ σ) (x : E) : σ (σ x) = x := by
  obtain ⟨a, b, rfl⟩ := h.span x
  rw [h.conj_coord, map_sub, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, h.conj]; ring

/- English proof (translation)
Establish `hli : LinearIndependent F ![(1 : E), θ]`. Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t hst`. Apply `h.coord_indep` to reduce the goal to its premises. Simplify `hst` using `[Algebra.smul_def]`.

Establish `hsp : ⊤ ≤ Submodule.span F (Set.range ![(1 : E), θ])`. Introduce `x _`. Take `⟨a, b, rfl⟩` from `h.span x`. Use `Submodule.add_mem _ ?_ ?_` and prove the remaining obligations. Rewrite using `[Algebra.algebraMap_eq_smul_one]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)`. Rewrite using `[← Algebra.smul_def]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)`. Simplify using `using Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)`.
-/
theorem IsQuad.finrank_eq_two (h : IsQuad δ θ σ) : Module.finrank F E = 2 := by
  have hli : LinearIndependent F ![(1 : E), θ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    apply h.coord_indep
    simpa [Algebra.smul_def] using hst
  have hsp : ⊤ ≤ Submodule.span F (Set.range ![(1 : E), θ]) := by
    intro x _
    obtain ⟨a, b, rfl⟩ := h.span x
    refine Submodule.add_mem _ ?_ ?_
    · rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
    · rw [← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)
  simpa using Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)

end

open NumberField IsDedekindDomain in
open scoped WithZero in

/- English proof (translation)
Introduce `F E _ _ _ _ δ θ σ h`. Establish `t1` using `h.coord_indep`. Establish `hθ` using `h.root_ne_zero`. Establish `hc` using `h.conj`. Establish `hs` using `h.sq`.

Use `⟨?_, ?_, t1, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x`. Take `⟨a, b, rfl⟩` from `h.span x`. Simplify using `[AlgEquiv.commutes, hc]`. Introduce `x hx`.

Take `⟨a, b, rfl⟩` from `h.span x`. Simplify using `only [map_add, map_mul, AlgEquiv.commutes, hc] at hx`. Use `t1 0 (2 * b) (by simp only [map_zero, map_mul, map_ofNat]; linear_combination -hx)` as an intermediate fact. Establish `hb : b = 0` using `by simpa using this.2`. Conclude with `⟨a, by simp [hb]⟩`.

Introduce `x`. Take `⟨a, b, rfl⟩` from `h.span x`. Use `⟨a, b, ?_⟩` and prove the remaining obligations. Simplify using `only [map_add, map_mul, AlgEquiv.commutes, hc, map_sub, map_pow]`. Take the linear combination `(-(algebraMap F E b) ^ 2) * hs`.

Introduce `x hx`. Distinguish the cases in `h1 : x = -1`. Use `⟨θ, hθ, ?_⟩` and prove the remaining obligations. Rewrite using `[hc, h1, div_neg, div_self hθ]`. Establish `hy : (1 + x) ≠ 0` using `fun h0 => h1 (by linear_combination h0)`.

Establish `hσy : σ (1 + x) ≠ 0`. Rewrite using `[ne_eq, map_eq_zero_iff _ σ.injective]` and apply the resulting hypothesis. Use `⟨1 + x, hy, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_div_iff hσy, map_add, map_one]`. Take the linear combination `hx`.

Introduce and unpack `u ⟨y, hy⟩`. Take `⟨a, b, rfl⟩` from `h.span y`. Use `t1 (u - a ^ 2 - b ^ 2 * δ) (-(2 * a * b)) (by` as an intermediate fact. Simplify using `only [map_sub, map_mul, map_pow, map_neg, map_ofNat]`. Take the linear combination `hy + (algebraMap F E b) ^ 2 * hs)`.

Establish `h2 : a * b = 0`. Establish `h3` using `this.2`. Establish `h4 : (2 : F) * (a * b) = 0` using `by linear_combination -h3`. Simplify using `using h4`. Establish `hu : u = a ^ 2 + b ^ 2 * δ` using `by linear_combination this.1`.

Break down `mul_eq_zero.1 h2 with ha | hb` into its components or cases. Use the proof step `right; exact ⟨b * δ, by rw [hu, ha]; ring⟩`. Use the proof step `left; exact ⟨a, by rw [hu, hb]; ring⟩`. Establish `hli : LinearIndependent F ![(1 : E), θ]`. Rewrite using `[LinearIndependent.pair_iff]`.

Introduce `s t hst`. Apply `t1` to reduce the goal to its premises. Simplify `hst` using `[Algebra.smul_def]`. Establish `hsp : ⊤ ≤ Submodule.span F (Set.range ![(1 : E), θ])`. Introduce `x _`.

Take `⟨a, b, rfl⟩` from `h.span x`. Rewrite using `[Matrix.range_cons_cons_empty]`. Use `Submodule.mem_span_pair.2 ⟨a, b, ?_⟩` and prove the remaining obligations. Simplify using `[Algebra.smul_def]`. Simplify using `using Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)`.
-/
theorem _root_.GlobalTheory.QNorm.isQuad_basic : ∀ (F E : Type) [Field F] [CharZero F] [Field E]
    [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), _root_.GlobalTheory.QNorm.IsQuad δ θ σ →
    (∀ x, σ (σ x) = x) ∧ (∀ x, σ x = x → ∃ a : F, x = algebraMap F E a) ∧
    (∀ a b : F, algebraMap F E a + algebraMap F E b * θ = 0 → a = 0 ∧ b = 0) ∧
    (∀ x : E, ∃ a b : F, x * σ x = algebraMap F E (a ^ 2 - δ * b ^ 2)) ∧
    (∀ x : E, x * σ x = 1 → ∃ y : E, y ≠ 0 ∧ x = y / σ y) ∧
    (∀ u : F, IsSquare (algebraMap F E u) → IsSquare u ∨ IsSquare (u * δ)) ∧
    Module.finrank F E = 2 := by
  intro F E _ _ _ _ δ θ σ h
  have t1 := h.coord_indep
  have hθ := h.root_ne_zero
  have hc := h.conj
  have hs := h.sq
  refine ⟨?_, ?_, t1, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨a, b, rfl⟩ := h.span x
    simp [AlgEquiv.commutes, hc]
  · intro x hx
    obtain ⟨a, b, rfl⟩ := h.span x
    simp only [map_add, map_mul, AlgEquiv.commutes, hc] at hx
    have := t1 0 (2 * b) (by simp only [map_zero, map_mul, map_ofNat]; linear_combination -hx)
    have hb : b = 0 := by simpa using this.2
    exact ⟨a, by simp [hb]⟩
  · intro x
    obtain ⟨a, b, rfl⟩ := h.span x
    refine ⟨a, b, ?_⟩
    simp only [map_add, map_mul, AlgEquiv.commutes, hc, map_sub, map_pow]
    linear_combination (-(algebraMap F E b) ^ 2) * hs
  · intro x hx
    by_cases h1 : x = -1
    · refine ⟨θ, hθ, ?_⟩
      rw [hc, h1, div_neg, div_self hθ]
    · have hy : (1 + x) ≠ 0 := fun h0 => h1 (by linear_combination h0)
      have hσy : σ (1 + x) ≠ 0 := by
        rwa [ne_eq, map_eq_zero_iff _ σ.injective]
      refine ⟨1 + x, hy, ?_⟩
      rw [eq_div_iff hσy, map_add, map_one]
      linear_combination hx
  · rintro u ⟨y, hy⟩
    obtain ⟨a, b, rfl⟩ := h.span y
    have := t1 (u - a ^ 2 - b ^ 2 * δ) (-(2 * a * b)) (by
      simp only [map_sub, map_mul, map_pow, map_neg, map_ofNat]
      linear_combination hy + (algebraMap F E b) ^ 2 * hs)
    have h2 : a * b = 0 := by
      have h3 := this.2
      have h4 : (2 : F) * (a * b) = 0 := by linear_combination -h3
      simpa using h4
    have hu : u = a ^ 2 + b ^ 2 * δ := by linear_combination this.1
    rcases mul_eq_zero.1 h2 with ha | hb
    · right; exact ⟨b * δ, by rw [hu, ha]; ring⟩
    · left; exact ⟨a, by rw [hu, hb]; ring⟩
  · have hli : LinearIndependent F ![(1 : E), θ] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      apply t1
      simpa [Algebra.smul_def] using hst
    have hsp : ⊤ ≤ Submodule.span F (Set.range ![(1 : E), θ]) := by
      intro x _
      obtain ⟨a, b, rfl⟩ := h.span x
      rw [Matrix.range_cons_cons_empty]
      refine Submodule.mem_span_pair.2 ⟨a, b, ?_⟩
      simp [Algebra.smul_def]
    simpa using Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)

end GlobalTheory.QNorm
