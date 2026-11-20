import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
open GlobalTheory.LKTrip NumberField

namespace GlobalTheory.HTGroupOver

/- English proof (translation)
Set `σ : F →+* ℂ` to `(IsAlgClosed.lift : F →ₐ[ℚ] ℂ).toRingHom`. Take `⟨x0, hx0K, hx0⟩` from `hKq.2 σ`. Set `x : Kq` to `⟨x0, hx0K⟩`. Establish `hσq : ∀ q : ℚ, (σ (q : F)).im = 0` using `by intro q; simp [map_ratCast]`. Establish `hdep : ¬ LinearIndependent ℚ ![(1 : Kq), x, x * x]`.

Introduce `h`. Use `h.fintype_card_le_finrank` as an intermediate fact. Simplify using `[hKq.1] at this`. Rewrite `hdep` using `[Fintype.not_linearIndependent_iff]`. Take `⟨g, hg, i, hi⟩` from `hdep`.

Simplify using `only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hg`. Establish `hgF : (g 0 : F) + g 1 * x0 + g 2 * (x0 * x0) = 0`. Use `congrArg (fun w : Kq => (w : F)) hg` as an intermediate fact. Simplify `this` using `[Rat.smul_def, x]`. Establish `hnr : ∀ a b : ℚ, b ≠ 0 → (a : F) + b * x0 ≠ 0`.

Introduce `a b hb h`. Establish `h2` using `congrArg (fun w => (σ w).im) h`. Simplify using `only [map_add, map_mul, map_ratCast, Complex.add_im, Complex.ratCast_im, Complex.mul_im, Complex.ratCast_re, zero_mul, add_zero, zero_add, map_zero, Complex.zero_im] at h2`. Break down `mul_eq_zero.1 h2 with h3 | h3` into its components or cases. Conclude with `hb (by exact_mod_cast h3)`.

Conclude with `hx0 h3`. Establish `hg2 : g 2 ≠ 0`. Introduce `h2`. Rewrite `hgF` using `[h2]`. Simplify using `only [Rat.cast_zero, zero_mul, add_zero] at hgF`.

Distinguish the cases in `h1 : g 1 = 0`. Rewrite `hgF` using `[h1]`. Simplify using `only [Rat.cast_zero, zero_mul, add_zero, Rat.cast_eq_zero] at hgF`. Apply the tactic sequence `fin_cases i <;> simp_all`. Conclude with `hnr _ _ h1 hgF`.

Set `y0 : F` to `2 * g 2 * x0 + g 1`. Establish `hy0K : y0 ∈ Kq`. Use `add_mem (mul_mem (mul_mem (ofNat_mem Kq 2) (SubfieldClass.ratCast_mem Kq _)) hx0K) (SubfieldClass.ratCast_mem Kq _)` and prove the remaining obligations. Establish `hy0sq : y0 * y0 = ((g 1 ^ 2 - 4 * g 0 * g 2 : ℚ) : F)`. Use `push_cast`.

Take the linear combination `(4 * (g 2 : F)) * hgF`. Establish `hy0ne : ∀ a b : ℚ, b ≠ 0 → (a : F) + b * y0 ≠ 0`. Introduce `a b hb h`. Apply `hnr (a + b * g 1) (2 * b * g 2) (by simp [hb, hg2])` to reduce the goal to its premises. Use `push_cast`.

Take the linear combination `h`. Set `y : Kq` to `⟨y0, hy0K⟩`. Use `⟨y, g 1 ^ 2 - 4 * g 0 * g 2, hy0sq, ?_, ?_⟩` and prove the remaining obligations. Establish `hc : (IsCMField.complexConj F y0 - y0) * (IsCMField.complexConj F y0 + y0) = 0`. Establish `h1 : IsCMField.complexConj F y0 * IsCMField.complexConj F y0 = y0 * y0`.

Rewrite using `[← map_mul, hy0sq, map_ratCast]`. Take the linear combination `h1`. Break down `mul_eq_zero.1 hc with h | h` into its components or cases. It suffices to derive a contradiction. Establish `h1 : IsCMField.complexConj F y0 = y0` using `sub_eq_zero.1 h`.

Establish `h2` using `IsCMField.complexEmbedding_complexConj F σ y0`. Rewrite `h2` using `[h1]`. Establish `h3` using `congrArg Complex.im h2`. Simplify using `only [Complex.conj_im] at h3`. Establish `h4 : (σ y0).im = 0` using `by linarith`.

Establish `h5 : (σ y0).im = 2 * g 2 * (σ x0).im`. Establish `e : σ y0 = ((2 * g 2 : ℚ) : ℂ) * σ x0 + ((g 1 : ℚ) : ℂ)`. Simplify using `only [y0, map_add, map_mul, map_ratCast, map_ofNat]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, Complex.add_im, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im, Complex.ratCast_im]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h4` using `[h5]`. Break down `mul_eq_zero.1 h4 with h6 | h6` into its components or cases.

Break down `mul_eq_zero.1 h6 with h7 | h7` into its components or cases. Evaluate the numerical expressions using `at h7`. Conclude with `hg2 (by exact_mod_cast h7)`. Conclude with `hx0 h6`. Conclude with `eq_neg_of_add_eq_zero_left h`.

Establish `hli : LinearIndependent ℚ ![(1 : Kq), y]`. Rewrite using `[LinearIndependent.pair_iff' one_ne_zero]`. Introduce `a ha`. Establish `ha'` using `congrArg (fun w : Kq => (w : F)) ha`. Simplify using `only [Rat.smul_def, mul_one] at ha'`.

Apply `hy0ne (-a) 1 one_ne_zero` to reduce the goal to its premises. Move the coercions through the operations in `at ha' ⊢`. Simplify using `only [y] at ha'`. Rewrite using `[← ha']`. Expand and normalize the polynomial expressions, which then agree.

Establish `hsp` using `hli.span_eq_top_of_card_eq_finrank (by simp [hKq.1])`. Introduce `z`. Establish `hz : z ∈ Submodule.span ℚ (Set.range ![(1 : Kq), y])` using `by rw [hsp]; trivial`. Rewrite `hz` using `[Matrix.range_cons_cons_empty, Submodule.mem_span_pair]`. Take `⟨a, b, hab⟩` from `hz`.

Use `⟨a, b, ?_⟩` and prove the remaining obligations. Rewrite using `[← hab]`. Simplify using `[Rat.smul_def, y]`.
-/
theorem exists_gen {F : Type} [Field F] [NumberField F] [IsCMField F] (Kq : Subfield F)
    (hKq : Module.finrank ℚ Kq = 2 ∧ ∀ τ : F →+* ℂ, ∃ x ∈ Kq, (τ x).im ≠ 0) :
    ∃ y : Kq, ∃ r : ℚ, (y : F) * y = r ∧ IsCMField.complexConj F (y : F) = -(y : F) ∧
      ∀ z : Kq, ∃ a b : ℚ, (z : F) = a + b * y := by
  classical
  let σ : F →+* ℂ := (IsAlgClosed.lift : F →ₐ[ℚ] ℂ).toRingHom
  obtain ⟨x0, hx0K, hx0⟩ := hKq.2 σ
  let x : Kq := ⟨x0, hx0K⟩
  have hσq : ∀ q : ℚ, (σ (q : F)).im = 0 := by intro q; simp [map_ratCast]
  have hdep : ¬ LinearIndependent ℚ ![(1 : Kq), x, x * x] := by
    intro h
    have := h.fintype_card_le_finrank
    simp [hKq.1] at this
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨g, hg, i, hi⟩ := hdep
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hg
  have hgF : (g 0 : F) + g 1 * x0 + g 2 * (x0 * x0) = 0 := by
    have := congrArg (fun w : Kq => (w : F)) hg
    simpa [Rat.smul_def, x] using this

  have hnr : ∀ a b : ℚ, b ≠ 0 → (a : F) + b * x0 ≠ 0 := by
    intro a b hb h
    have h2 := congrArg (fun w => (σ w).im) h
    simp only [map_add, map_mul, map_ratCast, Complex.add_im, Complex.ratCast_im, Complex.mul_im,
      Complex.ratCast_re, zero_mul, add_zero, zero_add, map_zero, Complex.zero_im] at h2
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact hb (by exact_mod_cast h3)
    · exact hx0 h3
  have hg2 : g 2 ≠ 0 := by
    intro h2
    rw [h2] at hgF
    simp only [Rat.cast_zero, zero_mul, add_zero] at hgF
    by_cases h1 : g 1 = 0
    · rw [h1] at hgF
      simp only [Rat.cast_zero, zero_mul, add_zero, Rat.cast_eq_zero] at hgF
      fin_cases i <;> simp_all
    · exact hnr _ _ h1 hgF
  let y0 : F := 2 * g 2 * x0 + g 1
  have hy0K : y0 ∈ Kq := by
    refine add_mem (mul_mem (mul_mem (ofNat_mem Kq 2) (SubfieldClass.ratCast_mem Kq _)) hx0K)
      (SubfieldClass.ratCast_mem Kq _)
  have hy0sq : y0 * y0 = ((g 1 ^ 2 - 4 * g 0 * g 2 : ℚ) : F) := by
    push_cast
    linear_combination (4 * (g 2 : F)) * hgF
  have hy0ne : ∀ a b : ℚ, b ≠ 0 → (a : F) + b * y0 ≠ 0 := by
    intro a b hb h
    apply hnr (a + b * g 1) (2 * b * g 2) (by simp [hb, hg2])
    push_cast
    linear_combination h

  let y : Kq := ⟨y0, hy0K⟩
  refine ⟨y, g 1 ^ 2 - 4 * g 0 * g 2, hy0sq, ?_, ?_⟩
  · have hc : (IsCMField.complexConj F y0 - y0) * (IsCMField.complexConj F y0 + y0) = 0 := by
      have h1 : IsCMField.complexConj F y0 * IsCMField.complexConj F y0 = y0 * y0 := by
        rw [← map_mul, hy0sq, map_ratCast]
      linear_combination h1
    rcases mul_eq_zero.1 hc with h | h
    · exfalso
      have h1 : IsCMField.complexConj F y0 = y0 := sub_eq_zero.1 h
      have h2 := IsCMField.complexEmbedding_complexConj F σ y0
      rw [h1] at h2
      have h3 := congrArg Complex.im h2
      simp only [Complex.conj_im] at h3
      have h4 : (σ y0).im = 0 := by linarith
      have h5 : (σ y0).im = 2 * g 2 * (σ x0).im := by
        have e : σ y0 = ((2 * g 2 : ℚ) : ℂ) * σ x0 + ((g 1 : ℚ) : ℂ) := by
          simp only [y0, map_add, map_mul, map_ratCast, map_ofNat]; push_cast; ring
        rw [e, Complex.add_im, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im, Complex.ratCast_im]
        push_cast; ring
      rw [h5] at h4
      rcases mul_eq_zero.1 h4 with h6 | h6
      · rcases mul_eq_zero.1 h6 with h7 | h7
        · norm_num at h7
        · exact hg2 (by exact_mod_cast h7)
      · exact hx0 h6
    · exact eq_neg_of_add_eq_zero_left h
  · have hli : LinearIndependent ℚ ![(1 : Kq), y] := by
      rw [LinearIndependent.pair_iff' one_ne_zero]
      intro a ha
      have ha' := congrArg (fun w : Kq => (w : F)) ha
      simp only [Rat.smul_def, mul_one] at ha'
      apply hy0ne (-a) 1 one_ne_zero
      push_cast at ha' ⊢
      simp only [y] at ha'
      rw [← ha']
      ring
    have hsp := hli.span_eq_top_of_card_eq_finrank (by simp [hKq.1])
    intro z
    have hz : z ∈ Submodule.span ℚ (Set.range ![(1 : Kq), y]) := by rw [hsp]; trivial
    rw [Matrix.range_cons_cons_empty, Submodule.mem_span_pair] at hz
    obtain ⟨a, b, hab⟩ := hz
    refine ⟨a, b, ?_⟩
    rw [← hab]
    simp [Rat.smul_def, y]

/- English proof (translation)
Introduce `p _ G τ`. Take `⟨y, r, hyr, hcy, hspan⟩` from `exists_gen G.Kq G.hKq`. Establish `hyK : y * y = (r : G.Kq)` using `Subtype.ext (by push_cast; exact hyr)`. Establish `hsq : τ (y : G.F) * τ (y : G.F) = algebraMap ℚ_[p] (PadicAlgCl p) (G.u y) * algebraMap ℚ_[p] (PadicAlgCl p) (G.u y)`. Rewrite using `[← map_mul, ← map_mul, ← map_mul, hyK, hyr, map_ratCast, map_ratCast, map_ratCast]`.

Establish `hz : ∀ z : G.Kq, ∃ a b : ℚ, z = (a : G.Kq) + (b : G.Kq) * y`. Introduce `z`. Take `⟨a, b, h⟩` from `hspan z`. Conclude with `⟨a, b, Subtype.ext (by push_cast; exact h)⟩`. Break down `mul_self_eq_mul_self_iff.1 hsq with h | h` into its components or cases.

Use `left`. Introduce `z`. Take `⟨a, b, rfl⟩` from `hz z`. Simplify using `only [Subfield.coe_add, Subfield.coe_mul, SubfieldClass.coe_ratCast, map_add, map_mul, map_ratCast, h]`. Use `right`.

Introduce `z`. Take `⟨a, b, rfl⟩` from `hz z`. Simplify using `only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, conjQ_apply, Subfield.coe_add, Subfield.coe_mul, SubfieldClass.coe_ratCast, map_add, map_mul, map_ratCast, hcy, map_neg, h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem liesOver_or_conj : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (τ : G.F →+* PadicAlgCl p),
    LiesOver G.Kq G.u τ ∨ LiesOver G.Kq G.u (τ.comp (conjQ G.F).toRingHom) := by
  intro p _ G τ
  obtain ⟨y, r, hyr, hcy, hspan⟩ := exists_gen G.Kq G.hKq
  have hyK : y * y = (r : G.Kq) := Subtype.ext (by push_cast; exact hyr)
  have hsq : τ (y : G.F) * τ (y : G.F) =
      algebraMap ℚ_[p] (PadicAlgCl p) (G.u y) * algebraMap ℚ_[p] (PadicAlgCl p) (G.u y) := by
    rw [← map_mul, ← map_mul, ← map_mul, hyK, hyr, map_ratCast, map_ratCast, map_ratCast]
  have hz : ∀ z : G.Kq, ∃ a b : ℚ, z = (a : G.Kq) + (b : G.Kq) * y := by
    intro z
    obtain ⟨a, b, h⟩ := hspan z
    exact ⟨a, b, Subtype.ext (by push_cast; exact h)⟩
  rcases mul_self_eq_mul_self_iff.1 hsq with h | h
  · left
    intro z
    obtain ⟨a, b, rfl⟩ := hz z
    simp only [Subfield.coe_add, Subfield.coe_mul, SubfieldClass.coe_ratCast, map_add, map_mul, map_ratCast, h]
  · right
    intro z
    obtain ⟨a, b, rfl⟩ := hz z
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, conjQ_apply,
      Subfield.coe_add, Subfield.coe_mul, SubfieldClass.coe_ratCast, map_add, map_mul, map_ratCast, hcy, map_neg, h]
    ring

end GlobalTheory.HTGroupOver
