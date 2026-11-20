import Mathlib
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.TraceFormDualOneTraceFormDual
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmFieldHostElementAddConjEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ConjugateConjugate
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.ExponentTrace

section

variable {E : Type} [Field E] [NumberField E]

noncomputable abbrev dif (E : Type) [Field E] [NumberField E] : FractionalIdeal (𝓞 E)⁰ E :=
  ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)

/- English proof (translation)
Rewrite using `[← div_eq_mul_inv, FractionalIdeal.mem_div_iff_of_ne_zero hA]`.
-/
theorem mem_mul_inv_iff {A B : FractionalIdeal (𝓞 E)⁰ E} (hA : A ≠ 0) (x : E) :
    x ∈ B * A⁻¹ ↔ ∀ y ∈ A, x * y ∈ B := by
  rw [← div_eq_mul_inv, FractionalIdeal.mem_div_iff_of_ne_zero hA]

/- English proof (translation)
Rewrite using `[FractionalIdeal.mem_one_iff]`. Both sides reduce to the same expression.
-/
theorem mem_one_iff_range (x : E) :
    x ∈ Set.range (algebraMap (𝓞 E) E) ↔ x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
  rw [FractionalIdeal.mem_one_iff]; rfl

/- English proof (translation)
Rewrite using `[mem_mul_inv_iff hA]`. Prove the components needed by the constructor for the conclusion. Introduce `h a ha`. Rewrite using `[mem_inv_different_iff]`. Introduce `o ho`.

Establish `hm : a * o ∈ A`. Use `FractionalIdeal.mul_mem_mul ha (mem_one_fractionalIdeal_iff.2 ho)` as an intermediate fact. Rewrite `this` using `[mul_one]`. Then use the resulting hypothesis. Rewrite using `[mul_assoc]`. Conclude with `h _ hm`.

Introduce `h a ha`. Simplify using `using mem_inv_different_iff.1 (h a ha) 1 isIntegral_one`.
-/
theorem trace_dual_iff {A : FractionalIdeal (𝓞 E)⁰ E} (hA : A ≠ 0) (y : E) :
    (∀ a ∈ A, ∃ n : ℤ, Algebra.trace ℚ E (y * a) = n) ↔ y ∈ (dif E)⁻¹ * A⁻¹ := by
  rw [mem_mul_inv_iff hA]
  constructor
  · intro h a ha
    rw [mem_inv_different_iff]
    intro o ho
    have hm : a * o ∈ A := by
      have := FractionalIdeal.mul_mem_mul ha (mem_one_fractionalIdeal_iff.2 ho)
      rwa [mul_one] at this
    rw [mul_assoc]
    exact h _ hm
  · intro h a ha
    simpa using mem_inv_different_iff.1 (h a ha) 1 isIntegral_one

/- English proof (translation)
Establish `hd : dif E ≠ 0` using `coe_different_ne_zero`. Establish `h0 : (dif E)⁻¹ * A⁻¹ ≠ 0` using `mul_ne_zero (inv_ne_zero hd) (inv_ne_zero hA)`. Establish `e : dif E * A = 1 * ((dif E)⁻¹ * A⁻¹)⁻¹` using `by rw [mul_inv, inv_inv, inv_inv, one_mul]`. Rewrite using `[e, mem_mul_inv_iff h0]`. Simplify using `only [trace_dual_iff hA, mem_one_iff_range]`.
-/
theorem coord_iff {A : FractionalIdeal (𝓞 E)⁰ E} (hA : A ≠ 0) (u : E) :
    (∀ y : E, (∀ a ∈ A, ∃ n : ℤ, Algebra.trace ℚ E (y * a) = n) →
      u * y ∈ Set.range (algebraMap (𝓞 E) E)) ↔ u ∈ dif E * A := by
  have hd : dif E ≠ 0 := coe_different_ne_zero
  have h0 : (dif E)⁻¹ * A⁻¹ ≠ 0 := mul_ne_zero (inv_ne_zero hd) (inv_ne_zero hA)
  have e : dif E * A = 1 * ((dif E)⁻¹ * A⁻¹)⁻¹ := by rw [mul_inv, inv_inv, inv_inv, one_mul]
  rw [e, mem_mul_inv_iff h0]
  simp only [trace_dual_iff hA, mem_one_iff_range]

variable [IsCMField E]

noncomputable def pairIdeal (N : ℕ) (A B : FractionalIdeal (𝓞 E)⁰ E) : FractionalIdeal (𝓞 E)⁰ E :=
  FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E) * A * (dif E * conjFrac B)

/- English proof (translation)
The claim follows from `mul_ne_zero (mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2 (Nat.cast_ne_zero.2 hN.ne')) hA) (mul_ne_zero coe_different_ne_zero (conjFrac_ne_zero hB))`.
-/
theorem pairIdeal_ne_zero {N : ℕ} (hN : 0 < N) {A B : FractionalIdeal (𝓞 E)⁰ E} (hA : A ≠ 0)
    (hB : B ≠ 0) : pairIdeal N A B ≠ 0 :=
  mul_ne_zero (mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2
    (Nat.cast_ne_zero.2 hN.ne')) hA) (mul_ne_zero coe_different_ne_zero (conjFrac_ne_zero hB))

/- English proof (translation)
The claim follows from `map_mul _ a b`.
-/
theorem ccm (a b : E) : cc (a * b) = cc a * cc b := map_mul _ a b
/- English proof (translation)
The claim follows from `map_add _ a b`.
-/
theorem cca (a b : E) : cc (a + b) = cc a + cc b := map_add _ a b
/- English proof (translation)
The claim follows from `IsCMField.complexConj_apply_apply E a`.
-/
theorem ccc (a : E) : cc (cc a) = a := IsCMField.complexConj_apply_apply E a

/- English proof (translation)
Establish `e : pairIdeal N B A = conjFrac (pairIdeal N A B)`. Establish `hN : cc (N : E) = N` using `map_natCast _ N`. Unfold `pairIdeal`. Rewrite using `[map_mul, map_mul, map_mul, conjFrac_conjFrac, conjFrac_spanSingleton, hN, conjFrac_different]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `cc_mem_conjFrac.2 hs`.
-/
theorem conj_mem_pairIdeal {N : ℕ} {A B : FractionalIdeal (𝓞 E)⁰ E} {s : E}
    (hs : s ∈ pairIdeal N A B) : cc s ∈ pairIdeal N B A := by
  have e : pairIdeal N B A = conjFrac (pairIdeal N A B) := by
    have hN : cc (N : E) = N := map_natCast _ N
    unfold pairIdeal
    rw [map_mul, map_mul, map_mul, conjFrac_conjFrac, conjFrac_spanSingleton, hN,
      conjFrac_different]
    ring
  rw [e]
  exact cc_mem_conjFrac.2 hs

/- English proof (translation)
Establish `hd : dif E ≠ 0` using `coe_different_ne_zero`. Establish `hB'` using `conjFrac_ne_zero hB`. Establish `h0 : (dif E)⁻¹ * (conjFrac B)⁻¹ ≠ 0` using `mul_ne_zero (inv_ne_zero hd) (inv_ne_zero hB')`. Establish `e : pairIdeal N A B = (FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E) * A) * ((dif E)⁻¹ * (conjFrac B)⁻¹)⁻¹`. Rewrite using `[mul_inv, inv_inv, inv_inv]`.

Both sides reduce to the same expression. Rewrite using `[e, mem_mul_inv_iff h0]`. Use `forall_congr' fun y => imp_congr ?_ FractionalIdeal.mem_singleton_mul.symm` and prove the remaining obligations. Rewrite using `[← trace_dual_iff hB']`. Prove the components needed by the constructor for the conclusion.

Introduce `h a ha`. Use `h _ (mem_conjFrac.1 ha)` as an intermediate fact. Rewrite `this` using `[ccc]`. Then use the resulting hypothesis. Introduce `h a ha`. Conclude with `h _ (cc_mem_conjFrac.2 ha)`.
-/
theorem entry_iff (N : ℕ) (A : FractionalIdeal (𝓞 E)⁰ E) {B : FractionalIdeal (𝓞 E)⁰ E}
    (hB : B ≠ 0) (s : E) :
    (∀ y : E, (∀ a' ∈ B, ∃ n : ℤ, Algebra.trace ℚ E (y * cc a') = n) →
      ∃ z ∈ A, s * y = (N : E) * z) ↔ s ∈ pairIdeal N A B := by
  have hd : dif E ≠ 0 := coe_different_ne_zero
  have hB' := conjFrac_ne_zero hB
  have h0 : (dif E)⁻¹ * (conjFrac B)⁻¹ ≠ 0 := mul_ne_zero (inv_ne_zero hd) (inv_ne_zero hB')
  have e : pairIdeal N A B = (FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E) * A) *
      ((dif E)⁻¹ * (conjFrac B)⁻¹)⁻¹ := by
    rw [mul_inv, inv_inv, inv_inv]; rfl
  rw [e, mem_mul_inv_iff h0]
  refine forall_congr' fun y => imp_congr ?_ FractionalIdeal.mem_singleton_mul.symm
  rw [← trace_dual_iff hB']
  constructor
  · intro h a ha
    have := h _ (mem_conjFrac.1 ha)
    rwa [ccc] at this
  · intro h a ha
    exact h _ (cc_mem_conjFrac.2 ha)

/- English proof (translation)
Establish `hd : dif E ≠ 0` using `coe_different_ne_zero`. Establish `hB'` using `conjFrac_ne_zero hB`. Establish `hN' : (N : E) ≠ 0` using `Nat.cast_ne_zero.2 hN.ne'`. Establish `hs : FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E) ≠ 0` using `FractionalIdeal.spanSingleton_ne_zero_iff.2 hN'`. Establish `hc : conjFrac (dif E * B) = dif E * conjFrac B` using `by rw [map_mul, conjFrac_different]`.

Establish `e : (dif E)⁻¹ * (pairIdeal N A B)⁻¹ = FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E)⁻¹ * (1 * (dif E * conjFrac B)⁻¹ * (dif E * A)⁻¹)`. Rewrite using `[← FractionalIdeal.spanSingleton_inv]`. Unfold `pairIdeal`. Simplify using `only [mul_inv]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[trace_dual_iff (pairIdeal_ne_zero hN hA hB), e, FractionalIdeal.mem_singleton_mul]`. Simplify using `only [mem_mul_inv_iff (mul_ne_zero hd hA), mem_mul_inv_iff (mul_ne_zero hd hB')]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩ u hu m hm`. Use `hy u hu (cc m) (hc ▸ cc_mem_conjFrac.2 hm)` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Clear the denominators using the available nonvanishing facts. Introduce `h`. Use `⟨(N : E) * x, fun u hu m hm => ?_, by field_simp⟩` and prove the remaining obligations. Use `h u hu (cc m) (mem_conjFrac.1 (hc ▸ hm))` as an intermediate fact.

Rewrite `this` using `[ccc]`. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pair_iff {N : ℕ} (hN : 0 < N) {A B : FractionalIdeal (𝓞 E)⁰ E} (hA : A ≠ 0)
    (hB : B ≠ 0) (x : E) :
    (∀ s ∈ pairIdeal N A B, ∃ n : ℤ, Algebra.trace ℚ E (x * s) = n) ↔
      ∀ u ∈ dif E * A, ∀ m ∈ dif E * B,
        (N : E) * (u * x * cc m) ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
  have hd : dif E ≠ 0 := coe_different_ne_zero
  have hB' := conjFrac_ne_zero hB
  have hN' : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hs : FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E) ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.2 hN'
  have hc : conjFrac (dif E * B) = dif E * conjFrac B := by rw [map_mul, conjFrac_different]
  have e : (dif E)⁻¹ * (pairIdeal N A B)⁻¹ =
      FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E)⁻¹ *
        (1 * (dif E * conjFrac B)⁻¹ * (dif E * A)⁻¹) := by
    rw [← FractionalIdeal.spanSingleton_inv]
    unfold pairIdeal
    simp only [mul_inv]
    ring
  rw [trace_dual_iff (pairIdeal_ne_zero hN hA hB), e, FractionalIdeal.mem_singleton_mul]
  simp only [mem_mul_inv_iff (mul_ne_zero hd hA), mem_mul_inv_iff (mul_ne_zero hd hB')]
  constructor
  · rintro ⟨y, hy, rfl⟩ u hu m hm
    have := hy u hu (cc m) (hc ▸ cc_mem_conjFrac.2 hm)
    convert this using 1
    field_simp
  · intro h
    refine ⟨(N : E) * x, fun u hu m hm => ?_, by field_simp⟩
    have := h u hu (cc m) (mem_conjFrac.1 (hc ▸ hm))
    rw [ccc] at this
    convert this using 1
    ring

/- English proof (translation)
Establish `h1 : FJ.prE X χ β = (Algebra.trace ℚ E (Matrix.trace (χ.transpose * β) / (X.κ0 / 2)) : ℝ) / 2`. Rewrite using `[← X.re_sum_Psi, Complex.re_sum]`. Both sides reduce to the same expression. Establish `h2 : Matrix.trace (χ.transpose * β) / X.ξ0 = ∑ a, ∑ b, χ a b * (β a b / X.ξ0)`. Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_div, mul_div_assoc]`.

Rewrite using `[Finset.sum_comm]`. Rewrite using `[h1, ← h2]`. Establish `key : ∀ (q : ℚ) (n : ℤ), (q : ℝ) / 2 = n ↔ q = 2 * n` using `fun q n => by`. Rewrite using `[div_eq_iff two_ne_zero, mul_comm]`. Conclude with `Iff.rfl` after adjusting the coercions.

Simplify using `only [key]`. Break down `X.κ0_xi with h | h` into its components or cases. Rewrite using `[h, mul_div_cancel_left₀ _ two_ne_zero]`. Rewrite using `[h, neg_div, mul_div_cancel_left₀ _ two_ne_zero, div_neg, map_neg]`. Apply the tactic sequence `constructor <;> rintro ⟨n, hn⟩ <;> exact ⟨-n, by push_cast; linarith⟩`.
-/
theorem prE_int_iff {r ρ : ℕ} (X : Data E r) (χ β : Matrix (Fin ρ) (Fin ρ) E) :
    (∃ n : ℤ, FJ.prE X χ β = n) ↔
      ∃ n : ℤ, Algebra.trace ℚ E (∑ a, ∑ b, χ a b * (β a b / X.ξ0)) = 2 * n := by
  have h1 : FJ.prE X χ β =
      (Algebra.trace ℚ E (Matrix.trace (χ.transpose * β) / (X.κ0 / 2)) : ℝ) / 2 := by
    rw [← X.re_sum_Psi, Complex.re_sum]; rfl
  have h2 : Matrix.trace (χ.transpose * β) / X.ξ0 = ∑ a, ∑ b, χ a b * (β a b / X.ξ0) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
      Finset.sum_div, mul_div_assoc]
    rw [Finset.sum_comm]
  rw [h1, ← h2]
  have key : ∀ (q : ℚ) (n : ℤ), (q : ℝ) / 2 = n ↔ q = 2 * n := fun q n => by
    rw [div_eq_iff two_ne_zero, mul_comm]
    exact_mod_cast Iff.rfl
  simp only [key]
  rcases X.κ0_xi with h | h
  · rw [h, mul_div_cancel_left₀ _ two_ne_zero]
  · rw [h, neg_div, mul_div_cancel_left₀ _ two_ne_zero, div_neg, map_neg]
    constructor <;> rintro ⟨n, hn⟩ <;> exact ⟨-n, by push_cast; linarith⟩

/- English proof (translation)
Establish `hξ` using `X.ξ0_ne`. Establish `hc0 : cc (0 : E) = 0` using `map_zero _`. Simplify using `only [prE_int_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h a b s hs`.

Set `S : Matrix (Fin ρ) (Fin ρ) E` to `Matrix.of fun i j => (if a = i ∧ b = j then s else 0) + (if b = i ∧ a = j then cc s else 0)`. Establish `hS : ∀ i j, (X.ξ0 • S) i j / X.ξ0 = S i j` using `fun i j => by`. Rewrite using `[Matrix.smul_apply, smul_eq_mul, mul_div_cancel_left₀ _ hξ]`. Take `⟨n, hn⟩` from `h (X.ξ0 • S) (fun i j => by`. Simplify using `only [Matrix.smul_apply, smul_eq_mul, S, Matrix.of_apply, ccm, cca, X.ξ0_im, apply_ite cc, ccc, hc0, and_comm (a := a = j), and_comm (a := b = j)]`.

Use the proof step `ring) (fun i j => by`. Rewrite using `[hS]`. Use `Submodule.add_mem (I i j : Submodule (𝓞 E) E) ?_ ?_` and prove the remaining obligations. Use `split_ifs with h`. Take `⟨rfl, rfl⟩` from `h`.

Conclude with `hs`. Conclude with `zero_mem _`. Use `split_ifs with h`. Take `⟨rfl, rfl⟩` from `h`. Conclude with `hI _ _ s hs`.

Conclude with `zero_mem _)`. Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `e : ∑ i, ∑ j, χ i j * ((X.ξ0 • S) i j / X.ξ0) = χ a b * s + cc (χ a b * s)`. Simplify using `only [hS]`. Simplify using `only [S, Matrix.of_apply, mul_add, Finset.sum_add_distrib, ite_and, mul_ite, mul_zero]`.

Rewrite using `[ccm, hχ a b]`. Simplify using the standard rewrite rules. Rewrite `hn` using `[e, map_add, trace_cc]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `h β hβ hm`.

Establish `hreal : cc (∑ a, ∑ b, χ a b * (β a b / X.ξ0)) = ∑ a, ∑ b, χ a b * (β a b / X.ξ0)`. Establish `h1 : ∀ a b, IsCMField.complexConj E (χ a b) = χ b a` using `hχ`. Establish `h2 : ∀ a b, IsCMField.complexConj E (β a b) = -β b a` using `hβ`. Establish `h3 : IsCMField.complexConj E X.ξ0 = -X.ξ0` using `X.ξ0_im`. Simplify using `only [cc, map_sum, map_mul, map_div₀, h1, h2, h3, neg_div_neg_eq]`.

Rewrite using `[Finset.sum_comm]`. Use `(DiagDifferent.trace_even_real_iff E H 1 _ (fun a ha => mem_one_fractionalIdeal_iff.2 (isIntegral_cc (mem_one_fractionalIdeal_iff.1 ha))) hreal).2 (fun o ho => ?_) 1 (FractionalIdeal.one_mem_one _) (map_one _)` as an intermediate fact. Rewrite `this` using `[mul_one]`. Then use the resulting hypothesis. Establish `hh : ∀ a b, ∃ n : ℤ, Algebra.trace ℚ E (χ a b * (β a b / X.ξ0 * o)) = n` using `fun a b => h a b _ (by`. Use `FractionalIdeal.mul_mem_mul (hm a b) ho` as an intermediate fact.

Rewrite using `[mul_one] at this)` and apply the resulting hypothesis. Use `choose k hk using hh`. Use `⟨∑ a, ∑ b, k a b, ?_⟩` and prove the remaining obligations. Simplify using `only [Finset.sum_mul, map_sum, mul_assoc, hk]`. Use `push_cast`.

Both sides reduce to the same expression.
-/
theorem skew_iff (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {r ρ : ℕ} (X : Data E r)
    (I : Fin ρ → Fin ρ → FractionalIdeal (𝓞 E)⁰ E) (hI : ∀ a b, ∀ s ∈ I a b, cc s ∈ I b a)
    (χ : Matrix (Fin ρ) (Fin ρ) E) (hχ : FJ.IsHermE χ) :
    (∀ β, FJ.IsSkew β → (∀ a b, β a b / X.ξ0 ∈ I a b) → ∃ n : ℤ, FJ.prE X χ β = n) ↔
      ∀ a b, ∀ s ∈ I a b, ∃ n : ℤ, Algebra.trace ℚ E (χ a b * s) = n := by
  have hξ := X.ξ0_ne
  have hc0 : cc (0 : E) = 0 := map_zero _
  simp only [prE_int_iff]
  constructor
  · intro h a b s hs
    let S : Matrix (Fin ρ) (Fin ρ) E := Matrix.of fun i j =>
      (if a = i ∧ b = j then s else 0) + (if b = i ∧ a = j then cc s else 0)
    have hS : ∀ i j, (X.ξ0 • S) i j / X.ξ0 = S i j := fun i j => by
      rw [Matrix.smul_apply, smul_eq_mul, mul_div_cancel_left₀ _ hξ]
    obtain ⟨n, hn⟩ := h (X.ξ0 • S) (fun i j => by
      simp only [Matrix.smul_apply, smul_eq_mul, S, Matrix.of_apply, ccm, cca, X.ξ0_im,
        apply_ite cc, ccc, hc0, and_comm (a := a = j), and_comm (a := b = j)]
      ring) (fun i j => by
      rw [hS]
      refine Submodule.add_mem (I i j : Submodule (𝓞 E) E) ?_ ?_
      · split_ifs with h
        · obtain ⟨rfl, rfl⟩ := h; exact hs
        · exact zero_mem _
      · split_ifs with h
        · obtain ⟨rfl, rfl⟩ := h; exact hI _ _ s hs
        · exact zero_mem _)
    refine ⟨n, ?_⟩
    have e : ∑ i, ∑ j, χ i j * ((X.ξ0 • S) i j / X.ξ0) = χ a b * s + cc (χ a b * s) := by
      simp only [hS]
      simp only [S, Matrix.of_apply, mul_add, Finset.sum_add_distrib, ite_and, mul_ite, mul_zero]
      rw [ccm, hχ a b]
      simp
    rw [e, map_add, trace_cc] at hn
    linarith
  · intro h β hβ hm
    have hreal : cc (∑ a, ∑ b, χ a b * (β a b / X.ξ0)) = ∑ a, ∑ b, χ a b * (β a b / X.ξ0) := by
      have h1 : ∀ a b, IsCMField.complexConj E (χ a b) = χ b a := hχ
      have h2 : ∀ a b, IsCMField.complexConj E (β a b) = -β b a := hβ
      have h3 : IsCMField.complexConj E X.ξ0 = -X.ξ0 := X.ξ0_im
      simp only [cc, map_sum, map_mul, map_div₀, h1, h2, h3, neg_div_neg_eq]
      rw [Finset.sum_comm]
    have := (DiagDifferent.trace_even_real_iff E H 1 _ (fun a ha =>
      mem_one_fractionalIdeal_iff.2 (isIntegral_cc (mem_one_fractionalIdeal_iff.1 ha))) hreal).2
      (fun o ho => ?_) 1 (FractionalIdeal.one_mem_one _) (map_one _)
    · rwa [mul_one] at this
    · have hh : ∀ a b, ∃ n : ℤ, Algebra.trace ℚ E (χ a b * (β a b / X.ξ0 * o)) = n := fun a b =>
        h a b _ (by
          have := FractionalIdeal.mul_mem_mul (hm a b) ho
          rwa [mul_one] at this)
      choose k hk using hh
      refine ⟨∑ a, ∑ b, k a b, ?_⟩
      simp only [Finset.sum_mul, map_sum, mul_assoc, hk]
      push_cast
      rfl

end

/- English proof (translation)
Introduce `E _ _ _ H r ρ X N cc' χ hN hc hχ`. Establish `h1` using `skew_iff H X (fun a b => pairIdeal N (cc' a) (cc' b)) (fun a b s hs => conj_mem_pairIdeal hs) χ hχ`. Simplify using `only [entry_iff N _ (hc _), coord_iff (hc _)]`. Rewrite using `[h1]`. Simplify using `only [pair_iff hN (hc _) (hc _), mem_one_iff_range]`.

Prove the components needed by the constructor for the conclusion. Introduce `h u m hu hm`. Simplify using `only [Finset.mul_sum]`. Conclude with `Submodule.sum_mem ((1 : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) fun i _ => Submodule.sum_mem _ fun k _ => h i k _ (hu i) _ (hm k)`. Introduce `h a b u hu m hm`.

Establish `hc0 : cc (0 : E) = 0` using `map_zero _`. Establish `hs : ∀ (a : Fin ρ) (u : E), u ∈ dif E * cc' a → ∀ i, (Pi.single a u : Fin ρ → E) i ∈ dif E * cc' i` using `fun a u hu i => by`. Distinguish the cases in `hi : i = a`. Substitute `hi` using the available equality. Simplify using `using hu`.

Rewrite using `[Pi.single_eq_of_ne hi]`. Conclude with `FractionalIdeal.zero_mem _`. Use `h _ _ (hs a u hu) (hs b m hm)` as an intermediate fact. Simplify `this` using `[Pi.single_apply, apply_ite cc, hc0]`.
-/
theorem prE_int_iff_values_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (r ρ : ℕ) (X : Data E r) (N : ℕ) (cc' : Fin ρ → FractionalIdeal (𝓞 E)⁰ E) (χ : Matrix (Fin ρ) (Fin ρ) E), 0 < N → (∀ b, cc' b ≠ 0) → FJ.IsHermE χ → ((∀ β, FJ.IsSkew β → (∀ a b (y : E), (∀ a' ∈ cc' b, ∃ n : ℤ, Algebra.trace ℚ E (y * cc a') = n) → ∃ z ∈ cc' a, β a b / X.ξ0 * y = (N : E) * z) → ∃ n : ℤ, FJ.prE X χ β = n) ↔ ∀ u m : Fin ρ → E, (∀ a (y : E), (∀ a' ∈ cc' a, ∃ n : ℤ, Algebra.trace ℚ E (y * a') = n) → u a * y ∈ Set.range (algebraMap (𝓞 E) E)) → (∀ a (y : E), (∀ a' ∈ cc' a, ∃ n : ℤ, Algebra.trace ℚ E (y * a') = n) → m a * y ∈ Set.range (algebraMap (𝓞 E) E)) → (N : E) * ∑ i, ∑ k, u i * χ i k * cc (m k) ∈ Set.range (algebraMap (𝓞 E) E)) := by
  intro E _ _ _ H r ρ X N cc' χ hN hc hχ
  have h1 := skew_iff H X (fun a b => pairIdeal N (cc' a) (cc' b))
    (fun a b s hs => conj_mem_pairIdeal hs) χ hχ
  simp only [entry_iff N _ (hc _), coord_iff (hc _)]
  rw [h1]
  simp only [pair_iff hN (hc _) (hc _), mem_one_iff_range]
  constructor
  · intro h u m hu hm
    simp only [Finset.mul_sum]
    exact Submodule.sum_mem ((1 : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) fun i _ =>
      Submodule.sum_mem _ fun k _ => h i k _ (hu i) _ (hm k)
  · intro h a b u hu m hm
    have hc0 : cc (0 : E) = 0 := map_zero _
    have hs : ∀ (a : Fin ρ) (u : E), u ∈ dif E * cc' a →
        ∀ i, (Pi.single a u : Fin ρ → E) i ∈ dif E * cc' i := fun a u hu i => by
      by_cases hi : i = a
      · subst hi; simpa using hu
      · rw [Pi.single_eq_of_ne hi]; exact FractionalIdeal.zero_mem _
    have := h _ _ (hs a u hu) (hs b m hm)
    simpa [Pi.single_apply, apply_ite cc, hc0] using this

end GlobalTheory.ExponentTrace
