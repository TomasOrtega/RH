import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.UnitFrame

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open NumberField Matrix in
open scoped nonZeroDivisors ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
omit [IsCMField E] in

/- English proof (translation)
Apply `Complex.ofReal_injective` to reduce the goal to its premises. Establish `htr : ((Algebra.trace ℚ E z : ℚ) : ℂ) = ∑ τ : E →+* ℂ, τ z`. Establish `h` using `trace_eq_sum_embeddings (K := ℚ) (L := E) (E := ℂ) (x := z)`. Rewrite `h` using `[eq_ratCast]`. Rewrite using `[h]`.

Conclude with `(Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) (fun τ => τ z) (fun σ => σ z) (fun _ => rfl)).symm`. Rewrite using `[Complex.ofReal_ratCast, htr]`. Use `push_cast`. Rewrite using `[← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ Ψ)]`. Establish `hsplit : ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ ∉ Ψ), τ z = ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ ∈ Ψ), conj (τ z)`.

Use `Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `τ hτ`. Simplify using `only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢`. Assume the negation of the conclusion as `h`. Conclude with `hτ ((hΨ _).2 (by simpa using h))`.

Introduce `τ hτ`. Simplify using `only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢`. Conclude with `(hΨ τ).1 hτ`. Introduce `τ _`. Simplify using the standard rewrite rules.

Introduce `τ _`. Simplify using the standard rewrite rules. Introduce `τ _`. Simplify using `[ComplexEmbedding.conjugate_coe_eq]`. Rewrite using `[hsplit, ← Finset.sum_add_distrib]`.

Rewrite using `[Finset.sum_subtype (Finset.univ.filter (· ∈ Ψ)) (p := (· ∈ Ψ)) (by simp)]`. Use `Fintype.sum_congr _ _ (fun τ => ?_)` and prove the remaining obligations. Rewrite using `[Complex.add_conj]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem _root_.GlobalTheory.UnitFrame.trace_eq_sum_re (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (z : E) :
    ((Algebra.trace ℚ E z : ℚ) : ℝ) = ∑ τ : Ψ, 2 * (τ.1 z).re := by
  classical
  apply Complex.ofReal_injective
  have htr : ((Algebra.trace ℚ E z : ℚ) : ℂ) = ∑ τ : E →+* ℂ, τ z := by
    have h := trace_eq_sum_embeddings (K := ℚ) (L := E) (E := ℂ) (x := z)
    rw [eq_ratCast] at h
    rw [h]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) (fun τ => τ z) (fun σ => σ z)
      (fun _ => rfl)).symm
  rw [Complex.ofReal_ratCast, htr]
  push_cast
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ Ψ)]
  have hsplit : ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ ∉ Ψ), τ z
      = ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ ∈ Ψ), conj (τ z) := by
    refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
    · intro τ hτ
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      by_contra h
      exact hτ ((hΨ _).2 (by simpa using h))
    · intro τ hτ
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      exact (hΨ τ).1 hτ
    · intro τ _; simp
    · intro τ _; simp
    · intro τ _; simp [ComplexEmbedding.conjugate_coe_eq]
  rw [hsplit, ← Finset.sum_add_distrib]
  rw [Finset.sum_subtype (Finset.univ.filter (· ∈ Ψ)) (p := (· ∈ Ψ)) (by simp)]
  refine Fintype.sum_congr _ _ (fun τ => ?_)
  rw [Complex.add_conj]
  push_cast; ring

open NumberField Matrix in
open scoped nonZeroDivisors ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
omit [NumberField E] [IsCMField E] in

/- English proof (translation)
Simplify using `[_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC, dotProduct, mulVec, Finset.mul_sum, mul_assoc]`.
-/
theorem _root_.GlobalTheory.UnitFrame.hermC_eq {r : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (u v : Fin r → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G u v = u ⬝ᵥ (G.map τ) *ᵥ (star v) := by
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

open NumberField Matrix in
open scoped nonZeroDivisors ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
omit [NumberField E] [IsCMField E] in

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[_root_.ReciprocityTheory.ChartRestriction.G.FD.gram, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC, _root_.ReciprocityTheory.ChartRestriction.G.FD.col, mul_apply, Finset.mul_sum, mul_assoc]`.
-/
theorem _root_.GlobalTheory.UnitFrame.gram_eq {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (x : Matrix (Fin r) (Fin r) ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G x = xᵀ * (G.map τ * x.map conj) := by
  ext a b
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.gram, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC, _root_.ReciprocityTheory.ChartRestriction.G.FD.col, mul_apply, Finset.mul_sum, mul_assoc]

open NumberField Matrix in
open scoped nonZeroDivisors ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
omit [NumberField E] [IsCMField E] in

/- English proof (translation)
Establish `hstar : star (x *ᵥ c') = x.map conj *ᵥ star c'`. Use function extensionality and compare the values at `i`. Simplify using `[mulVec, dotProduct, star_sum, mul_comm]`. Rewrite using `[_root_.GlobalTheory.UnitFrame.hermC_eq, _root_.GlobalTheory.UnitFrame.gram_eq, ← mulVec_mulVec, ← mulVec_mulVec, hstar, dotProduct_mulVec c xᵀ, vecMul_transpose]`.
-/
theorem _root_.GlobalTheory.UnitFrame.hermC_mulVec {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (x : Matrix (Fin r) (Fin r) ℂ) (c c' : Fin r → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G (x *ᵥ c) (x *ᵥ c') = c ⬝ᵥ (_root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G x) *ᵥ (star c') := by
  have hstar : star (x *ᵥ c') = x.map conj *ᵥ star c' := by
    funext i
    simp [mulVec, dotProduct, star_sum, mul_comm]
  rw [_root_.GlobalTheory.UnitFrame.hermC_eq, _root_.GlobalTheory.UnitFrame.gram_eq,
    ← mulVec_mulVec, ← mulVec_mulVec, hstar, dotProduct_mulVec c xᵀ, vecMul_transpose]

open NumberField Matrix in
open scoped nonZeroDivisors ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
omit [NumberField E] [IsCMField E] in

/- English proof (translation)
Establish `hsgn : ∀ a : ℕ, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn q a = 1 ∨ _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn q a = -1`. Apply the tactic sequence `intro a; unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn; split_ifs <;> simp`. Establish `hdet : x.det ≠ 0`. Introduce `h0`. Establish `h1` using `congrArg Matrix.det hx`.

Rewrite `h1` using `[_root_.GlobalTheory.UnitFrame.gram_eq, det_mul, det_transpose, h0, zero_mul, det_diagonal]`. Use `(Finset.prod_ne_zero_iff.2 fun a _ => ?_) h1.symm` and prove the remaining obligations. Apply the tactic sequence `rcases hsgn a with h | h <;> simp [h]`. Establish `hx1 : x * x⁻¹ = 1` using `mul_nonsing_inv x (isUnit_iff_ne_zero.2 hdet)`. Establish `hback : ∀ y : Fin r → ℂ, x *ᵥ (x⁻¹ *ᵥ y) = y`.

Introduce `y`. Rewrite using `[mulVec_mulVec, hx1, one_mulVec]`. Establish `hcol : ∀ a, _root_.ReciprocityTheory.ChartRestriction.G.FD.col x a = x *ᵥ Pi.single a 1`. Introduce `a`. Use function extensionality and compare the values at `k`.

Simplify using `[_root_.ReciprocityTheory.ChartRestriction.G.FD.col, mulVec_single_one]`. Establish `hkey : ∀ a (y : Fin r → ℂ), _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G (_root_.ReciprocityTheory.ChartRestriction.G.FD.col x a) y = ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ) * conj ((x⁻¹ *ᵥ y) a)`. Introduce `a y`. Use `conv_lhs => rw [hcol, ← hback y]`. Rewrite using `[_root_.GlobalTheory.UnitFrame.hermC_mulVec, hx]`.

Simplify using `[mulVec_diagonal]`. Establish `hfull : _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G u v = ∑ a, (x⁻¹ *ᵥ u) a * (((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ) * conj ((x⁻¹ *ᵥ v) a))` using `by conv_lhs => rw [← hback u, ← hback v]`. Rewrite using `[_root_.GlobalTheory.UnitFrame.hermC_mulVec, hx]`. Simplify using `[dotProduct, mulVec_diagonal]`. Rewrite using `[hfull, Complex.im_sum, Complex.im_sum, ← Finset.sum_neg_distrib]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Distinguish the cases in `ha : (a : ℕ) < q`. Simplify using `only [ha, if_true, hkey]`. Establish `: _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn q a = 1` using `by simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, ha]`. Simplify using `[this, Complex.mul_im]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [ha, if_false]`. Establish `: _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn q a = -1` using `by simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, ha]`. Simplify using `[this, Complex.mul_im]`.
-/
theorem _root_.GlobalTheory.UnitFrame.im_sum_periods {r : ℕ} (q : ℕ) (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E)
    (x : Matrix (Fin r) (Fin r) ℂ)
    (hx : _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G x = Matrix.diagonal fun a : Fin r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ))
    (u v : Fin r → ℂ) :
    (∑ a : Fin r, (if (a : ℕ) < q then _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G (_root_.ReciprocityTheory.ChartRestriction.G.FD.col x a) u else (x⁻¹ *ᵥ u) a) *
      conj (if (a : ℕ) < q then _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G (_root_.ReciprocityTheory.ChartRestriction.G.FD.col x a) v else (x⁻¹ *ᵥ v) a)).im =
      -(_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G u v).im := by
  have hsgn : ∀ a : ℕ, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn q a = 1 ∨ _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn q a = -1 := by
    intro a; unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn; split_ifs <;> simp
  have hdet : x.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hx
    rw [_root_.GlobalTheory.UnitFrame.gram_eq, det_mul, det_transpose, h0, zero_mul,
      det_diagonal] at h1
    refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h1.symm
    rcases hsgn a with h | h <;> simp [h]
  have hx1 : x * x⁻¹ = 1 := mul_nonsing_inv x (isUnit_iff_ne_zero.2 hdet)
  have hback : ∀ y : Fin r → ℂ, x *ᵥ (x⁻¹ *ᵥ y) = y := by
    intro y; rw [mulVec_mulVec, hx1, one_mulVec]
  have hcol : ∀ a, _root_.ReciprocityTheory.ChartRestriction.G.FD.col x a = x *ᵥ Pi.single a 1 := by
    intro a; funext k; simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.col, mulVec_single_one]
  have hkey : ∀ a (y : Fin r → ℂ), _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G (_root_.ReciprocityTheory.ChartRestriction.G.FD.col x a) y
      = ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ) * conj ((x⁻¹ *ᵥ y) a) := by
    intro a y
    conv_lhs => rw [hcol, ← hback y]
    rw [_root_.GlobalTheory.UnitFrame.hermC_mulVec, hx]
    simp [mulVec_diagonal]
  have hfull : _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G u v
      = ∑ a, (x⁻¹ *ᵥ u) a * (((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ) * conj ((x⁻¹ *ᵥ v) a)) := by
    conv_lhs => rw [← hback u, ← hback v]
    rw [_root_.GlobalTheory.UnitFrame.hermC_mulVec, hx]
    simp [dotProduct, mulVec_diagonal]
  rw [hfull, Complex.im_sum, Complex.im_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : (a : ℕ) < q
  · simp only [ha, if_true, hkey]
    have : _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn q a = 1 := by simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, ha]
    simp [this, Complex.mul_im]
    ring
  · simp only [ha, if_false]
    have : _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn q a = -1 := by simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, ha]
    simp [this, Complex.mul_im]

open NumberField Matrix in
open scoped nonZeroDivisors ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Establish `hd : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`. Establish `hrt : ((H.rt : E)) ^ 2 = -(H.d : E)`. Use `congrArg (fun y : 𝓞 E => (y : E)) H.rt_sq` as an intermediate fact. Simplify using `using this`. Establish `hw : (τ (H.rt : E)) ^ 2 = -(H.d : ℂ)`.

Rewrite using `[← map_pow, hrt]`. Simplify using the standard rewrite rules. Establish `h0` using `H.sqrt_neg_disc_sq`. Rewrite using `[hΨ, hΨ, ComplexEmbedding.conjugate_coe_eq]`. Use `set w := τ (H.rt : E)`.

Use `set m := H.rt0`. Establish `reZero : ∀ z : ℂ, z ^ 2 = -(H.d : ℂ) → z.re = 0 ∧ z.im ^ 2 = H.d`. Introduce `z hz`. Establish `e1` using `congrArg Complex.re hz`. Establish `e2` using `congrArg Complex.im hz`.

Simplify using `[sq, Complex.mul_re, Complex.mul_im] at e1 e2`. Establish `hre : z.re = 0`. Break down `mul_eq_zero.1 (show z.re * z.im = 0 by linarith) with h | h` into its components or cases. Conclude with `h`. It suffices to derive a contradiction.

Rewrite `e1` using `[h]`. Use polynomial arithmetic with `[sq_nonneg z.re]`. Use `⟨hre, ?_⟩` and prove the remaining obligations. Rewrite `e1` using `[hre]`. Use the polynomial consequences of the given equalities and inequalities.

Take `⟨hwr, hwi⟩` from `reZero w hw`. Take `⟨hmr, hmi⟩` from `reZero m h0`. Establish `hm0 : m.im ≠ 0`. Introduce `h`. Rewrite `hmi` using `[h]`.

Combine the linear equalities and inequalities to obtain the conclusion. Prove the components needed by the constructor for the conclusion. Introduce `h hc`. Rewrite `hc` using `[h]`. Use `congrArg Complex.im hc` as an intermediate fact.

Simplify using `at this`. Conclude with `hm0 (by linarith)`. Introduce `hn`. Apply `Complex.ext` to reduce the goal to its premises. Rewrite using `[hwr, hmr]`.

Establish `: (w.im - m.im) * (w.im + m.im) = 0` using `by nlinarith`. Break down `mul_eq_zero.1 this with h | h` into its components or cases. Combine the linear equalities and inequalities to obtain the conclusion. It suffices to derive a contradiction. Apply `hn` to reduce the goal to its premises.

Apply `Complex.ext` to reduce the goal to its premises. Simplify using `[hwr, hmr]`. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private lemma mem_iff_conjugate_not_mem (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) (τ : E →+* ℂ) :
    τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hrt : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (fun y : 𝓞 E => (y : E)) H.rt_sq
    simpa using this
  have hw : (τ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
    rw [← map_pow, hrt]; simp
  have h0 := H.sqrt_neg_disc_sq
  rw [hΨ, hΨ, ComplexEmbedding.conjugate_coe_eq]
  set w := τ (H.rt : E)
  set m := H.rt0
  have reZero : ∀ z : ℂ, z ^ 2 = -(H.d : ℂ) → z.re = 0 ∧ z.im ^ 2 = H.d := by
    intro z hz
    have e1 := congrArg Complex.re hz
    have e2 := congrArg Complex.im hz
    simp [sq, Complex.mul_re, Complex.mul_im] at e1 e2
    have hre : z.re = 0 := by
      rcases mul_eq_zero.1 (show z.re * z.im = 0 by linarith) with h | h
      · exact h
      · exfalso; rw [h] at e1; nlinarith [sq_nonneg z.re]
    refine ⟨hre, ?_⟩
    rw [hre] at e1; nlinarith
  obtain ⟨hwr, hwi⟩ := reZero w hw
  obtain ⟨hmr, hmi⟩ := reZero m h0
  have hm0 : m.im ≠ 0 := by
    intro h; rw [h] at hmi; linarith
  constructor
  · intro h hc
    rw [h] at hc
    have := congrArg Complex.im hc
    simp at this
    exact hm0 (by linarith)
  · intro hn
    apply Complex.ext
    · rw [hwr, hmr]
    · have : (w.im - m.im) * (w.im + m.im) = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · exfalso; apply hn
        apply Complex.ext
        · simp [hwr, hmr]
        · simp; linarith

open NumberField Matrix in
open scoped nonZeroDivisors ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

/- English proof (translation)
Introduce `E _ _ _ H D r ξ Gm φ Ψ hΨ g idx ty hty hξ hpos hdata x P hP hgram v w`. Establish `hEF` using `hdata.2.2.2.2`. Establish `hcm` using `mem_iff_conjugate_not_mem H Ψ hΨ`. Establish `hherm : ∀ (τ : E →+* ℂ) (a b : Fin r → E), τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm a b) = _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ a) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data …`. Introduce `τ a b`.

Simplify using `[_root_.ReciprocityTheory.ChartRestriction.G.FD.herm, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC, _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc, map_sum, map_mul, IsCMField.complexEmbedding_complexConj]`. Establish `hre : ∀ τ : Ψ, (τ.1 (ξ * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm (φ v) (φ w))).re = -‖τ.1 ξ‖ * (_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (φ v)) (_root_.ReciprocityTheory.ChartRestrictio …`. Introduce `τ`. Establish `hc : conj (τ.1 ξ) = -τ.1 ξ`. Rewrite using `[← IsCMField.complexEmbedding_complexConj, ← map_neg]`.

Use `congr 1`. Establish `hr : (τ.1 ξ).re = 0`. Use `congrArg Complex.re hc` as an intermediate fact. Simplify using `at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hn : ‖τ.1 ξ‖ = (τ.1 ξ).im`. Establish `hz : τ.1 ξ = ((τ.1 ξ).im : ℂ) * Complex.I`. Apply the tactic sequence `apply Complex.ext <;> simp [hr]`. Rewrite using `[hz, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos]`. Simplify using the standard rewrite rules.

Simplify using `using hpos τ.1 τ.2`. Rewrite using `[map_mul, hherm, Complex.mul_re, hr, hn]`. Expand and normalize the polynomial expressions, which then agree. Establish `hL : (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Matrix.diagonal fun k => ((2 * ‖(idx k).1.1 ξ‖ : ℝ) : ℂ)) (P v) (P w)).im = ∑ k, 2 * ‖(idx k).1.1 ξ‖ * (P v k * conj (P w k)).im`. Simplify using `only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, dotProduct, mulVec_diagonal, Complex.im_sum, Pi.star_apply, Complex.star_def]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_left_comm, Complex.im_ofReal_mul]`. Rewrite using `[hL, ← Rat.cast_intCast, hEF, _root_.GlobalTheory.UnitFrame.trace_eq_sum_re Ψ hcm, ← idx.symm.sum_comp, Fintype.sum_prod_type]`. Use `Fintype.sum_congr _ _ fun τ => ?_` and prove the remaining obligations. Simplify using `only [Equiv.apply_symm_apply]`.

Rewrite using `[← Finset.mul_sum, ← Complex.im_sum]`. Establish `hPv : ∀ u, ∀ a : Fin r, P u (idx.symm (τ, a)) = if (a : ℕ) < D.q then _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) a) (_root_.ReciprocityTheory.ChartRestric …`. Introduce `u a`. Rewrite using `[hP]`. Simplify using the standard rewrite rules.

Simplify using `only [hPv]`. Rewrite using `[_root_.GlobalTheory.UnitFrame.im_sum_periods D.q τ.1 Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (hgram τ), hre]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem _root_.GlobalTheory.UnitFrame.im_hermForm_eq :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (hΨ : ∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) (g : ℕ) (idx : Fin g ≃ Ψ × Fin r) (ty : Fin g → (E →+* ℂ)) (hty : ∀ k, ty k = if ((idx k).2 : ℕ) < D.q then ComplexEmbedding.conjugate (idx k).1.1 else (idx k).1.1), _root_.ReciprocityTheory.ChartRestriction.G.FD.cc ξ = -ξ → (∀ τ ∈ Ψ, 0 < (τ ξ).im) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm (φ x) (φ y))) → ∀ (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) (P : D.La →+ (Fin g → ℂ)), (∀ v k, P v k = if ((idx k).2 : ℕ) < D.q then _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (idx k).1.1 Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (idx k).1) (idx k).2) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (idx k).1.1 (φ v)) else ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (idx k).1)⁻¹ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (idx k).1.1 (φ v)) (idx k).2) → (∀ τ : Ψ, _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) = Matrix.diagonal fun a : Fin r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn D.q (a : ℕ) : ℝ) : ℂ)) → ∀ v w, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Matrix.diagonal fun k => ((2 * ‖(idx k).1.1 ξ‖ : ℝ) : ℂ)) (P v) (P w)).im = D.EF v w := by
  intro E _ _ _ H D r ξ Gm φ Ψ hΨ g idx ty hty hξ hpos hdata x P hP hgram v w
  have hEF := hdata.2.2.2.2
  have hcm := mem_iff_conjugate_not_mem H Ψ hΨ
  have hherm : ∀ (τ : E →+* ℂ) (a b : Fin r → E),
      τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm a b) = _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ a) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ b) := by
    intro τ a b
    simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.herm, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC, _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc, map_sum, map_mul,
      IsCMField.complexEmbedding_complexConj]
  have hre : ∀ τ : Ψ, (τ.1 (ξ * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm (φ v) (φ w))).re
      = -‖τ.1 ξ‖ * (_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (φ v)) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (φ w))).im := by
    intro τ
    have hc : conj (τ.1 ξ) = -τ.1 ξ := by
      rw [← IsCMField.complexEmbedding_complexConj, ← map_neg]
      congr 1
    have hr : (τ.1 ξ).re = 0 := by
      have := congrArg Complex.re hc
      simp at this; linarith
    have hn : ‖τ.1 ξ‖ = (τ.1 ξ).im := by
      have hz : τ.1 ξ = ((τ.1 ξ).im : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [hr]
      rw [hz, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos]
      · simp
      · simpa using hpos τ.1 τ.2
    rw [map_mul, hherm, Complex.mul_re, hr, hn]
    ring
  have hL : (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Matrix.diagonal fun k => ((2 * ‖(idx k).1.1 ξ‖ : ℝ) : ℂ)) (P v) (P w)).im
      = ∑ k, 2 * ‖(idx k).1.1 ξ‖ * (P v k * conj (P w k)).im := by
    simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, dotProduct, mulVec_diagonal, Complex.im_sum, Pi.star_apply,
      Complex.star_def]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_left_comm, Complex.im_ofReal_mul]
  rw [hL, ← Rat.cast_intCast, hEF, _root_.GlobalTheory.UnitFrame.trace_eq_sum_re Ψ hcm, ← idx.symm.sum_comp,
    Fintype.sum_prod_type]
  refine Fintype.sum_congr _ _ fun τ => ?_
  simp only [Equiv.apply_symm_apply]
  rw [← Finset.mul_sum, ← Complex.im_sum]
  have hPv : ∀ u, ∀ a : Fin r, P u (idx.symm (τ, a)) = if (a : ℕ) < D.q then
      _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) a) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (φ u))
      else ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (φ u)) a := by
    intro u a; rw [hP]; simp
  simp only [hPv]
  rw [_root_.GlobalTheory.UnitFrame.im_sum_periods D.q τ.1 Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (hgram τ), hre]
  ring

end GlobalTheory.UnitFrame
