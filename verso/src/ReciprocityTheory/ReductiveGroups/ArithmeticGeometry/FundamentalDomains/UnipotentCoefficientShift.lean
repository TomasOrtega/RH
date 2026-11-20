import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianTraceFormVanishing

namespace ReciprocityTheory.ChartRestriction.G.FD

namespace UnipotentCoefficientShift

open NumberField Complex
open scoped ComplexConjugate ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Assume the negation of the conclusion as `ha0`. Establish `hint : IsIntegral ℤ (Algebra.norm ℚ a)` using `Algebra.isIntegral_norm ℚ ha`. Take `⟨n, hn⟩` from `IsIntegrallyClosed.isIntegral_iff.mp hint`. Establish `hN : Algebra.norm ℚ a ≠ 0` using `Algebra.norm_ne_zero_iff.mpr ha0`. Establish `hn0 : n ≠ 0`.

Introduce and unpack `rfl`. Apply `hN` to reduce the goal to its premises. Rewrite using `[← hn, map_zero]`. Establish `hne : (Finset.univ : Finset (E →ₐ[ℚ] ℂ)).Nonempty`. Rewrite using `[Finset.univ_nonempty_iff, ← Fintype.card_pos_iff, AlgHom.card]`.

Conclude with `Module.finrank_pos`. Establish `hlt : ∏ σ : E →ₐ[ℚ] ℂ, ‖σ a‖ < ∏ _σ : E →ₐ[ℚ] ℂ, (1 : ℝ)` using `Finset.prod_lt_prod_of_nonempty (fun σ _ => norm_pos_iff.mpr ((map_ne_zero σ).mpr ha0)) (fun σ _ => h (σ : E →+* ℂ)) hne`. Rewrite `hlt` using `[Finset.prod_const_one, ← norm_prod, ← Algebra.norm_eq_prod_embeddings ℚ ℂ a, ← hn]`. Establish `h1 : ‖((n : ℚ) : ℂ)‖ < 1` using `by simpa using hlt`. Establish `h2 : (1 : ℝ) ≤ |(n : ℝ)|`.

Rewrite using `[← Int.cast_abs]`. Conclude with `Int.one_le_abs hn0` after adjusting the coercions. Establish `h3 : ‖((n : ℚ) : ℂ)‖ = |(n : ℝ)|`. Rewrite using `[Rat.cast_intCast, Complex.norm_intCast]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem eq_zero_of_conj_lt_one {a : E} (ha : IsIntegral ℤ a) (h : ∀ σ : E →+* ℂ, ‖σ a‖ < 1) :
    a = 0 := by
  classical
  by_contra ha0
  have hint : IsIntegral ℤ (Algebra.norm ℚ a) := Algebra.isIntegral_norm ℚ ha
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hN : Algebra.norm ℚ a ≠ 0 := Algebra.norm_ne_zero_iff.mpr ha0
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hN
    rw [← hn, map_zero]
  have hne : (Finset.univ : Finset (E →ₐ[ℚ] ℂ)).Nonempty := by
    rw [Finset.univ_nonempty_iff, ← Fintype.card_pos_iff, AlgHom.card]
    exact Module.finrank_pos
  have hlt : ∏ σ : E →ₐ[ℚ] ℂ, ‖σ a‖ < ∏ _σ : E →ₐ[ℚ] ℂ, (1 : ℝ) :=
    Finset.prod_lt_prod_of_nonempty (fun σ _ => norm_pos_iff.mpr ((map_ne_zero σ).mpr ha0))
      (fun σ _ => h (σ : E →+* ℂ)) hne
  rw [Finset.prod_const_one, ← norm_prod, ← Algebra.norm_eq_prod_embeddings ℚ ℂ a, ← hn] at hlt
  have h1 : ‖((n : ℚ) : ℂ)‖ < 1 := by simpa using hlt
  have h2 : (1 : ℝ) ≤ |(n : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hn0
  have h3 : ‖((n : ℚ) : ℂ)‖ = |(n : ℝ)| := by
    rw [Rat.cast_intCast, Complex.norm_intCast]
  linarith

variable {r : ℕ} {X : Data E r}

/- English proof (translation)
Simplify using `only [Data.Hf, Data.ppos_add, smul_add, hermC_sub_left, hermC_add_left, hermC_smul_left]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Hf_add_left (z : Frame X.Ψ r) (τ : X.Ψ) (u v w : Fin r → ℂ) :
    X.Hf z τ (u + v) w = X.Hf z τ u w + X.Hf z τ v w := by
  simp only [Data.Hf, Data.ppos_add, smul_add, hermC_sub_left, hermC_add_left, hermC_smul_left]
  ring

/- English proof (translation)
Simplify using `only [Data.Hf, Data.ppos_sub, smul_sub, hermC_sub_left, hermC_smul_left]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Hf_sub_left (z : Frame X.Ψ r) (τ : X.Ψ) (u v w : Fin r → ℂ) :
    X.Hf z τ (u - v) w = X.Hf z τ u w - X.Hf z τ v w := by
  simp only [Data.Hf, Data.ppos_sub, smul_sub, hermC_sub_left, hermC_smul_left]
  ring

/- English proof (translation)
Simplify using `only [Data.ppos, hermC_smul_left, Finset.smul_sum, smul_smul, Finset.mul_sum, mul_assoc]`.
-/
private lemma ppos_smul' (z : Frame X.Ψ r) (τ : X.Ψ) (k : ℂ) (u : Fin r → ℂ) :
    X.ppos z τ (k • u) = k • X.ppos z τ u := by
  simp only [Data.ppos, hermC_smul_left, Finset.smul_sum, smul_smul, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Simplify using `only [Data.Hf, ppos_smul', smul_comm (2 : ℂ) k, hermC_sub_left, hermC_smul_left]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Hf_smul_left (z : Frame X.Ψ r) (τ : X.Ψ) (k : ℂ) (u w : Fin r → ℂ) :
    X.Hf z τ (k • u) w = k * X.Hf z τ u w := by
  simp only [Data.Hf, ppos_smul', smul_comm (2 : ℂ) k, hermC_sub_left, hermC_smul_left]
  ring

/- English proof (translation)
Simplify using `only [Data.Hf, hermC_add_right]`.
-/
theorem Hf_add_right (z : Frame X.Ψ r) (τ : X.Ψ) (u v w : Fin r → ℂ) :
    X.Hf z τ u (v + w) = X.Hf z τ u v + X.Hf z τ u w := by
  simp only [Data.Hf, hermC_add_right]

/- English proof (translation)
Simplify using `only [Data.Hf, hermC_smul_right]`.
-/
theorem Hf_smul_right (z : Frame X.Ψ r) (τ : X.Ψ) (k : ℂ) (u w : Fin r → ℂ) :
    X.Hf z τ u (k • w) = conj k * X.Hf z τ u w := by
  simp only [Data.Hf, hermC_smul_right]

/- English proof (translation)
Establish `key : hermC τ.1 X.Gm w (X.ppos z τ u) = hermC τ.1 X.Gm (X.ppos z τ w) u`. Rewrite using `[← hermC_conj τ.1 X.Gm_herm (X.ppos z τ u) w, X.hermC_ppos_left hz τ u w, hermC_conj τ.1 X.Gm_herm, X.hermC_ppos_left hz τ w u]`. Simplify using `only [Data.Hf]`. Rewrite using `[hermC_conj τ.1 X.Gm_herm, hermC_sub_right, hermC_smul_right, hermC_sub_left, hermC_smul_left, key, map_ofNat]`.
-/
theorem Hf_conj {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (u w : Fin r → ℂ) :
    conj (X.Hf z τ u w) = X.Hf z τ w u := by
  have key : hermC τ.1 X.Gm w (X.ppos z τ u) = hermC τ.1 X.Gm (X.ppos z τ w) u := by
    rw [← hermC_conj τ.1 X.Gm_herm (X.ppos z τ u) w, X.hermC_ppos_left hz τ u w,
      hermC_conj τ.1 X.Gm_herm, X.hermC_ppos_left hz τ w u]
  simp only [Data.Hf]
  rw [hermC_conj τ.1 X.Gm_herm, hermC_sub_right, hermC_smul_right, hermC_sub_left, hermC_smul_left,
    key, map_ofNat]

/- English proof (translation)
Break down `eq_or_ne v 0 with h | h` into its components or cases. Substitute `h` using the available equality. Simplify using `[Data.maj, Data.posPart, hermC]`. Conclude with `(X.maj_pos hz τ h).le`.
-/
private lemma maj_nonneg_of_mem_dom {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) :
    0 ≤ X.maj z τ v := by
  rcases eq_or_ne v 0 with h | h
  · subst h
    simp [Data.maj, Data.posPart, hermC]
  · exact (X.maj_pos hz τ h).le

/- English proof (translation)
Establish `hv : v = X.ppos z τ v + (v - X.ppos z τ v)` using `by abel`. Establish `hPq : X.ppos z τ (v - X.ppos z τ v) = 0`. Rewrite using `[Data.ppos_sub, X.ppos_ppos hz, sub_self]`. Establish `hpq : hermC τ.1 X.Gm (X.ppos z τ v) (v - X.ppos z τ v) = 0`. Rewrite using `[hermC_sub_right, X.hermC_ppos_left hz τ v v, sub_self]`.

Establish `hqp : hermC τ.1 X.Gm (v - X.ppos z τ v) (X.ppos z τ v) = 0`. Rewrite using `[← hermC_conj τ.1 X.Gm_herm (X.ppos z τ v) (v - X.ppos z τ v), hpq, map_zero]`. Establish `hA : X.Hf z τ (X.ppos z τ v) (X.ppos z τ v) = hermC τ.1 X.Gm (X.ppos z τ v) (X.ppos z τ v)`. Rewrite using `[Data.Hf, X.ppos_ppos hz, two_smul, add_sub_cancel_right]`. Establish `hB : X.Hf z τ (v - X.ppos z τ v) (v - X.ppos z τ v) = -hermC τ.1 X.Gm (v - X.ppos z τ v) (v - X.ppos z τ v)`.

Rewrite using `[Data.Hf, hPq, smul_zero, hermC_sub_left, hermC_zero_left, zero_sub]`. Establish `hV : X.Hf z τ v v = 2 * hermC τ.1 X.Gm (X.ppos z τ v) (X.ppos z τ v) - hermC τ.1 X.Gm v v`. Rewrite using `[Data.Hf, hermC_sub_left, hermC_smul_left, X.hermC_ppos_left hz τ v v]`. Establish `hvv : hermC τ.1 X.Gm v v = hermC τ.1 X.Gm (X.ppos z τ v) (X.ppos z τ v) + hermC τ.1 X.Gm (v - X.ppos z τ v) (v - X.ppos z τ v)` using `by conv_lhs => rw [hv]`. Rewrite using `[hermC_add_left, hermC_add_right, hermC_add_right, hpq, hqp]`.

Expand and normalize the polynomial expressions, which then agree. Establish `eA : hermC τ.1 X.Gm (X.ppos z τ v) (X.ppos z τ v) = (X.maj z τ (X.ppos z τ v) : ℂ)`. Rewrite using `[← hA]`. Conclude with `X.Hf_self hz τ _`. Establish `eB : hermC τ.1 X.Gm (v - X.ppos z τ v) (v - X.ppos z τ v) = -(X.maj z τ (v - X.ppos z τ v) : ℂ)`.

Rewrite using `[← X.Hf_self hz τ, hB, neg_neg]`. Establish `eC : ((X.maj z τ v : ℝ) : ℂ) = ((X.maj z τ (X.ppos z τ v) + X.maj z τ (v - X.ppos z τ v) : ℝ) : ℂ)`. Rewrite using `[← X.Hf_self hz τ, hV, hvv, eA, eB]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `eC' : X.maj z τ v = X.maj z τ (X.ppos z τ v) + X.maj z τ (v - X.ppos z τ v)`. Conclude with `eC` after adjusting the coercions. Establish `ha` using `maj_nonneg_of_mem_dom hz τ (X.ppos z τ v)`. Establish `hb` using `maj_nonneg_of_mem_dom hz τ (v - X.ppos z τ v)`. Establish `e : hermC τ.1 X.Gm v v = ((X.maj z τ (X.ppos z τ v) - X.maj z τ (v - X.ppos z τ v) : ℝ) : ℂ)`.

Rewrite using `[hvv, eA, eB]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, Complex.norm_real, Real.norm_eq_abs, eC']`. Conclude with `abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩`.
-/
theorem norm_hermC_le_maj {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) :
    ‖hermC τ.1 X.Gm v v‖ ≤ X.maj z τ v := by
  have hv : v = X.ppos z τ v + (v - X.ppos z τ v) := by abel
  have hPq : X.ppos z τ (v - X.ppos z τ v) = 0 := by
    rw [Data.ppos_sub, X.ppos_ppos hz, sub_self]
  have hpq : hermC τ.1 X.Gm (X.ppos z τ v) (v - X.ppos z τ v) = 0 := by
    rw [hermC_sub_right, X.hermC_ppos_left hz τ v v, sub_self]
  have hqp : hermC τ.1 X.Gm (v - X.ppos z τ v) (X.ppos z τ v) = 0 := by
    rw [← hermC_conj τ.1 X.Gm_herm (X.ppos z τ v) (v - X.ppos z τ v), hpq, map_zero]
  have hA : X.Hf z τ (X.ppos z τ v) (X.ppos z τ v) = hermC τ.1 X.Gm (X.ppos z τ v) (X.ppos z τ v) := by
    rw [Data.Hf, X.ppos_ppos hz, two_smul, add_sub_cancel_right]
  have hB : X.Hf z τ (v - X.ppos z τ v) (v - X.ppos z τ v) =
      -hermC τ.1 X.Gm (v - X.ppos z τ v) (v - X.ppos z τ v) := by
    rw [Data.Hf, hPq, smul_zero, hermC_sub_left, hermC_zero_left, zero_sub]
  have hV : X.Hf z τ v v = 2 * hermC τ.1 X.Gm (X.ppos z τ v) (X.ppos z τ v) - hermC τ.1 X.Gm v v := by
    rw [Data.Hf, hermC_sub_left, hermC_smul_left, X.hermC_ppos_left hz τ v v]
  have hvv : hermC τ.1 X.Gm v v = hermC τ.1 X.Gm (X.ppos z τ v) (X.ppos z τ v) +
      hermC τ.1 X.Gm (v - X.ppos z τ v) (v - X.ppos z τ v) := by
    conv_lhs => rw [hv]
    rw [hermC_add_left, hermC_add_right, hermC_add_right, hpq, hqp]
    ring
  have eA : hermC τ.1 X.Gm (X.ppos z τ v) (X.ppos z τ v) = (X.maj z τ (X.ppos z τ v) : ℂ) := by
    rw [← hA]; exact X.Hf_self hz τ _
  have eB : hermC τ.1 X.Gm (v - X.ppos z τ v) (v - X.ppos z τ v) = -(X.maj z τ (v - X.ppos z τ v) : ℂ) := by
    rw [← X.Hf_self hz τ, hB, neg_neg]
  have eC : ((X.maj z τ v : ℝ) : ℂ) = ((X.maj z τ (X.ppos z τ v) + X.maj z τ (v - X.ppos z τ v) : ℝ) : ℂ) := by
    rw [← X.Hf_self hz τ, hV, hvv, eA, eB]
    push_cast
    ring
  have eC' : X.maj z τ v = X.maj z τ (X.ppos z τ v) + X.maj z τ (v - X.ppos z τ v) := by
    exact_mod_cast eC
  have ha := maj_nonneg_of_mem_dom hz τ (X.ppos z τ v)
  have hb := maj_nonneg_of_mem_dom hz τ (v - X.ppos z τ v)
  have e : hermC τ.1 X.Gm v v = ((X.maj z τ (X.ppos z τ v) - X.maj z τ (v - X.ppos z τ v) : ℝ) : ℂ) := by
    rw [hvv, eA, eB]
    push_cast
    ring
  rw [e, Complex.norm_real, Real.norm_eq_abs, eC']
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

/- English proof (translation)
Establish `hS : (∑ a : Fin X.p0, ∑ b : Fin X.p0, hermC τ.1 X.Gm ((k : ℂ) • v) (col (mat z τ) (Fin.castLE X.p0_le a)) * (X.gramPos z τ)⁻¹ a b * conj (hermC τ.1 X.Gm ((k : ℂ) • v) (col (mat z τ) (Fin.castLE X.p0_le b)))) = ((k ^ 2 : ℝ) : ℂ) * ∑ a : Fin X.p0, ∑ b : Fin X.p0, hermC τ.1 X.Gm v ( …`. Simplify using `only [hermC_smul_left, map_mul, Complex.conj_ofReal, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hh : hermC τ.1 X.Gm ((k : ℂ) • v) ((k : ℂ) • v) = ((k ^ 2 : ℝ) : ℂ) * hermC τ.1 X.Gm v v`. Rewrite using `[hermC_smul_left, hermC_smul_right, Complex.conj_ofReal]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Data.maj, Data.posPart]`.

Rewrite using `[hS, hh, Complex.re_ofReal_mul, Complex.re_ofReal_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem maj_smul {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (k : ℝ) (v : Fin r → ℂ) :
    X.maj z τ ((k : ℂ) • v) = k ^ 2 * X.maj z τ v := by
  have hS : (∑ a : Fin X.p0, ∑ b : Fin X.p0,
      hermC τ.1 X.Gm ((k : ℂ) • v) (col (mat z τ) (Fin.castLE X.p0_le a)) * (X.gramPos z τ)⁻¹ a b *
        conj (hermC τ.1 X.Gm ((k : ℂ) • v) (col (mat z τ) (Fin.castLE X.p0_le b)))) =
      ((k ^ 2 : ℝ) : ℂ) * ∑ a : Fin X.p0, ∑ b : Fin X.p0,
        hermC τ.1 X.Gm v (col (mat z τ) (Fin.castLE X.p0_le a)) * (X.gramPos z τ)⁻¹ a b *
          conj (hermC τ.1 X.Gm v (col (mat z τ) (Fin.castLE X.p0_le b))) := by
    simp only [hermC_smul_left, map_mul, Complex.conj_ofReal, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    push_cast
    ring
  have hh : hermC τ.1 X.Gm ((k : ℂ) • v) ((k : ℂ) • v) = ((k ^ 2 : ℝ) : ℂ) * hermC τ.1 X.Gm v v := by
    rw [hermC_smul_left, hermC_smul_right, Complex.conj_ofReal]
    push_cast
    ring
  simp only [Data.maj, Data.posPart]
  rw [hS, hh, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  ring

/- English proof (translation)
Rewrite using `[Hf_add_left, Hf_smul_left, add_div, mul_div_assoc, div_self he, mul_one]`.
-/
theorem coef_shift (z : Frame X.Ψ r) (τ : X.Ψ) (u e : Fin r → ℂ) (c : ℂ) (he : X.Hf z τ e e ≠ 0) :
    X.Hf z τ (u + c • e) e / X.Hf z τ e e = X.Hf z τ u e / X.Hf z τ e e + c := by
  rw [Hf_add_left, Hf_smul_left, add_div, mul_div_assoc, div_self he, mul_one]

/- English proof (translation)
Rewrite using `[coef_shift z τ u e c he, add_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem ucomp_shift (z : Frame X.Ψ r) (τ : X.Ψ) (u e : Fin r → ℂ) (c : ℂ) (he : X.Hf z τ e e ≠ 0) :
    (u + c • e) - (X.Hf z τ (u + c • e) e / X.Hf z τ e e) • e =
      u - (X.Hf z τ u e / X.Hf z τ e e) • e := by
  rw [coef_shift z τ u e c he, add_smul]
  abel

/- English proof (translation)
Use `set K := X.Hf z τ v e / X.Hf z τ e e with hKdef`. Establish `hK : K * X.Hf z τ e e = X.Hf z τ v e` using `div_mul_cancel₀ _ he`. Establish `h1 : X.Hf z τ (v - K • e) e = 0`. Rewrite using `[Hf_sub_left, Hf_smul_left, hK, sub_self]`. Establish `h2 : X.Hf z τ e (v - K • e) = 0`.

Rewrite using `[← Hf_conj hz τ (v - K • e) e, h1, map_zero]`. Establish `hv : v = (v - K • e) + K • e` using `(sub_add_cancel v (K • e)).symm`. Establish `hexp : X.Hf z τ v v = X.Hf z τ (v - K • e) (v - K • e) + K * conj K * X.Hf z τ e e` using `by conv_lhs => rw [hv]`. Rewrite using `[Hf_add_left, Hf_add_right, Hf_add_right, Hf_smul_left, Hf_smul_left, Hf_smul_right, Hf_smul_right, h1, h2]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `hexp` using `[X.Hf_self hz, X.Hf_self hz, X.Hf_self hz, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Conclude with `hexp` after adjusting the coercions.
-/
theorem maj_decomp {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (v e : Fin r → ℂ)
    (he : X.Hf z τ e e ≠ 0) :
    X.maj z τ v = X.maj z τ (v - (X.Hf z τ v e / X.Hf z τ e e) • e) +
      ‖X.Hf z τ v e / X.Hf z τ e e‖ ^ 2 * X.maj z τ e := by
  set K := X.Hf z τ v e / X.Hf z τ e e with hKdef
  have hK : K * X.Hf z τ e e = X.Hf z τ v e := div_mul_cancel₀ _ he
  have h1 : X.Hf z τ (v - K • e) e = 0 := by
    rw [Hf_sub_left, Hf_smul_left, hK, sub_self]
  have h2 : X.Hf z τ e (v - K • e) = 0 := by
    rw [← Hf_conj hz τ (v - K • e) e, h1, map_zero]
  have hv : v = (v - K • e) + K • e := (sub_add_cancel v (K • e)).symm
  have hexp : X.Hf z τ v v = X.Hf z τ (v - K • e) (v - K • e) + K * conj K * X.Hf z τ e e := by
    conv_lhs => rw [hv]
    rw [Hf_add_left, Hf_add_right, Hf_add_right, Hf_smul_left, Hf_smul_left, Hf_smul_right,
      Hf_smul_right, h1, h2]
    ring
  rw [X.Hf_self hz, X.Hf_self hz, X.Hf_self hz, Complex.mul_conj, Complex.normSq_eq_norm_sq] at hexp
  exact_mod_cast hexp

end UnipotentCoefficientShift

end ReciprocityTheory.ChartRestriction.G.FD
