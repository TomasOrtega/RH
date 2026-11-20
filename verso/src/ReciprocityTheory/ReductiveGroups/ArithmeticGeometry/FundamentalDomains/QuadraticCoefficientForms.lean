import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowIsotropicPairs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PackingSeparation

namespace ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate Classical

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Establish `h00 : (M 0 0).im = 0`. Use `hM.apply 0 0` as an intermediate fact. Rewrite `this` using `[Complex.star_def]`. Conclude with `Complex.conj_eq_iff_im.mp this`. Establish `h11 : (M 1 1).im = 0`.

Use `hM.apply 1 1` as an intermediate fact. Rewrite `this` using `[Complex.star_def]`. Conclude with `Complex.conj_eq_iff_im.mp this`. Establish `h10 : M 1 0 = conj (M 0 1)`. Use `hM.apply 1 0` as an intermediate fact.

Rewrite `this` using `[Complex.star_def]`. Conclude with `this.symm`. Simplify using `only [Matrix.det_fin_two, Fin.sum_univ_two, h10, Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.normSq_apply, h00, h11]`. Use polynomial arithmetic with `[sq_nonneg ((M 0 0).re * (a 0).re + (M 0 1).re * (a 1).re + (M 0 1).im * (a 1).im), sq_nonneg ((M 0 0).re * (a 0).im + (M 0 1).re * (a 1).im - (M 0 1).im * (a 1).re)]`.
-/
theorem quad2 (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.IsHermitian) (a : Fin 2 → ℂ) :
    M.det.re * Complex.normSq (a 1) ≤ (M 0 0).re * (∑ i, ∑ k, M i k * a i * conj (a k)).re := by
  have h00 : (M 0 0).im = 0 := by
    have := hM.apply 0 0
    rw [Complex.star_def] at this
    exact Complex.conj_eq_iff_im.mp this
  have h11 : (M 1 1).im = 0 := by
    have := hM.apply 1 1
    rw [Complex.star_def] at this
    exact Complex.conj_eq_iff_im.mp this
  have h10 : M 1 0 = conj (M 0 1) := by
    have := hM.apply 1 0
    rw [Complex.star_def] at this
    exact this.symm
  simp only [Matrix.det_fin_two, Fin.sum_univ_two, h10, Complex.sub_re, Complex.add_re,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.normSq_apply, h00, h11]
  nlinarith [sq_nonneg ((M 0 0).re * (a 0).re + (M 0 1).re * (a 1).re + (M 0 1).im * (a 1).im),
    sq_nonneg ((M 0 0).re * (a 0).im + (M 0 1).re * (a 1).im - (M 0 1).im * (a 1).re)]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a, ξ a ≠ 0 := by`. Assume the negation of the conclusion as `h0`. Use `push_neg at h0`. Conclude with `hξ0 (funext h0)`. Choose the witnesses or unpack the hypotheses as in `⟨b, hb⟩ : ∃ b, x b ≠ (x a / ξ a) * ξ b := by`.

Assume the negation of the conclusion as `h0`. Use `push_neg at h0`. Conclude with `hne (x a / ξ a) (funext fun b => by rw [Pi.smul_apply, smul_eq_mul, h0 b])`. Establish `hm : ξ a * x b - ξ b * x a ≠ 0`. Introduce `h0`.

Apply `hb` to reduce the goal to its premises. Rewrite using `[div_mul_eq_mul_div, eq_div_iff ha]`. Take the linear combination `h0`. Establish `h1` using `congrFun h a`. Establish `h2` using `congrFun h b`.

Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Data.emb] at h1 h2`. Establish `hτ : τ (ξ a * x b - ξ b * x a) ≠ 0` using `(map_ne_zero τ).2 hm`. Rewrite `hτ` using `[map_sub, map_mul, map_mul]`. Establish `h3 : q * (τ (ξ a) * τ (x b) - τ (ξ b) * τ (x a)) = 0`. Take the linear combination `τ (ξ a) * h2 - τ (ξ b) * h1`.

Conclude with `(mul_eq_zero.1 h3).resolve_right hτ`.
-/
theorem coef_zero {r : ℕ} {ξ x : Fin r → E} (hξ0 : ξ ≠ 0) (hne : ∀ e : E, x ≠ e • ξ)
    (τ : E →+* ℂ) (p q : ℂ) (h : p • Data.emb τ ξ + q • Data.emb τ x = 0) : q = 0 := by
  obtain ⟨a, ha⟩ : ∃ a, ξ a ≠ 0 := by
    by_contra h0
    push_neg at h0
    exact hξ0 (funext h0)
  obtain ⟨b, hb⟩ : ∃ b, x b ≠ (x a / ξ a) * ξ b := by
    by_contra h0
    push_neg at h0
    exact hne (x a / ξ a) (funext fun b => by rw [Pi.smul_apply, smul_eq_mul, h0 b])
  have hm : ξ a * x b - ξ b * x a ≠ 0 := by
    intro h0
    apply hb
    rw [div_mul_eq_mul_div, eq_div_iff ha]
    linear_combination h0
  have h1 := congrFun h a
  have h2 := congrFun h b
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Data.emb] at h1 h2
  have hτ : τ (ξ a * x b - ξ b * x a) ≠ 0 := (map_ne_zero τ).2 hm
  rw [map_sub, map_mul, map_mul] at hτ
  have h3 : q * (τ (ξ a) * τ (x b) - τ (ξ b) * τ (x a)) = 0 := by
    linear_combination τ (ξ a) * h2 - τ (ξ b) * h1
  exact (mul_eq_zero.1 h3).resolve_right hτ

variable {r : ℕ} (X : Data E r)

def toCP (τ : X.Ψ) : TraceIntegralBasis.CP E := ⟨InfinitePlace.mk τ.1, IsTotallyComplex.isComplex _⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨τ, hτ⟩ ⟨τ', hτ'⟩ h`. Establish `h' : InfinitePlace.mk τ = InfinitePlace.mk τ'` using `congrArg Subtype.val h`. Break down `InfinitePlace.mk_eq_iff.1 h' with e | e` into its components or cases. Conclude with `Subtype.ext e`.

It suffices to derive a contradiction. Rewrite `hτ'` using `[← e]`. Conclude with `(X.cmType τ).1 hτ hτ'`. Introduce and unpack `⟨w, hw⟩`. Distinguish the cases in `hφ : w.embedding ∈ X.Ψ`.

Conclude with `⟨⟨_, hφ⟩, Subtype.ext (InfinitePlace.mk_embedding w)⟩`. Establish `hc : ComplexEmbedding.conjugate w.embedding ∈ X.Ψ`. Assume the negation of the conclusion as `hc`. Conclude with `hφ ((X.cmType _).2 hc)`. Conclude with `⟨⟨_, hc⟩, Subtype.ext ((InfinitePlace.mk_conjugate_eq _).trans (InfinitePlace.mk_embedding w))⟩`.
-/
theorem toCP_bij : Function.Bijective (toCP X) := by
  constructor
  · rintro ⟨τ, hτ⟩ ⟨τ', hτ'⟩ h
    have h' : InfinitePlace.mk τ = InfinitePlace.mk τ' := congrArg Subtype.val h
    rcases InfinitePlace.mk_eq_iff.1 h' with e | e
    · exact Subtype.ext e
    · exfalso
      rw [← e] at hτ'
      exact (X.cmType τ).1 hτ hτ'
  · rintro ⟨w, hw⟩
    by_cases hφ : w.embedding ∈ X.Ψ
    · exact ⟨⟨_, hφ⟩, Subtype.ext (InfinitePlace.mk_embedding w)⟩
    · have hc : ComplexEmbedding.conjugate w.embedding ∈ X.Ψ := by
        by_contra hc
        exact hφ ((X.cmType _).2 hc)
      exact ⟨⟨_, hc⟩, Subtype.ext ((InfinitePlace.mk_conjugate_eq _).trans (InfinitePlace.mk_embedding w))⟩

/- English proof (translation)
Rewrite using `[Fintype.card_of_bijective (toCP_bij X)]`. Unfold `fdeg`. Establish `h` using `NumberField.InfinitePlace.card_add_two_mul_card_eq_rank E`. Establish `h0 : NumberField.InfinitePlace.nrRealPlaces E = 0` using `by first`. Consider the case `exact NumberField.IsTotallyComplex.nrRealPlaces_eq_zero`.

Consider the case `exact NumberField.nrRealPlaces_eq_zero_iff.2 inferInstance`. Consider the case `simp`. Rewrite `h` using `[h0, zero_add]`. Rewrite using `[← h]`. Unfold `NumberField.InfinitePlace.nrComplexPlaces`.

Establish `h3 : Fintype.card (TraceIntegralBasis.CP E) = Fintype.card {w : InfinitePlace E // w.IsComplex}` using `Fintype.card_congr (Equiv.refl _)`. Use linear arithmetic over natural numbers and integers.
-/
theorem card_Psi : Fintype.card X.Ψ = fdeg E := by
  rw [Fintype.card_of_bijective (toCP_bij X)]
  unfold fdeg
  have h := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank E
  have h0 : NumberField.InfinitePlace.nrRealPlaces E = 0 := by
    first
    | exact NumberField.IsTotallyComplex.nrRealPlaces_eq_zero
    | exact NumberField.nrRealPlaces_eq_zero_iff.2 inferInstance
    | simp
  rw [h0, zero_add] at h
  rw [← h]
  unfold NumberField.InfinitePlace.nrComplexPlaces
  have h3 : Fintype.card (TraceIntegralBasis.CP E) = Fintype.card {w : InfinitePlace E // w.IsComplex} :=
    Fintype.card_congr (Equiv.refl _)
  omega

/- English proof (translation)
Take `⟨φ⟩ : Nonempty (E →+* ℂ)` from `by first`. Consider the case `exact inferInstance`. Consider the case `exact ⟨(Classical.arbitrary (InfinitePlace E)).embedding⟩`. Rewrite using `[Fintype.card_pos_iff]`. Distinguish the cases in `h : φ ∈ X.Ψ`.

Conclude with `⟨⟨φ, h⟩⟩`. Conclude with `⟨⟨ComplexEmbedding.conjugate φ, by`. Assume the negation of the conclusion as `hc`. Conclude with `h ((X.cmType φ).2 hc)⟩⟩`.
-/
theorem card_Psi_pos : 0 < Fintype.card X.Ψ := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := by
    first
    | exact inferInstance
    | exact ⟨(Classical.arbitrary (InfinitePlace E)).embedding⟩
  rw [Fintype.card_pos_iff]
  by_cases h : φ ∈ X.Ψ
  · exact ⟨⟨φ, h⟩⟩
  · exact ⟨⟨ComplexEmbedding.conjugate φ, by
      by_contra hc
      exact h ((X.cmType φ).2 hc)⟩⟩

/- English proof (translation)
Establish `hall : ∀ w : InfinitePlace E, w.IsComplex` using `fun w => IsTotallyComplex.isComplex w`. Establish `h1 : ∏ τ : X.Ψ, ‖τ.1 γ‖ ^ 2 = ∏ w : TraceIntegralBasis.CP E, w.1 γ ^ 2` using `Fintype.prod_bijective (toCP X) (toCP_bij X) _ _ fun τ => by show _ = (InfinitePlace.mk τ.1 γ) ^ 2`. Rewrite using `[InfinitePlace.apply]`. Establish `h2 : ∏ w : TraceIntegralBasis.CP E, w.1 γ ^ 2 = ∏ w : InfinitePlace E, w γ ^ w.mult`. Use `Fintype.prod_equiv (Equiv.subtypeUnivEquiv hall) _ _ fun w => ?_` and prove the remaining obligations.

Use `show w.1 γ ^ 2 = w.1 γ ^ InfinitePlace.mult w.1`. Rewrite using `[InfinitePlace.mult_isComplex w]`. Rewrite using `[h1, h2, InfinitePlace.prod_eq_abs_norm]`. Establish `hI : IsIntegral ℤ (Algebra.norm ℚ γ)` using `by first`. Consider the case `exact Algebra.isIntegral_norm ℚ hint`.

Consider the case `exact Algebra.isIntegral_norm hint`. Take `⟨n, hn⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hI`. Establish `hN : Algebra.norm ℚ γ ≠ 0` using `Algebra.norm_ne_zero_iff.2 hγ`. Rewrite `hN`, the goal using `[← hn]`. Establish `hn0 : n ≠ 0`.

Introduce and unpack `rfl`. Conclude with `hN (map_zero _)`. Establish `h3` using `Int.one_le_abs hn0`. Simplify using `only [algebraMap_int_eq, eq_intCast]`. Use `push_cast`.

Conclude with `h3` after adjusting the coercions.
-/
theorem one_le_prod_norm (γ : E) (hint : IsIntegral ℤ γ) (hγ : γ ≠ 0) :
    1 ≤ ∏ τ : X.Ψ, ‖τ.1 γ‖ ^ 2 := by
  have hall : ∀ w : InfinitePlace E, w.IsComplex := fun w => IsTotallyComplex.isComplex w
  have h1 : ∏ τ : X.Ψ, ‖τ.1 γ‖ ^ 2 = ∏ w : TraceIntegralBasis.CP E, w.1 γ ^ 2 :=
    Fintype.prod_bijective (toCP X) (toCP_bij X) _ _ fun τ => by
      show _ = (InfinitePlace.mk τ.1 γ) ^ 2
      rw [InfinitePlace.apply]
  have h2 : ∏ w : TraceIntegralBasis.CP E, w.1 γ ^ 2 = ∏ w : InfinitePlace E, w γ ^ w.mult := by
    refine Fintype.prod_equiv (Equiv.subtypeUnivEquiv hall) _ _ fun w => ?_
    show w.1 γ ^ 2 = w.1 γ ^ InfinitePlace.mult w.1
    rw [InfinitePlace.mult_isComplex w]
  rw [h1, h2, InfinitePlace.prod_eq_abs_norm]
  have hI : IsIntegral ℤ (Algebra.norm ℚ γ) := by
    first
    | exact Algebra.isIntegral_norm ℚ hint
    | exact Algebra.isIntegral_norm hint
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 hI
  have hN : Algebra.norm ℚ γ ≠ 0 := Algebra.norm_ne_zero_iff.2 hγ
  rw [← hn] at hN ⊢
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hN (map_zero _)
  have h3 := Int.one_le_abs hn0
  simp only [algebraMap_int_eq, eq_intCast]
  push_cast
  exact_mod_cast h3

end

end ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms
