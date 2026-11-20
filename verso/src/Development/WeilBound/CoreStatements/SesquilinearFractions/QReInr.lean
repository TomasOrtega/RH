import Development.WeilBound.CoreStatements.SesquilinearFractions.HermSplit

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexConjugate ComplexOrder

noncomputable section

namespace PositivityTheory.Xgf.DPer

open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {g : ℕ} {ty : Fin g → (E →+* ℂ)} {p q : ℕ} (hty : IsTypeFn H p q ty)
variable (G : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) E)

/- English proof (translation)
Use extensionality with `k k'`. Simplify using `only [Matrix.conjTranspose_apply, Hm, Matrix.of_apply]`. Distinguish the cases in `h : ty k = ty k'`. Rewrite using `[if_pos h.symm, if_pos h, hskew (blk hty k) (blk hty k'), map_neg, IsCMField.complexEmbedding_complexConj, h]`. Simplify using `[Complex.conj_I]`.

Rewrite using `[if_neg (Ne.symm h), if_neg h, star_zero]`.
-/
theorem Hm_herm (hskew : ∀ m m', G m' m = -IsCMField.complexConj E (G m m')) : (Hm hty G).IsHermitian := by
  ext k k'
  simp only [Matrix.conjTranspose_apply, Hm, Matrix.of_apply]
  by_cases h : ty k = ty k'
  · rw [if_pos h.symm, if_pos h, hskew (blk hty k) (blk hty k'), map_neg,
      IsCMField.complexEmbedding_complexConj, h]
    simp [Complex.conj_I]
  · rw [if_neg (Ne.symm h), if_neg h, star_zero]

/- English proof (translation)
Assemble the required witnesses or components as `⟨(Complex.nonneg_iff.mp (hN.posSemidef.dotProduct_mulVec_nonneg x)).1, fun hx => (Complex.pos_iff.mp (hN.dotProduct_mulVec_pos hx)).1⟩`.
-/
private theorem re_star_dotProduct_mulVec_pos_of_posDef {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ) (hN : N.PosDef) (x : Fin n → ℂ) :
    0 ≤ (star x ⬝ᵥ N *ᵥ x).re ∧ (x ≠ 0 → 0 < (star x ⬝ᵥ N *ᵥ x).re) :=
  ⟨(Complex.nonneg_iff.mp (hN.posSemidef.dotProduct_mulVec_nonneg x)).1,
    fun hx => (Complex.pos_iff.mp (hN.dotProduct_mulVec_pos hx)).1⟩

/- English proof (translation)
Use `set x : Fin p → ℂ := fun a => star (z ((eP hty σ h).symm a)) with hx`. Establish `hQ : Q hty G σ z z = 2 * (star x ⬝ᵥ (Matrix.of fun a b : Fin p => Complex.I * σ (G (.inl a) (.inl b))) *ᵥ x)`. Rewrite using `[Q_inl hty G σ h]`. Simplify using `only [hx, dotProduct, mulVec, Matrix.of_apply, Finset.mul_sum, Pi.star_apply, star_star, Complex.star_def, Complex.conj_conj]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Take `⟨h0, h1⟩` from `re_star_dotProduct_mulVec_pos_of_posDef _ hG1 x`. Establish `hre : (Q hty G σ z z).re = 2 * (star x ⬝ᵥ (Matrix.of fun a b : Fin p => Complex.I * σ (G (.inl a) (.inl b))) *ᵥ x).re`. Rewrite using `[hQ, Complex.mul_re]`. Evaluate the numerical expressions.

Rewrite using `[hre]`. Use `⟨by positivity, fun ⟨a, ha⟩ => ?_⟩` and prove the remaining obligations. Establish `hx0 : x ≠ 0` using `fun h0' => ha (by simpa [hx] using congrFun h0' a)`. Use `h1 hx0` as an intermediate fact. Check the signs of the components of the expression.
-/
theorem Q_re_inl (σ : E →+* ℂ) (h : σ (H.rt : E) = H.rt0)
    (hG1 : (Matrix.of fun a b : Fin p => Complex.I * σ (G (.inl a) (.inl b))).PosDef) (z : Fin g → ℂ) :
    0 ≤ (Q hty G σ z z).re ∧ ((∃ a, z ((eP hty σ h).symm a) ≠ 0) → 0 < (Q hty G σ z z).re) := by
  set x : Fin p → ℂ := fun a => star (z ((eP hty σ h).symm a)) with hx
  have hQ : Q hty G σ z z =
      2 * (star x ⬝ᵥ (Matrix.of fun a b : Fin p => Complex.I * σ (G (.inl a) (.inl b))) *ᵥ x) := by
    rw [Q_inl hty G σ h]
    simp only [hx, dotProduct, mulVec, Matrix.of_apply, Finset.mul_sum, Pi.star_apply, star_star,
      Complex.star_def, Complex.conj_conj]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  obtain ⟨h0, h1⟩ := re_star_dotProduct_mulVec_pos_of_posDef _ hG1 x
  have hre : (Q hty G σ z z).re = 2 * (star x ⬝ᵥ (Matrix.of fun a b : Fin p =>
      Complex.I * σ (G (.inl a) (.inl b))) *ᵥ x).re := by
    rw [hQ, Complex.mul_re]
    norm_num
  rw [hre]
  refine ⟨by positivity, fun ⟨a, ha⟩ => ?_⟩
  have hx0 : x ≠ 0 := fun h0' => ha (by simpa [hx] using congrFun h0' a)
  have := h1 hx0
  positivity

/- English proof (translation)
Use `set x : Fin q → ℂ := fun a => z ((eQ hty σ h).symm a) with hx`. Use `set M : Matrix (Fin q) (Fin q) ℂ := -(Matrix.of fun a b : Fin q => Complex.I * ComplexEmbedding.conjugate σ (G (.inr a) (.inr b))) with hM`. Establish `hQ : Q hty G σ z z = 2 * starRingEnd ℂ (star x ⬝ᵥ M *ᵥ x)`. Rewrite using `[Q_inr hty G σ h]`. Simplify using `only [hx, hM, dotProduct, mulVec, Matrix.neg_apply, Matrix.of_apply, Finset.mul_sum, map_sum, map_mul, map_neg, Pi.star_apply, Complex.star_def, Complex.conj_conj, Complex.conj_I, ComplexEmbedding.conjugate_coe_eq]`.

Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Take `⟨h0, h1⟩` from `re_star_dotProduct_mulVec_pos_of_posDef _ hG2 x`. Establish `hre : (Q hty G σ z z).re = 2 * (star x ⬝ᵥ M *ᵥ x).re`. Rewrite using `[hQ, Complex.mul_re, Complex.conj_re, Complex.conj_im]`.

Evaluate the numerical expressions. Rewrite using `[hre]`. Use `⟨by positivity, fun ⟨a, ha⟩ => ?_⟩` and prove the remaining obligations. Establish `hx0 : x ≠ 0` using `fun h0' => ha (by simpa [hx] using congrFun h0' a)`. Use `h1 hx0` as an intermediate fact.

Check the signs of the components of the expression.
-/
theorem Q_re_inr (σ : E →+* ℂ) (h : σ (H.rt : E) ≠ H.rt0)
    (hG2 : (-(Matrix.of fun a b : Fin q => Complex.I * ComplexEmbedding.conjugate σ (G (.inr a) (.inr b)))).PosDef)
    (z : Fin g → ℂ) :
    0 ≤ (Q hty G σ z z).re ∧ ((∃ a, z ((eQ hty σ h).symm a) ≠ 0) → 0 < (Q hty G σ z z).re) := by
  set x : Fin q → ℂ := fun a => z ((eQ hty σ h).symm a) with hx
  set M : Matrix (Fin q) (Fin q) ℂ :=
    -(Matrix.of fun a b : Fin q => Complex.I * ComplexEmbedding.conjugate σ (G (.inr a) (.inr b))) with hM
  have hQ : Q hty G σ z z = 2 * starRingEnd ℂ (star x ⬝ᵥ M *ᵥ x) := by
    rw [Q_inr hty G σ h]
    simp only [hx, hM, dotProduct, mulVec, Matrix.neg_apply, Matrix.of_apply, Finset.mul_sum, map_sum,
      map_mul, map_neg, Pi.star_apply, Complex.star_def, Complex.conj_conj, Complex.conj_I,
      ComplexEmbedding.conjugate_coe_eq]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  obtain ⟨h0, h1⟩ := re_star_dotProduct_mulVec_pos_of_posDef _ hG2 x
  have hre : (Q hty G σ z z).re = 2 * (star x ⬝ᵥ M *ᵥ x).re := by
    rw [hQ, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    norm_num
  rw [hre]
  refine ⟨by positivity, fun ⟨a, ha⟩ => ?_⟩
  have hx0 : x ≠ 0 := fun h0' => ha (by simpa [hx] using congrFun h0' a)
  have := h1 hx0
  positivity

/- English proof (translation)
Rewrite using `[herm_split, Complex.re_sum]`. Establish `hQ : ∀ σ : E →+* ℂ, 0 ≤ (Q hty G σ z z).re ∧ ((∃ k, ty k = σ ∧ z k ≠ 0) → 0 < (Q hty G σ z z).re)`. Introduce `σ`. Distinguish the cases in `h : σ (H.rt : E) = H.rt0`. Take `⟨h1, h2⟩` from `Q_re_inl hty G σ h (hG1 σ h) z`.

Use `⟨h1, fun ⟨k, hk, hz⟩ => h2 ⟨eP hty σ h ⟨k, hk⟩, by simpa using hz⟩⟩` and prove the remaining obligations. Establish `hc : ComplexEmbedding.conjugate σ (H.rt : E) = H.rt0` using `(conjugate_rt σ).2 h`. Take `⟨h1, h2⟩` from `Q_re_inr hty G σ h (hG2 _ hc) z`. Use `⟨h1, fun ⟨k, hk, hz⟩ => h2 ⟨eQ hty σ h ⟨k, hk⟩, by simpa using hz⟩⟩` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨k0, hk0⟩ : ∃ k, z k ≠ 0 := by`.

Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hz (funext hc)`. Conclude with `Finset.sum_pos' (fun σ _ => (hQ σ).1) ⟨ty k0, Finset.mem_univ _, (hQ (ty k0)).2 ⟨k0, rfl, hk0⟩⟩`.
-/
theorem Hm_pos
    (hG1 : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 →
      (Matrix.of fun a b : Fin p => Complex.I * τ (G (.inl a) (.inl b))).PosDef)
    (hG2 : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 →
      (-(Matrix.of fun a b : Fin q => Complex.I * τ (G (.inr a) (.inr b)))).PosDef)
    (z : Fin g → ℂ) (hz : z ≠ 0) : 0 < (hermForm (Hm hty G) z z).re := by
  rw [herm_split, Complex.re_sum]
  have hQ : ∀ σ : E →+* ℂ, 0 ≤ (Q hty G σ z z).re ∧
      ((∃ k, ty k = σ ∧ z k ≠ 0) → 0 < (Q hty G σ z z).re) := by
    intro σ
    by_cases h : σ (H.rt : E) = H.rt0
    · obtain ⟨h1, h2⟩ := Q_re_inl hty G σ h (hG1 σ h) z
      refine ⟨h1, fun ⟨k, hk, hz⟩ => h2 ⟨eP hty σ h ⟨k, hk⟩, by simpa using hz⟩⟩
    · have hc : ComplexEmbedding.conjugate σ (H.rt : E) = H.rt0 := (conjugate_rt σ).2 h
      obtain ⟨h1, h2⟩ := Q_re_inr hty G σ h (hG2 _ hc) z
      refine ⟨h1, fun ⟨k, hk, hz⟩ => h2 ⟨eQ hty σ h ⟨k, hk⟩, by simpa using hz⟩⟩
  obtain ⟨k0, hk0⟩ : ∃ k, z k ≠ 0 := by
    by_contra hc; push Not at hc; exact hz (funext hc)
  exact Finset.sum_pos' (fun σ _ => (hQ σ).1) ⟨ty k0, Finset.mem_univ _, (hQ (ty k0)).2 ⟨k0, rfl, hk0⟩⟩

end PositivityTheory.Xgf.DPer

end
