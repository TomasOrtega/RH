import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero

set_option autoImplicit false

noncomputable section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
open scoped ComplexConjugate

namespace GlobalTheory.DefConst

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def detPow (Ψ : Finset (E →+* ℂ)) (a : ℤ) (x : Frame Ψ r) : ℂ := ∏ τ, (mat x τ).det ^ a

/- English proof (translation)
The claim follows from `| 0, f, h => by rw [Fin.prod_univ_zero]; exact (div_self (h 0)).symm | n + 1, f, h => by rw [Fin.prod_univ_castSucc] have ih : ∏ i : Fin n, f i.succ.castSucc / f i.castSucc.castSucc = f (Fin.last n).castSucc / f (0 : Fin (n + 1)).castSucc := telescope n (fun i => f i.castSucc) (f …`.
-/
theorem telescope : ∀ (n : ℕ) (f : Fin (n + 1) → ℝ), (∀ i, f i ≠ 0) →
    ∏ i : Fin n, f i.succ / f i.castSucc = f (Fin.last n) / f 0
  | 0, f, h => by
    rw [Fin.prod_univ_zero]; exact (div_self (h 0)).symm
  | n + 1, f, h => by
    rw [Fin.prod_univ_castSucc]
    have ih : ∏ i : Fin n, f i.succ.castSucc / f i.castSucc.castSucc =
        f (Fin.last n).castSucc / f (0 : Fin (n + 1)).castSucc :=
      telescope n (fun i => f i.castSucc) (fun i => h _)
    simp only [Fin.succ_castSucc]
    rw [ih, Fin.succ_last, Fin.castSucc_zero]
    have h1 := h (Fin.last n).castSucc
    have h2 := h 0
    field_simp

/- English proof (translation)
Unfold `lminor`. Conclude with `Matrix.det_eq_one_of_card_eq_zero (by simp; exact Fintype.card_eq_zero)`.
-/
theorem lminor_zero (M : Matrix (Fin r) (Fin r) ℂ) : lminor M 0 = 1 := by
  unfold lminor
  exact Matrix.det_eq_one_of_card_eq_zero (by simp; exact Fintype.card_eq_zero)

/- English proof (translation)
Unfold `lminor`. Conclude with `Matrix.det_submatrix_equiv_self (finCongr (Fin.val_last r)) M`.
-/
theorem lminor_last (M : Matrix (Fin r) (Fin r) ℂ) : lminor M (Fin.last r) = M.det := by
  unfold lminor
  exact Matrix.det_submatrix_equiv_self (finCongr (Fin.val_last r)) M

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Conclude with `Finset.sum_comm`.
-/
theorem gram_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G x = x.transpose * G.map τ * x.map (starRingEnd ℂ) := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  exact Finset.sum_comm

/- English proof (translation)
Rewrite using `[gram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]`. Use `congr 1`. Conclude with `(RingHom.map_det (starRingEnd ℂ) x).symm`.
-/
theorem det_gram (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    (gram τ G x).det = x.det * (G.map τ).det * starRingEnd ℂ x.det := by
  rw [gram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  congr 1
  exact (RingHom.map_det (starRingEnd ℂ) x).symm

/- English proof (translation)
Introduce `h`. Use `(hx τ).2 i` as an intermediate fact. Rewrite `this` using `[h]`. Simplify using `at this`.
-/
theorem dmin_ne (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm x τ i ≠ 0 := by
  intro h
  have := (hx τ).2 i
  rw [h] at this
  simp at this

/- English proof (translation)
Establish `hD : (mat x τ).det ≠ 0` using `(hx τ).1`. Establish `hpos : 0 < ‖(mat x τ).det‖` using `norm_pos_iff.mpr hD`. Establish `ht` using `telescope r (fun i => ‖dmin X.Gm x τ i‖) (fun i => norm_ne_zero_iff.mpr (dmin_ne X hx τ i))`. Use `beta_reduce at ht`. Establish `hprod : ∏ i : Fin r, ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(a : ℝ) / 2) = (‖dmin X.Gm x τ (Fin.last r)‖ / ‖dmin X.Gm x τ 0‖) ^ (-(a : ℝ) / 2)`.

Repeatedly rewrite using `[norm_div]`. Rewrite using `[Real.finset_prod_rpow _ _ (fun i _ => by positivity), ht]`. Rewrite using `[hprod]`. Establish `h0 : dmin X.Gm x τ 0 = 1` using `lminor_zero _`. Establish `hl : dmin X.Gm x τ (Fin.last r) = (mat x τ).det * (X.Gm.map τ.1).det * starRingEnd ℂ (mat x τ).det`.

Unfold `dmin`. Rewrite using `[lminor_last, det_gram]`. Rewrite using `[h0, hl, norm_one, div_one, norm_mul, norm_mul, Complex.norm_conj, norm_zpow]`. Establish `hg : 0 ≤ ‖(X.Gm.map τ.1).det‖` using `norm_nonneg _`. Rewrite using `[show ‖(mat x τ).det‖ * ‖(X.Gm.map τ.1).det‖ * ‖(mat x τ).det‖ = ‖(mat x τ).det‖ * ‖(mat x τ).det‖ * ‖(X.Gm.map τ.1).det‖ by ring, Real.mul_rpow (by positivity) hg, Real.mul_rpow hpos.le hpos.le, ← Real.rpow_intCast, ← mul_assoc, ← mul_assoc, ← Real.rpow_add hpos, ← Real.rpow_add …`.

Establish `: (a : ℝ) + -(a : ℝ) / 2 + -(a : ℝ) / 2 = 0` using `by ring`. Rewrite using `[this, Real.rpow_zero, one_mul]`.
-/
theorem pnorm_factor (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (a : ℤ) (τ : X.Ψ) :
    ‖(mat x τ).det ^ a‖ * ∏ i : Fin r, ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(a : ℝ) / 2) =
      ‖(X.Gm.map τ.1).det‖ ^ (-(a : ℝ) / 2) := by
  have hD : (mat x τ).det ≠ 0 := (hx τ).1
  have hpos : 0 < ‖(mat x τ).det‖ := norm_pos_iff.mpr hD
  have ht := telescope r (fun i => ‖dmin X.Gm x τ i‖) (fun i => norm_ne_zero_iff.mpr (dmin_ne X hx τ i))
  beta_reduce at ht
  have hprod : ∏ i : Fin r, ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(a : ℝ) / 2) =
      (‖dmin X.Gm x τ (Fin.last r)‖ / ‖dmin X.Gm x τ 0‖) ^ (-(a : ℝ) / 2) := by
    simp_rw [norm_div]
    rw [Real.finset_prod_rpow _ _ (fun i _ => by positivity), ht]
  rw [hprod]
  have h0 : dmin X.Gm x τ 0 = 1 := lminor_zero _
  have hl : dmin X.Gm x τ (Fin.last r) = (mat x τ).det * (X.Gm.map τ.1).det * starRingEnd ℂ (mat x τ).det := by
    unfold dmin; rw [lminor_last, det_gram]
  rw [h0, hl, norm_one, div_one, norm_mul, norm_mul, Complex.norm_conj, norm_zpow]
  have hg : 0 ≤ ‖(X.Gm.map τ.1).det‖ := norm_nonneg _
  rw [show ‖(mat x τ).det‖ * ‖(X.Gm.map τ.1).det‖ * ‖(mat x τ).det‖ =
      ‖(mat x τ).det‖ * ‖(mat x τ).det‖ * ‖(X.Gm.map τ.1).det‖ by ring,
    Real.mul_rpow (by positivity) hg, Real.mul_rpow hpos.le hpos.le, ← Real.rpow_intCast,
    ← mul_assoc, ← mul_assoc, ← Real.rpow_add hpos, ← Real.rpow_add hpos]
  have : (a : ℝ) + -(a : ℝ) / 2 + -(a : ℝ) / 2 = 0 := by ring
  rw [this, Real.rpow_zero, one_mul]

/- English proof (translation)
Unfold `Data.pnorm detPow`. Simplify using `only [hla, norm_prod, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun τ _ => pnorm_factor X hx a τ`.
-/
theorem pnorm_detPow (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la : Wt X.Ψ r) (a : ℤ)
    (hla : ∀ τ i, la τ i = a) :
    X.pnorm la (detPow X.Ψ a) x = ∏ τ : X.Ψ, ‖(X.Gm.map τ.1).det‖ ^ (-(a : ℝ) / 2) := by
  unfold Data.pnorm detPow
  simp only [hla, norm_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun τ _ => pnorm_factor X hx a τ

/- English proof (translation)
Simplify using `only [Matrix.det_apply', mat, Matrix.of_apply]`. Use `fun_prop`.
-/
theorem det_diff (Ψ : Finset (E →+* ℂ)) (τ : Ψ) : Differentiable ℂ (fun x : Frame Ψ r => (mat x τ).det) := by
  simp only [Matrix.det_apply', mat, Matrix.of_apply]
  fun_prop

/- English proof (translation)
Introduce `x hx`. Apply `DifferentiableAt.differentiableWithinAt` to reduce the goal to its premises. Unfold `detPow`. Establish `h : ∀ τ : X.Ψ, DifferentiableAt ℂ (fun y : Frame X.Ψ r => (mat y τ).det ^ a) x` using `fun τ => (det_diff X.Ψ τ x).zpow (Or.inl (hx τ).1)`. Use `fun_prop`.
-/
theorem detPow_diff (X : Data E r) (a : ℤ) : DifferentiableOn ℂ (detPow X.Ψ a) X.dom := by
  intro x hx
  apply DifferentiableAt.differentiableWithinAt
  unfold detPow
  have h : ∀ τ : X.Ψ, DifferentiableAt ℂ (fun y : Frame X.Ψ r => (mat y τ).det ^ a) x :=
    fun τ => (det_diff X.Ψ τ x).zpow (Or.inl (hx τ).1)
  fun_prop

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Simplify using `[lact, mat, Matrix.map_one]`. Both sides reduce to the same expression.
-/
theorem lact_one {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) : lact 1 x = x := by
  funext τ
  simp [lact, mat, Matrix.map_one]
  rfl

/- English proof (translation)
Establish `h1 : (1 : GL (Fin r) E) ∈ X.Γ` using `X.Γ.one_mem`. Establish `hm` using `X.χ_mul la 1 h1 1 h1`. Rewrite `hm` using `[mul_one]`. Take `⟨n, hn, hf⟩` from `X.χ_fin la`. Establish `hne : X.χ la 1 ≠ 0` using `fun h0 => by`.

Use `hf 1 h1` as an intermediate fact. Rewrite `this` using `[h0, zero_pow hn.ne']`. Conclude with `zero_ne_one this`. Conclude with `mul_left_cancel₀ hne (hm.symm.trans (mul_one _).symm)`.
-/
theorem chi_one (X : Data E r) (la : Wt X.Ψ r) : X.χ la 1 = 1 := by
  have h1 : (1 : GL (Fin r) E) ∈ X.Γ := X.Γ.one_mem
  have hm := X.χ_mul la 1 h1 1 h1
  rw [mul_one] at hm
  obtain ⟨n, hn, hf⟩ := X.χ_fin la
  have hne : X.χ la 1 ≠ 0 := fun h0 => by
    have := hf 1 h1
    rw [h0, zero_pow hn.ne'] at this
    exact zero_ne_one this
  exact mul_left_cancel₀ hne (hm.symm.trans (mul_one _).symm)

/- English proof (translation)
Establish `sw : ∀ f : Fin r → Fin r → Fin r → Fin r → ℂ, ∑ a, ∑ b, ∑ k, ∑ l, f a b k l = ∑ k, ∑ l, ∑ a, ∑ b, f a b k l`. Introduce `f`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [hermC, gram, col, Matrix.of_apply, Matrix.mulVec, dotProduct]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [map_sum, Finset.sum_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm`. Use `_ = ∑ k, ∑ l, ∑ a, ∑ b, P a k * v k * τ (G a b) * conj (P b l * w l) := sw _`. Use `_ = _ := by`. Simplify using `only [Finset.sum_mul, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hermC_mulVec (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (P : Matrix (Fin r) (Fin r) ℂ)
    (v w : Fin r → ℂ) :
    hermC τ G (P.mulVec v) (P.mulVec w) = ∑ k, ∑ l, v k * gram τ G P k l * conj (w l) := by
  have sw : ∀ f : Fin r → Fin r → Fin r → Fin r → ℂ,
      ∑ a, ∑ b, ∑ k, ∑ l, f a b k l = ∑ k, ∑ l, ∑ a, ∑ b, f a b k l := by
    intro f
    calc ∑ a, ∑ b, ∑ k, ∑ l, f a b k l = ∑ a, ∑ k, ∑ b, ∑ l, f a b k l :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ k, ∑ a, ∑ b, ∑ l, f a b k l := Finset.sum_comm
      _ = ∑ k, ∑ a, ∑ l, ∑ b, f a b k l :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ k, ∑ l, ∑ a, ∑ b, f a b k l := Finset.sum_congr rfl fun k _ => Finset.sum_comm
  simp only [hermC, gram, col, Matrix.of_apply, Matrix.mulVec, dotProduct]
  calc _ = ∑ a, ∑ b, ∑ k, ∑ l, P a k * v k * τ (G a b) * conj (P b l * w l) := by
        simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ a, ∑ b, P a k * v k * τ (G a b) * conj (P b l * w l) := sw _
    _ = _ := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ =>
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [map_mul]; ring

/- English proof (translation)
Introduce and unpack `⟨-, h0, hne⟩`. Choose the witnesses or unpack the hypotheses as in `⟨τ, hτ⟩ : ∃ τ : E →+* ℂ, τ ∈ X.Ψ := by`. Set `τ0 : E →+* ℂ` to `(IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom`. Distinguish the cases in `h : τ0 ∈ X.Ψ`. Conclude with `⟨τ0, h⟩`.

Use `⟨ComplexEmbedding.conjugate τ0, (X.cmType _).2 ?_⟩` and prove the remaining obligations. Simplify using `using h`. Take `⟨P, hP, hg⟩` from `X.signature ⟨τ, hτ⟩`. Use `set u : Fin r → ℂ := fun a => τ (ξ a) with hu_def`. Establish `hu : hermC τ X.Gm u u = 0`.

Use `congrArg τ h0` as an intermediate fact. Simplify using `only [herm, cc, map_sum, map_mul, map_zero, IsCMField.complexEmbedding_complexConj] at this`. Simplify `this` using `[hermC, u]`. Choose the witnesses or unpack the hypotheses as in `⟨e, he, hsg⟩ : ∃ e : ℂ, e ≠ 0 ∧ ∀ a : Fin r, ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) = e := by`. Break down `hp with h | h` into its components or cases.

Conclude with `⟨-1, by norm_num, fun a => by simp [sgn, h]⟩`. Conclude with `⟨1, one_ne_zero, fun a => by simp [sgn, h, a.isLt]⟩`. Use `set v := P⁻¹.mulVec u with hv_def`. Establish `hPv : P.mulVec v = u`. Rewrite using `[hv_def, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hP), Matrix.one_mulVec]`.

Establish `hsum : hermC τ X.Gm u u = e * ∑ a, v a * conj (v a)`. Rewrite using `[← hPv, hermC_mulVec, hg]`. Simplify using `only [Matrix.diagonal_apply, hsg, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Establish `hv : v = 0`. Establish `h1 : ∑ a, (Complex.normSq (v a) : ℂ) = 0`. Use `hsum.symm.trans hu` as an intermediate fact. Break down `mul_eq_zero.mp this with h | h` into its components or cases. Conclude with `absurd h he`.

Simplify `h` using `[Complex.mul_conj]`. Establish `h2 : ∑ a, Complex.normSq (v a) = 0` using `by exact_mod_cast h1`. Rewrite `h2` using `[Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Complex.normSq_nonneg _)]`. Use function extensionality and compare the values at `a`. Simplify using `using h2 a (Finset.mem_univ _)`.

Establish `hu0 : u = 0` using `by rw [← hPv, hv, Matrix.mulVec_zero]`. Apply `hne` to reduce the goal to its premises. Use function extensionality and compare the values at `a`. Use `congrFun hu0 a` as an intermediate fact. Simplify `this` using `[u]`.
-/
theorem not_iso (X : Data E r) (hp : X.p0 = 0 ∨ X.p0 = r) (ξ : Fin r → E) : ¬ X.IsIso ξ := by
  rintro ⟨-, h0, hne⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : E →+* ℂ, τ ∈ X.Ψ := by
    let τ0 : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
    by_cases h : τ0 ∈ X.Ψ
    · exact ⟨τ0, h⟩
    · refine ⟨ComplexEmbedding.conjugate τ0, (X.cmType _).2 ?_⟩
      simpa using h
  obtain ⟨P, hP, hg⟩ := X.signature ⟨τ, hτ⟩
  set u : Fin r → ℂ := fun a => τ (ξ a) with hu_def
  have hu : hermC τ X.Gm u u = 0 := by
    have := congrArg τ h0
    simp only [herm, cc, map_sum, map_mul, map_zero, IsCMField.complexEmbedding_complexConj] at this
    simpa [hermC, u] using this
  obtain ⟨e, he, hsg⟩ : ∃ e : ℂ, e ≠ 0 ∧ ∀ a : Fin r, ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) = e := by
    rcases hp with h | h
    · exact ⟨-1, by norm_num, fun a => by simp [sgn, h]⟩
    · exact ⟨1, one_ne_zero, fun a => by simp [sgn, h, a.isLt]⟩
  set v := P⁻¹.mulVec u with hv_def
  have hPv : P.mulVec v = u := by
    rw [hv_def, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hP), Matrix.one_mulVec]
  have hsum : hermC τ X.Gm u u = e * ∑ a, v a * conj (v a) := by
    rw [← hPv, hermC_mulVec, hg]
    simp only [Matrix.diagonal_apply, hsg, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hv : v = 0 := by
    have h1 : ∑ a, (Complex.normSq (v a) : ℂ) = 0 := by
      have := hsum.symm.trans hu
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h he
      · simpa [Complex.mul_conj] using h
    have h2 : ∑ a, Complex.normSq (v a) = 0 := by exact_mod_cast h1
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Complex.normSq_nonneg _)] at h2
    funext a
    simpa using h2 a (Finset.mem_univ _)
  have hu0 : u = 0 := by rw [← hPv, hv, Matrix.mulVec_zero]
  apply hne
  funext a
  have := congrFun hu0 a
  simpa [u] using this

/- English proof (translation)
Use `⟨⟨⟨detPow_diff X a, ?_, ?_⟩, ⟨_, fun x hx => (pnorm_detPow X hx la a hla).le⟩⟩, fun ξ hξ => absurd hξ (hdef ξ)⟩` and prove the remaining obligations. Introduce `x _ b hb`. Unfold `detPow bchar`. Establish `hb' : ∀ τ : X.Ψ, (mat b τ).det = ∏ i, b τ i i` using `fun τ => Matrix.det_of_upperTriangular (fun i j hij => (hb τ).2 i j hij)`. Establish `e1 : ∀ τ : X.Ψ, (mat (rmul x b) τ).det ^ a = (mat x τ).det ^ a * ∏ i, b τ i i ^ la τ i`.

Introduce `τ`. Rewrite using `[show mat (rmul x b) τ = mat x τ * mat b τ from rfl, Matrix.det_mul, mul_zpow, hb' τ]`. Simplify using `only [hla]`. Rewrite using `[Finset.prod_zpow]`. Simplify using `only [e1, Finset.prod_mul_distrib]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `γ hγ x _`. Rewrite using `[hΓ γ hγ, lact_one, chi_one, one_mul]`.
-/
theorem detPow_mem_SS (X : Data E r) (hΓ : ∀ γ ∈ X.Γ, γ = 1) (hdef : ∀ ξ, ¬ X.IsIso ξ) (la : Wt X.Ψ r)
    (a : ℤ) (hla : ∀ τ i, la τ i = a) : detPow X.Ψ a ∈ X.SS la := by
  refine ⟨⟨⟨detPow_diff X a, ?_, ?_⟩, ⟨_, fun x hx => (pnorm_detPow X hx la a hla).le⟩⟩,
    fun ξ hξ => absurd hξ (hdef ξ)⟩
  · intro x _ b hb
    unfold detPow bchar
    have hb' : ∀ τ : X.Ψ, (mat b τ).det = ∏ i, b τ i i := fun τ =>
      Matrix.det_of_upperTriangular (fun i j hij => (hb τ).2 i j hij)
    have e1 : ∀ τ : X.Ψ, (mat (rmul x b) τ).det ^ a = (mat x τ).det ^ a * ∏ i, b τ i i ^ la τ i := by
      intro τ
      rw [show mat (rmul x b) τ = mat x τ * mat b τ from rfl, Matrix.det_mul, mul_zpow, hb' τ]
      simp only [hla]
      rw [Finset.prod_zpow]
    simp only [e1, Finset.prod_mul_distrib]
    ring
  · intro γ hγ x _
    rw [hΓ γ hγ, lact_one, chi_one, one_mul]

/- English proof (translation)
Introduce `E _ _ _ r X hΓ hp s x hx`. Use `⟨detPow X.Ψ (if X.p0 = 0 then ((s / 2 : ℕ) : ℤ) else -((s / 2 : ℕ) : ℤ)), detPow_mem_SS X hΓ (not_iso X hp) _ _ ?_, ?_⟩` and prove the remaining obligations. Introduce `τ i`. Distinguish the cases in `h0 : X.p0 = 0`. Simplify using `[deMul, h0]`.

Establish `h : X.p0 = r` using `hp.resolve_left h0`. Establish `hr : r ≠ 0` using `h ▸ h0`. Simplify using `[deMul, h0, h, hr, i.isLt]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (hx τ).1`.
-/
theorem exists_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    (∀ γ ∈ X.Γ, γ = 1) → (X.p0 = 0 ∨ X.p0 = r) → ∀ s : ℕ, ∀ x ∈ X.dom,
      ∃ P ∈ X.SS (deMul X.Ψ r X.p0 s), P x ≠ 0 := by
  intro E _ _ _ r X hΓ hp s x hx
  refine ⟨detPow X.Ψ (if X.p0 = 0 then ((s / 2 : ℕ) : ℤ) else -((s / 2 : ℕ) : ℤ)),
    detPow_mem_SS X hΓ (not_iso X hp) _ _ ?_, ?_⟩
  · intro τ i
    by_cases h0 : X.p0 = 0
    · simp [deMul, h0]
    · have h : X.p0 = r := hp.resolve_left h0
      have hr : r ≠ 0 := h ▸ h0
      simp [deMul, h0, h, hr, i.isLt]
  · exact Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (hx τ).1

end GlobalTheory.DefConst
