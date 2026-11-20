import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

open ReciprocityTheory.ChartRestriction.G.FD NumberField

namespace GlobalTheory.FlagSecProbe

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Use `choose P hP hG using X.signature`. Use `⟨fun τ => P τ, fun τ => ⟨hP τ, fun i => ?_⟩⟩` and prove the remaining obligations. Establish `h : dmin X.Gm (fun τ => P τ) τ i = ((psgn X.p0 i : ℝ) : ℂ)`. Establish `hm : mat (Ψ` using `X.Ψ) (fun τ => P τ) τ = P τ := rfl`. Unfold `dmin lminor`.

Rewrite using `[hm, hG τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]`. Unfold `psgn`. Rewrite using `[Complex.ofReal_prod, ← Fin.prod_univ_eq_prod_range (fun a => ((sgn X.p0 a : ℝ) : ℂ))]`. Both sides reduce to the same expression. Rewrite using `[h, Complex.ofReal_re]`.

Use `mul_self_pos.2 ?_` and prove the remaining obligations. Unfold `psgn`. Use `Finset.prod_ne_zero_iff.2 fun a _ => ?_` and prove the remaining obligations. Unfold `sgn`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
theorem dom_nonempty (X : Data E r) : X.dom.Nonempty := by
  classical
  choose P hP hG using X.signature
  refine ⟨fun τ => P τ, fun τ => ⟨hP τ, fun i => ?_⟩⟩
  have h : dmin X.Gm (fun τ => P τ) τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    have hm : mat (Ψ := X.Ψ) (fun τ => P τ) τ = P τ := rfl
    unfold dmin lminor
    rw [hm, hG τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    unfold psgn
    rw [Complex.ofReal_prod, ← Fin.prod_univ_eq_prod_range (fun a => ((sgn X.p0 a : ℝ) : ℂ))]
    rfl
  rw [h, Complex.ofReal_re]
  refine mul_self_pos.2 ?_
  unfold psgn
  refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
  unfold sgn
  split_ifs <;> norm_num

/- English proof (translation)
Introduce `h`. Use `(hx τ).2 i` as an intermediate fact. Simplify using `[h] at this`.
-/
theorem dmin_ne_zero (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ)
    (i : Fin (r + 1)) : dmin X.Gm x τ i ≠ 0 := by
  intro h
  have := (hx τ).2 i
  simp [h] at this

/- English proof (translation)
Unfold `Data.pnorm`. Establish `: (∏ τ, ∏ i : Fin r, ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2)) ≠ 0`. Use `Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ => ?_` and prove the remaining obligations. Conclude with `(Real.rpow_pos_of_pos (norm_pos_iff.2 (div_ne_zero (dmin_ne_zero X hx τ _) (dmin_ne_zero X hx τ _))) _).ne'`. Rewrite using `[mul_eq_zero, or_iff_left this, norm_eq_zero]`.
-/
theorem pnorm_eq_zero_iff (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) : X.pnorm la P x = 0 ↔ P x = 0 := by
  unfold Data.pnorm
  have : (∏ τ, ∏ i : Fin r,
      ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ => ?_
    exact (Real.rpow_pos_of_pos (norm_pos_iff.2
      (div_ne_zero (dmin_ne_zero X hx τ _) (dmin_ne_zero X hx τ _))) _).ne'
  rw [mul_eq_zero, or_iff_left this, norm_eq_zero]

/- English proof (translation)
Take `⟨n, hn, h⟩` from `X.χ_fin 0`. Establish `h0 : X.χ 0 γ ≠ 0` using `fun h0 => by`. Use `h γ hγ` as an intermediate fact. Rewrite `this` using `[h0, zero_pow hn.ne']`. Conclude with `zero_ne_one this`.

Establish `h1` using `X.χ_add 0 0 γ hγ`. Rewrite `h1` using `[add_zero]`. Conclude with `(mul_right_eq_self₀.1 h1.symm).resolve_right h0`.
-/
theorem chi_zero (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) : X.χ 0 γ = 1 := by
  obtain ⟨n, hn, h⟩ := X.χ_fin 0
  have h0 : X.χ 0 γ ≠ 0 := fun h0 => by
    have := h γ hγ
    rw [h0, zero_pow hn.ne'] at this
    exact zero_ne_one this
  have h1 := X.χ_add 0 0 γ hγ
  rw [add_zero] at h1
  exact (mul_right_eq_self₀.1 h1.symm).resolve_right h0

/- English proof (translation)
Use `⟨⟨differentiableOn_const _, fun x _ b _ => ?_, fun γ hγ x _ => ?_⟩, fun x => ?_⟩` and prove the remaining obligations. Simplify using `[bchar]`. Simplify using `[chi_zero X hγ]`. Simplify using `[Data.pnorm]`.
-/
theorem one_isSec (X : Data E r) :
    X.IsSec 0 (fun _ => 1) ∧ ∀ x, X.pnorm 0 (fun _ => 1) x = 1 := by
  refine ⟨⟨differentiableOn_const _, fun x _ b _ => ?_, fun γ hγ x _ => ?_⟩, fun x => ?_⟩
  · simp [bchar]
  · simp [chi_zero X hγ]
  · simp [Data.pnorm]

/- English proof (translation)
Take `⟨x, hx⟩` from `dom_nonempty X`. Use function extensionality and compare the values at `τ i`. Set `b : Frame X.Ψ r` to `fun σ => Matrix.diagonal fun a => if σ = τ ∧ a = i then (2 : ℂ) else 1`. Establish `hb : b ∈ Bor X.Ψ r` using `fun σ => ⟨by`. Establish `: mat b σ = Matrix.diagonal fun a => if σ = τ ∧ a = i then (2 : ℂ) else 1` using `rfl`.

Rewrite using `[this, Matrix.det_diagonal]`. Use `Finset.prod_ne_zero_iff.2 fun a _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> norm_num,`. Use `fun a c hca => Matrix.diagonal_apply_ne _ hca.ne'⟩`. Establish `h1` using `h.2.1 x hx b hb`.

Establish `h2 : bchar la b = (2 : ℂ) ^ la τ i`. Unfold `bchar`. Rewrite using `[Finset.prod_eq_single τ, Finset.prod_eq_single i]`. Simplify using `[b]`. Introduce `a _ ha`.

Simplify using `[b, ha]`. Simplify using the standard rewrite rules. Introduce `σ _ hσ`. Simplify using `[b, hσ]`. Simplify using the standard rewrite rules.

Rewrite `h1` using `[h2, mul_one]`. Establish `h3 : ((2 : ℝ)) ^ la τ i = 1`. Use `congrArg norm h1` as an intermediate fact. Simplify `this.symm` using `[norm_zpow]`. Conclude with `(zpow_eq_one_iff_right₀ (by norm_num) (by norm_num)).1 h3`.
-/
theorem weight_eq_zero_of_one_isSec (X : Data E r) (la : Wt X.Ψ r)
    (h : X.IsSec la (fun _ => 1)) : la = 0 := by
  classical
  obtain ⟨x, hx⟩ := dom_nonempty X
  funext τ i
  let b : Frame X.Ψ r := fun σ => Matrix.diagonal fun a => if σ = τ ∧ a = i then (2 : ℂ) else 1
  have hb : b ∈ Bor X.Ψ r := fun σ => ⟨by
      have : mat b σ = Matrix.diagonal fun a => if σ = τ ∧ a = i then (2 : ℂ) else 1 := rfl
      rw [this, Matrix.det_diagonal]
      refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
      split_ifs <;> norm_num,
    fun a c hca => Matrix.diagonal_apply_ne _ hca.ne'⟩
  have h1 := h.2.1 x hx b hb
  have h2 : bchar la b = (2 : ℂ) ^ la τ i := by
    unfold bchar
    rw [Finset.prod_eq_single τ, Finset.prod_eq_single i]
    · simp [b]
    · intro a _ ha; simp [b, ha]
    · simp
    · intro σ _ hσ; simp [b, hσ]
    · simp
  rw [h2, mul_one] at h1
  have h3 : ((2 : ℝ)) ^ la τ i = 1 := by
    have := congrArg norm h1
    simpa [norm_zpow] using this.symm
  exact (zpow_eq_one_iff_right₀ (by norm_num) (by norm_num)).1 h3

/- English proof (translation)
Assemble the required witnesses or components as `⟨hP.1.congr hQ, fun x hx b hb => by rw [hQ _ (hB x hx b hb), hQ x hx, hP.2.1 x hx b hb], fun γ hγ x hx => by rw [hQ _ (hΓ γ hγ x hx), hQ x hx, hP.2.2 γ hγ x hx]⟩`.
-/
theorem isSec_congr_on_dom (X : Data E (r + 1)) (la : Wt X.Ψ (r + 1))
    (P : Frame X.Ψ (r + 1) → ℂ) (hP : X.IsSec la P) (Q : Frame X.Ψ (r + 1) → ℂ)
    (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ (r + 1), rmul x b ∈ X.dom)
    (hΓ : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, lact γ x ∈ X.dom)
    (hQ : ∀ x ∈ X.dom, Q x = P x) : X.IsSec la Q :=
  ⟨hP.1.congr hQ, fun x hx b hb => by rw [hQ _ (hB x hx b hb), hQ x hx, hP.2.1 x hx b hb],
    fun γ hγ x hx => by rw [hQ _ (hΓ γ hγ x hx), hQ x hx, hP.2.2 γ hγ x hx]⟩

end GlobalTheory.FlagSecProbe
