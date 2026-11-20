import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SummableNormSiegelThetaSeriesTerms

open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW.ThetaProd

/- English proof (translation)
Use `⟨fun x hx k i => ?_, fun x y hy => ?_⟩` and prove the remaining obligations. Use `(h.1 x hx k i).nsmul S` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Use `h.2 x ((S : ℚ) • y) fun k i => by simpa using (hy k i).nsmul S` as an intermediate fact. Rewrite using `[← this, smul_smul, Nat.cast_mul, mul_comm]`.
-/
theorem hasLevel_mul {κ ι : Type} [Fintype κ] [Fintype ι] {R : ℕ} (S : ℕ)
    {φ : Matrix κ ι ℚ → ℂ} (h : HasLevel R φ) : HasLevel (S * R) φ := by
  refine ⟨fun x hx k i => ?_, fun x y hy => ?_⟩
  · have := (h.1 x hx k i).nsmul S
    simpa [mul_assoc] using this
  · have := h.2 x ((S : ℚ) • y) fun k i => by simpa using (hy k i).nsmul S
    rw [← this, smul_smul, Nat.cast_mul, mul_comm]

/- English proof (translation)
Take `⟨R₁, hR₁, h₁⟩` from `h₁`. Take `⟨R₂, hR₂, h₂⟩` from `h₂`. Establish `g₁` using `hasLevel_mul R₂ h₁`. Establish `g₂` using `hasLevel_mul R₁ h₂`. Rewrite `g₁` using `[mul_comm]`.

Use `⟨R₁ * R₂, by positivity, fun x hx k i => ?_, fun x y hy => ?_⟩` and prove the remaining obligations. Establish `a₁` using `g₁.1 _ (left_ne_zero_of_mul hx)`. Establish `a₂` using `g₂.1 _ ((map_ne_zero conj).1 (right_ne_zero_of_mul hx))`. Break down `i with i | i` into its components or cases. Conclude with `a₁ k i`.

Use `(a₂ k i).neg` as an intermediate fact. Simplify `this` using `[toCols₂]`. Establish `a₁` using `g₁.2 x.toCols₁ y.toCols₁ fun k i => hy k (Sum.inl i)`. Establish `a₂` using `g₂.2 (-x.toCols₂) (-y.toCols₂) fun k i => (hy k (Sum.inr i)).neg`. Establish `e₁ : (x + ((R₁ * R₂ : ℕ) : ℚ) • y).toCols₁ = x.toCols₁ + ((R₁ * R₂ : ℕ) : ℚ) • y.toCols₁` using `rfl`.

Establish `e₂ : -(x + ((R₁ * R₂ : ℕ) : ℚ) • y).toCols₂ = -x.toCols₂ + ((R₁ * R₂ : ℕ) : ℚ) • (-y.toCols₂)`. Rewrite using `[smul_neg, ← neg_add]`. Both sides reduce to the same expression. Simplify using `only [e₁, e₂, a₁, a₂]`.
-/
theorem isSB_prod {κ ι₁ ι₂ : Type} [Fintype κ] [Fintype ι₁] [Fintype ι₂]
    {φ₁ : Matrix κ ι₁ ℚ → ℂ} {φ₂ : Matrix κ ι₂ ℚ → ℂ} (h₁ : IsSB φ₁) (h₂ : IsSB φ₂) :
    IsSB (fun m : Matrix κ (ι₁ ⊕ ι₂) ℚ => φ₁ m.toCols₁ * conj (φ₂ (-m.toCols₂))) := by
  obtain ⟨R₁, hR₁, h₁⟩ := h₁
  obtain ⟨R₂, hR₂, h₂⟩ := h₂
  have g₁ := hasLevel_mul R₂ h₁
  have g₂ := hasLevel_mul R₁ h₂
  rw [mul_comm] at g₁
  refine ⟨R₁ * R₂, by positivity, fun x hx k i => ?_, fun x y hy => ?_⟩
  · have a₁ := g₁.1 _ (left_ne_zero_of_mul hx)
    have a₂ := g₂.1 _ ((map_ne_zero conj).1 (right_ne_zero_of_mul hx))
    rcases i with i | i
    · exact a₁ k i
    · have := (a₂ k i).neg
      simpa [toCols₂] using this
  · have a₁ := g₁.2 x.toCols₁ y.toCols₁ fun k i => hy k (Sum.inl i)
    have a₂ := g₂.2 (-x.toCols₂) (-y.toCols₂) fun k i => (hy k (Sum.inr i)).neg
    have e₁ : (x + ((R₁ * R₂ : ℕ) : ℚ) • y).toCols₁ =
      x.toCols₁ + ((R₁ * R₂ : ℕ) : ℚ) • y.toCols₁ := rfl
    have e₂ : -(x + ((R₁ * R₂ : ℕ) : ℚ) • y).toCols₂ =
      -x.toCols₂ + ((R₁ * R₂ : ℕ) : ℚ) • (-y.toCols₂) := by
      rw [smul_neg, ← neg_add]; rfl
    simp only [e₁, e₂, a₁, a₂]

/- English proof (translation)
Use `⟨Matrix.IsSymm.fromBlocks h₁.1 (by simp) (h₂.1.map _).neg, ?_⟩` and prove the remaining obligations. Establish `e : (Matrix.fromBlocks τ₁ 0 0 (-(τ₂.map conj))).map Complex.im = Matrix.fromBlocks (τ₁.map Complex.im) 0 0 (τ₂.map Complex.im)`. Apply the tactic sequence `ext (i | i) (j | j) <;> simp`. Rewrite using `[e]`. Use `Matrix.posDef_iff_dotProduct_mulVec.2 ⟨Matrix.IsHermitian.fromBlocks h₁.2.isHermitian (by simp) h₂.2.isHermitian, fun x hx => ?_⟩` and prove the remaining obligations.

Take `⟨u, v, rfl⟩ : ∃ u v, x = Sum.elim u v` from `⟨x ∘ Sum.inl, x ∘ Sum.inr, (Sum.elim_comp_inl_inr x).symm⟩`. Rewrite using `[star_trivial, fromBlocks_mulVec, sumElim_dotProduct_sumElim]`. Simplify using `only [Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, add_zero, zero_add]`. Establish `a` using `h₁.2.posSemidef.dotProduct_mulVec_nonneg u`. Establish `b` using `h₂.2.posSemidef.dotProduct_mulVec_nonneg v`.

Rewrite `a`, `b` using `[star_trivial]`. Distinguish the cases in `hu : u = 0`. Establish `hv : v ≠ 0`. Introduce and unpack `rfl`. Apply `hx` to reduce the goal to its premises.

Rewrite using `[hu]`. Apply the tactic sequence `ext (i | i) <;> rfl`. Use `h₂.2.dotProduct_mulVec_pos hv` as an intermediate fact. Rewrite `this` using `[star_trivial]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `h₁.2.dotProduct_mulVec_pos hu` as an intermediate fact. Rewrite `this` using `[star_trivial]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem fromBlocks_mem_siegel {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    {τ₁ : Matrix ι₁ ι₁ ℂ} {τ₂ : Matrix ι₂ ι₂ ℂ} (h₁ : τ₁ ∈ Siegel ι₁) (h₂ : τ₂ ∈ Siegel ι₂) :
    Matrix.fromBlocks τ₁ 0 0 (-(τ₂.map conj)) ∈ Siegel (ι₁ ⊕ ι₂) := by
  refine ⟨Matrix.IsSymm.fromBlocks h₁.1 (by simp) (h₂.1.map _).neg, ?_⟩
  have e : (Matrix.fromBlocks τ₁ 0 0 (-(τ₂.map conj))).map Complex.im =
      Matrix.fromBlocks (τ₁.map Complex.im) 0 0 (τ₂.map Complex.im) := by
    ext (i | i) (j | j) <;> simp
  rw [e]
  refine Matrix.posDef_iff_dotProduct_mulVec.2
    ⟨Matrix.IsHermitian.fromBlocks h₁.2.isHermitian (by simp) h₂.2.isHermitian, fun x hx => ?_⟩
  obtain ⟨u, v, rfl⟩ : ∃ u v, x = Sum.elim u v :=
    ⟨x ∘ Sum.inl, x ∘ Sum.inr, (Sum.elim_comp_inl_inr x).symm⟩
  rw [star_trivial, fromBlocks_mulVec, sumElim_dotProduct_sumElim]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, add_zero, zero_add]
  have a := h₁.2.posSemidef.dotProduct_mulVec_nonneg u
  have b := h₂.2.posSemidef.dotProduct_mulVec_nonneg v
  rw [star_trivial] at a b
  by_cases hu : u = 0
  · have hv : v ≠ 0 := by
      rintro rfl
      apply hx
      rw [hu]
      ext (i | i) <;> rfl
    have := h₂.2.dotProduct_mulVec_pos hv
    rw [star_trivial] at this
    linarith
  · have := h₁.2.dotProduct_mulVec_pos hu
    rw [star_trivial] at this
    linarith

def colsEquiv (κ ι₁ ι₂ : Type) : Matrix κ (ι₁ ⊕ ι₂) ℚ ≃ Matrix κ ι₁ ℚ × Matrix κ ι₂ ℚ where
  toFun m := (m.toCols₁, -m.toCols₂)
  invFun p := fromCols p.1 (-p.2)
  left_inv m := by simp
  right_inv p := by simp

/- English proof (translation)
Establish `h2 : conj (2 : ℂ) = 2` using `map_ofNat _ 2`. Simplify using `[dotProduct, mulVec, qv, Fintype.sum_sum_type, h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem row_exponent {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (τ₁ : Matrix ι₁ ι₁ ℂ) (τ₂ : Matrix ι₂ ι₂ ℂ) (ζ₁ : ι₁ → ℂ) (ζ₂ : ι₂ → ℂ) (v : ι₁ ⊕ ι₂ → ℚ) :
    qv v ⬝ᵥ Matrix.fromBlocks τ₁ 0 0 (-(τ₂.map conj)) *ᵥ qv v +
        2 * (qv v ⬝ᵥ Sum.elim ζ₁ (star ζ₂)) =
      (qv (fun i => v (Sum.inl i)) ⬝ᵥ τ₁ *ᵥ qv (fun i => v (Sum.inl i)) +
        2 * (qv (fun i => v (Sum.inl i)) ⬝ᵥ ζ₁)) -
      conj (qv (fun i => -v (Sum.inr i)) ⬝ᵥ τ₂ *ᵥ qv (fun i => -v (Sum.inr i)) +
        2 * (qv (fun i => -v (Sum.inr i)) ⬝ᵥ ζ₂)) := by
  have h2 : conj (2 : ℂ) = 2 := map_ofNat _ 2
  simp [dotProduct, mulVec, qv, Fintype.sum_sum_type, h2]
  ring

/- English proof (translation)
Introduce `κ ι₁ ι₂ _ _ _ _ _ φ₁ φ₂ h₁ h₂`. Use `⟨isSB_prod h₁ h₂, fun τ₁ t₁ τ₂ t₂ => ⟨fromBlocks_mem_siegel t₁ t₂, fun ζ₁ ζ₂ => ?_⟩⟩` and prove the remaining obligations. Establish `s₁` using `SiegelSum.summable_norm_thetaTerm κ ι₁ φ₁ h₁ τ₁ t₁ ζ₁`. Establish `s₂` using `SiegelSum.summable_norm_thetaTerm κ ι₂ φ₂ h₂ τ₂ t₂ ζ₂`. Unfold `thS`.

Rewrite using `[Complex.conj_tsum, tsum_mul_tsum_of_summable_norm s₁ (by simpa only [Complex.norm_conj] using s₂), ← (colsEquiv κ ι₁ ι₂).tsum_eq]`. Use `tsum_congr fun m => ?_` and prove the remaining obligations. Simplify using `only [row_exponent, Finset.sum_sub_distrib, mul_sub, ← map_sum]`. Rewrite using `[map_mul, ← Complex.exp_conj, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I, sub_eq_add_neg, Complex.exp_add, mul_mul_mul_comm, mul_neg, neg_mul]`. Both sides reduce to the same expression.
-/
theorem thS_mul_conj_thS : ∀ (κ ι₁ ι₂ : Type) [Fintype κ] [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] (φ₁ : Matrix κ ι₁ ℚ → ℂ) (φ₂ : Matrix κ ι₂ ℚ → ℂ), IsSB φ₁ → IsSB φ₂ → IsSB (fun m : Matrix κ (ι₁ ⊕ ι₂) ℚ => φ₁ m.toCols₁ * conj (φ₂ (-m.toCols₂))) ∧ ∀ τ₁ ∈ Siegel ι₁, ∀ τ₂ ∈ Siegel ι₂, Matrix.fromBlocks τ₁ 0 0 (-(τ₂.map conj)) ∈ Siegel (ι₁ ⊕ ι₂) ∧ ∀ (ζ₁ : κ → ι₁ → ℂ) (ζ₂ : κ → ι₂ → ℂ), thS φ₁ τ₁ ζ₁ * conj (thS φ₂ τ₂ ζ₂) = thS (fun m : Matrix κ (ι₁ ⊕ ι₂) ℚ => φ₁ m.toCols₁ * conj (φ₂ (-m.toCols₂))) (Matrix.fromBlocks τ₁ 0 0 (-(τ₂.map conj))) (fun k => Sum.elim (ζ₁ k) (star (ζ₂ k))) := by
  intro κ ι₁ ι₂ _ _ _ _ _ φ₁ φ₂ h₁ h₂
  refine ⟨isSB_prod h₁ h₂, fun τ₁ t₁ τ₂ t₂ => ⟨fromBlocks_mem_siegel t₁ t₂, fun ζ₁ ζ₂ => ?_⟩⟩
  have s₁ := SiegelSum.summable_norm_thetaTerm κ ι₁ φ₁ h₁ τ₁ t₁ ζ₁
  have s₂ := SiegelSum.summable_norm_thetaTerm κ ι₂ φ₂ h₂ τ₂ t₂ ζ₂
  unfold thS
  rw [Complex.conj_tsum, tsum_mul_tsum_of_summable_norm s₁
    (by simpa only [Complex.norm_conj] using s₂), ← (colsEquiv κ ι₁ ι₂).tsum_eq]
  refine tsum_congr fun m => ?_
  simp only [row_exponent, Finset.sum_sub_distrib, mul_sub, ← map_sum]
  rw [map_mul, ← Complex.exp_conj, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I,
    sub_eq_add_neg, Complex.exp_add, mul_mul_mul_comm, mul_neg, neg_mul]
  rfl

end GlobalTheory.SW.ThetaProd
