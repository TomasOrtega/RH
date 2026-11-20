import ReciprocityTheory.SemistableReduction.SemiDegF

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, S.c_invol, S.G_herm, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem herm_cGP {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (P : Matrix (Fin r) (Fin r) K) (a b : Fin r) :
    S.c (((P.map S.c)ᵀ * S.G * P) a b) = ((P.map S.c)ᵀ * S.G * P) b a := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
    S.c_invol, S.G_herm, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Establish `h` using `herm_cGP S P i i`. Rewrite `h` using `[hJ]`. Simplify `h` using `[wittMat, Matrix.of_apply, not_lt.2 h1, h1, h2]`.
-/
theorem g_fix {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (P : Matrix (Fin r) (Fin r) K) (m : ℕ) (g : Fin r → K)
    (hJ : (P.map S.c)ᵀ * S.G * P = wittMat r m g) (i : Fin r) (h1 : m ≤ (i : ℕ))
    (h2 : (i : ℕ) + m < r) : S.c (g i) = g i := by
  have h := herm_cGP S P i i
  rw [hJ] at h
  simpa [wittMat, Matrix.of_apply, not_lt.2 h1, h1, h2] using h

/- English proof (translation)
Establish `hPu : IsUnit P.det` using `isUnit_iff_ne_zero.2 hP`. Establish `hPP : P * P⁻¹ = 1` using `Matrix.mul_nonsing_inv P hPu`. Establish `hPP' : P⁻¹ * P = 1` using `Matrix.nonsing_inv_mul P hPu`. Establish `hG : S.G = ((P⁻¹).map S.c)ᵀ * wittMat r m g * P⁻¹`. Rewrite using `[← hJ]`.

Establish `h1 : ((P⁻¹).map S.c)ᵀ * (P.map S.c)ᵀ = 1`. Rewrite using `[← Matrix.transpose_mul, ← Matrix.map_mul, hPP, Matrix.map_one _ (map_zero S.c) (map_one S.c), Matrix.transpose_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h1, hPP, Matrix.one_mul, Matrix.mul_one]`. Use `_ = _ := by simp only [Matrix.mul_assoc]`.

Establish `key : ∀ σ : K →+* ℂ,`. Set `A` to `(P⁻¹).map σ`. Set `D` to `diagMet (adMet r m g dd) σ`. Use the proof step `(Aᴴ * D * A).PosDef ∧ Aᴴ * D * A * (S.G.map σ)⁻¹ * (Aᴴ * D * A) = S.G.map σ := by`. Introduce `σ A D`.

Use `set Ai := P.map σ with hAi`. Establish `e1 : A * Ai = 1`. Simplify using `only [A, Ai]`. Rewrite using `[← Matrix.map_mul, hPP', Matrix.map_one _ (map_zero σ) (map_one σ)]`. Establish `e2 : Ai * A = 1`.

Simplify using `only [A, Ai]`. Rewrite using `[← Matrix.map_mul, hPP, Matrix.map_one _ (map_zero σ) (map_one σ)]`. Establish `e3 : Aiᴴ * Aᴴ = 1` using `by rw [← Matrix.conjTranspose_mul, e1, Matrix.conjTranspose_one]`. Establish `e4 : Aᴴ * Aiᴴ = 1` using `by rw [← Matrix.conjTranspose_mul, e2, Matrix.conjTranspose_one]`. Establish `hpos : ∀ i, 0 < adMet r m g dd σ i` using `adMet_pos r m g dd hdd hg σ`.

Set `Dinv : Matrix (Fin r) (Fin r) ℂ` to `diagonal fun i => (((adMet r m g dd σ i : ℝ) : ℂ))⁻¹`. Establish `e5 : D * Dinv = 1`. Simplify using `only [D, Dinv, diagMet, Matrix.diagonal_mul_diagonal]`. Rewrite using `[← Matrix.diagonal_one]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Establish `: ((adMet r m g dd σ i : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast (hpos i).ne'`. Conclude with `mul_inv_cancel₀ this`. Establish `hGσ : S.G.map σ = Aᴴ * (wittMat r m g).map σ * A`. Rewrite using `[hG, Matrix.map_mul, Matrix.map_mul]`.

Use `congr 2`. Use extensionality with `a b`. Simplify using `[A, Matrix.conjTranspose_apply, S.c_emb]`. Establish `hreal : ∀ i : Fin r, m ≤ (i : ℕ) → (i : ℕ) + m < r → conj (σ (g i)) = σ (g i)`. Introduce `i h1 h2`.

Rewrite using `[← S.c_emb, g_fix S P m g hJ i h1 h2]`. Establish `hKey : (wittMat r m g).map σ * Dinv * (wittMat r m g).map σ = D`. Rewrite using `[wittMat_map_mul]`. Simplify using `only [D, diagMet]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Conclude with `wVal_adMet r m g dd h2m hg σ hreal i`. Use `set Y := S.G.map σ with hY`. Use `set Jσ := (wittMat r m g).map σ with hJσ`. Use `set H := Aᴴ * D * A with hH`.

Use `set Hinv := Ai * Dinv * Aiᴴ with hHinv`. Establish `hHH : H * Hinv = 1`. Combine the equalities or inequalities in the displayed calculation. Establish `hHH' : Hinv * H = 1` using `mul_eq_one_comm.1 hHH`. Establish `hYHY : Y * Hinv * Y = H`.

Rewrite using `[hGσ]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Hinv, Matrix.mul_assoc]`. Use `_ = Aᴴ * (Jσ * Dinv * Jσ) * A := by`. Rewrite using `[e1, e3, Matrix.mul_one, Matrix.mul_one]`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = H := by rw [hKey]`. Establish `hYinv : Y⁻¹ = Hinv * Y * Hinv`. Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hD : D.PosDef`. Simplify using `only [D, diagMet]`. Conclude with `Matrix.posDef_diagonal_iff.2 fun i => by exact_mod_cast hpos i`. Establish `hAu : IsUnit A` using `(Matrix.isUnit_iff_isUnit_det A).2 (Matrix.isUnit_det_of_right_inverse e1)`.

Conclude with `hD.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hAu)`. Rewrite using `[hYinv]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Y := by rw [hHH, hHH', Matrix.one_mul, Matrix.mul_one]`.

Use `⟨⟨fun σ => ((P⁻¹).map σ)ᴴ * diagMet (adMet r m g dd) σ * (P⁻¹).map σ, fun σ => (key σ).1, fun σ => (key σ).2, ?_⟩, fun σ => rfl⟩` and prove the remaining obligations. Introduce `σ`. Establish `hmap : (P⁻¹).map ((starRingEnd ℂ).comp σ) = ((P⁻¹).map σ).map (starRingEnd ℂ)`. Rewrite using `[Matrix.map_map]`. Both sides reduce to the same expression.

Establish `hDc : diagMet (adMet r m g dd) ((starRingEnd ℂ).comp σ) = (diagMet (adMet r m g dd) σ).map (starRingEnd ℂ)`. Simplify using `only [diagMet, adMet_conj]`. Rewrite using `[Matrix.diagonal_map (map_zero _)]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules. Use `show ((P⁻¹).map ((starRingEnd ℂ).comp σ))ᴴ * diagMet (adMet r m g dd) ((starRingEnd ℂ).comp σ) * (P⁻¹).map ((starRingEnd ℂ).comp σ) = (((P⁻¹).map σ)ᴴ * diagMet (adMet r m g dd) σ * (P⁻¹).map σ).map (starRingEnd ℂ)`. Rewrite using `[hmap, hDc, Matrix.map_mul, Matrix.map_mul, Matrix.conjTranspose_map]`. Introduce `x`. Simplify using the standard rewrite rules.
-/
theorem exists_adapted_majorant {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (P : Matrix (Fin r) (Fin r) K) (m : ℕ) (g : Fin r → K) (dd : Fin r → ℝ)
    (hP : P.det ≠ 0) (h2m : 2 * m ≤ r) (hJ : (P.map S.c)ᵀ * S.G * P = wittMat r m g)
    (hdd : ∀ i, 0 < dd i) (hg : ∀ i : Fin r, m ≤ (i : ℕ) → (i : ℕ) + m < r → g i ≠ 0) :
    ∃ M : Majorant S, ∀ σ,
      M.H σ = ((P⁻¹).map σ)ᴴ * diagMet (adMet r m g dd) σ * (P⁻¹).map σ := by
  classical
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.2 hP
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPu
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPu
  have hG : S.G = ((P⁻¹).map S.c)ᵀ * wittMat r m g * P⁻¹ := by
    rw [← hJ]
    have h1 : ((P⁻¹).map S.c)ᵀ * (P.map S.c)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, hPP,
        Matrix.map_one _ (map_zero S.c) (map_one S.c), Matrix.transpose_one]
    calc S.G = ((P⁻¹).map S.c)ᵀ * (P.map S.c)ᵀ * S.G * (P * P⁻¹) := by
          rw [h1, hPP, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]

  have key : ∀ σ : K →+* ℂ,
      let A := (P⁻¹).map σ
      let D := diagMet (adMet r m g dd) σ
      (Aᴴ * D * A).PosDef ∧ Aᴴ * D * A * (S.G.map σ)⁻¹ * (Aᴴ * D * A) = S.G.map σ := by
    intro σ A D
    set Ai := P.map σ with hAi
    have e1 : A * Ai = 1 := by
      simp only [A, Ai]
      rw [← Matrix.map_mul, hPP', Matrix.map_one _ (map_zero σ) (map_one σ)]
    have e2 : Ai * A = 1 := by
      simp only [A, Ai]
      rw [← Matrix.map_mul, hPP, Matrix.map_one _ (map_zero σ) (map_one σ)]
    have e3 : Aiᴴ * Aᴴ = 1 := by rw [← Matrix.conjTranspose_mul, e1, Matrix.conjTranspose_one]
    have e4 : Aᴴ * Aiᴴ = 1 := by rw [← Matrix.conjTranspose_mul, e2, Matrix.conjTranspose_one]
    have hpos : ∀ i, 0 < adMet r m g dd σ i := adMet_pos r m g dd hdd hg σ
    let Dinv : Matrix (Fin r) (Fin r) ℂ :=
      diagonal fun i => (((adMet r m g dd σ i : ℝ) : ℂ))⁻¹
    have e5 : D * Dinv = 1 := by
      simp only [D, Dinv, diagMet, Matrix.diagonal_mul_diagonal]
      rw [← Matrix.diagonal_one]
      congr 1
      funext i
      have : ((adMet r m g dd σ i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hpos i).ne'
      exact mul_inv_cancel₀ this
    have hGσ : S.G.map σ = Aᴴ * (wittMat r m g).map σ * A := by
      rw [hG, Matrix.map_mul, Matrix.map_mul]
      congr 2
      ext a b
      simp [A, Matrix.conjTranspose_apply, S.c_emb]
    have hreal : ∀ i : Fin r, m ≤ (i : ℕ) → (i : ℕ) + m < r → conj (σ (g i)) = σ (g i) := by
      intro i h1 h2
      rw [← S.c_emb, g_fix S P m g hJ i h1 h2]
    have hKey : (wittMat r m g).map σ * Dinv * (wittMat r m g).map σ = D := by
      rw [wittMat_map_mul]
      simp only [D, diagMet]
      congr 1
      funext i
      exact wVal_adMet r m g dd h2m hg σ hreal i
    set Y := S.G.map σ with hY
    set Jσ := (wittMat r m g).map σ with hJσ
    set H := Aᴴ * D * A with hH
    set Hinv := Ai * Dinv * Aiᴴ with hHinv
    have hHH : H * Hinv = 1 := by
      calc H * Hinv = Aᴴ * D * (A * Ai) * Dinv * Aiᴴ := by simp only [H, Hinv, Matrix.mul_assoc]
        _ = Aᴴ * (D * Dinv) * Aiᴴ := by rw [e1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = 1 := by rw [e5, Matrix.mul_one, e4]
    have hHH' : Hinv * H = 1 := mul_eq_one_comm.1 hHH
    have hYHY : Y * Hinv * Y = H := by
      rw [hGσ]
      calc Aᴴ * Jσ * A * Hinv * (Aᴴ * Jσ * A)
          = Aᴴ * Jσ * (A * Ai) * Dinv * (Aiᴴ * Aᴴ) * Jσ * A := by
            simp only [Hinv, Matrix.mul_assoc]
        _ = Aᴴ * (Jσ * Dinv * Jσ) * A := by
            rw [e1, e3, Matrix.mul_one, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = H := by rw [hKey]
    have hYinv : Y⁻¹ = Hinv * Y * Hinv := by
      apply Matrix.inv_eq_left_inv
      calc Hinv * Y * Hinv * Y = Hinv * (Y * Hinv * Y) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hYHY, hHH']
    refine ⟨?_, ?_⟩
    · have hD : D.PosDef := by
        simp only [D, diagMet]
        exact Matrix.posDef_diagonal_iff.2 fun i => by exact_mod_cast hpos i
      have hAu : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).2
        (Matrix.isUnit_det_of_right_inverse e1)
      exact hD.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hAu)
    · rw [hYinv]
      calc H * (Hinv * Y * Hinv) * H = (H * Hinv) * Y * (Hinv * H) := by
            simp only [Matrix.mul_assoc]
        _ = Y := by rw [hHH, hHH', Matrix.one_mul, Matrix.mul_one]
  refine ⟨⟨fun σ => ((P⁻¹).map σ)ᴴ * diagMet (adMet r m g dd) σ * (P⁻¹).map σ,
    fun σ => (key σ).1, fun σ => (key σ).2, ?_⟩, fun σ => rfl⟩
  intro σ
  have hmap : (P⁻¹).map ((starRingEnd ℂ).comp σ) = ((P⁻¹).map σ).map (starRingEnd ℂ) := by
    rw [Matrix.map_map]
    rfl
  have hDc : diagMet (adMet r m g dd) ((starRingEnd ℂ).comp σ) =
      (diagMet (adMet r m g dd) σ).map (starRingEnd ℂ) := by
    simp only [diagMet, adMet_conj]
    rw [Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    simp
  show ((P⁻¹).map ((starRingEnd ℂ).comp σ))ᴴ * diagMet (adMet r m g dd) ((starRingEnd ℂ).comp σ) *
      (P⁻¹).map ((starRingEnd ℂ).comp σ) =
    (((P⁻¹).map σ)ᴴ * diagMet (adMet r m g dd) σ * (P⁻¹).map σ).map (starRingEnd ℂ)
  rw [hmap, hDc, Matrix.map_mul, Matrix.map_mul, Matrix.conjTranspose_map]
  intro x
  simp

end ReciprocityTheory.MultiplicativeHeights.SemiPt
