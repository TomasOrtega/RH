import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicDescentPunctPolydiscLogCoverStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtensionAcrossCoordinateHyperplanesStatement
open GlobalTheory.ShFam.Hor

namespace GlobalTheory

/- English proof (translation)
Simplify using `[dotProduct, Matrix.mulVec, Complex.im_sum, Finset.mul_sum, Complex.mul_im]`.
-/
theorem periodVec_im_dot {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (v : Fin g → ℤ) :
    (dotProduct (fun i => (v i : ℂ)) (M.mulVec (fun i => (v i : ℂ)))).im
      = dotProduct (fun i => (v i : ℝ)) ((M.map Complex.im).mulVec (fun i => (v i : ℝ))) := by
  simp [dotProduct, Matrix.mulVec, Complex.im_sum, Finset.mul_sum, Complex.mul_im]

/- English proof (translation)
Establish `h1 : 0 ≤ dotProduct (fun i => (v i : ℝ)) ((M.map Complex.im).mulVec (fun i => (v i : ℝ)))`. Use `hM.posSemidef.dotProduct_mulVec_nonneg (fun i => (v i : ℝ))` as an intermediate fact. Simplify using `using this`. Rewrite using `[Complex.norm_exp, Real.exp_le_one_iff]`. Establish `: (2 * Real.pi * Complex.I * dotProduct (fun i => (v i : ℂ)) (M.mulVec (fun i => (v i : ℂ)))).re = -(2 * Real.pi) * (dotProduct (fun i => (v i : ℂ)) (M.mulVec (fun i => (v i : ℂ)))).im`.

Simplify using `[Complex.mul_re, Complex.mul_im]`. Rewrite using `[this, periodVec_im_dot]`. Use `Real.pi_pos` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem periodVec_norm_exp_le {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (hM : (M.map Complex.im).PosDef)
    (v : Fin g → ℤ) :
    ‖Complex.exp (2 * Real.pi * Complex.I *
      dotProduct (fun i => (v i : ℂ)) (M.mulVec (fun i => (v i : ℂ))))‖ ≤ 1 := by
  have h1 : 0 ≤ dotProduct (fun i => (v i : ℝ)) ((M.map Complex.im).mulVec (fun i => (v i : ℝ))) := by
    have := hM.posSemidef.dotProduct_mulVec_nonneg (fun i => (v i : ℝ))
    simpa using this
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  have : (2 * Real.pi * Complex.I *
      dotProduct (fun i => (v i : ℂ)) (M.mulVec (fun i => (v i : ℂ)))).re
      = -(2 * Real.pi) * (dotProduct (fun i => (v i : ℂ)) (M.mulVec (fun i => (v i : ℂ)))).im := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this, periodVec_im_dot]
  have := Real.pi_pos
  nlinarith

end GlobalTheory

namespace GlobalTheory

/- English proof (translation)
Introduce `n a g ha ρ₁ τ B v hρ0 hρ1 hdiff hpos hmono hm`. Set `vC : Fin g → ℂ` to `fun i => (v i : ℂ)`. Set `m : Fin a → ℤ` to `fun k => dotProduct v ((B k).mulVec v)`. Establish `hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0`. Simplify using `[Real.pi_ne_zero, Complex.I_ne_zero]`.

Establish `hcd : ∀ x : ℂ, 2 * Real.pi * Complex.I * (x / (2 * Real.pi * Complex.I)) = x` using `fun x => by`. Clear the denominators using the available nonvanishing facts. Set `h : (Fin n → ℂ) → ℂ` to `fun s => dotProduct vC ((τ s).mulVec vC) - ∑ k, s (Fin.castLE ha k) * ((m k : ℤ) : ℂ) / (2 * Real.pi * Complex.I)`. Establish `hdh : DifferentiableOn ℂ h {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁}`. Apply `DifferentiableOn.sub` to reduce the goal to its premises.

Simplify using `only [dotProduct, Matrix.mulVec]`. Apply `DifferentiableOn.fun_sum` to reduce the goal to its premises. Introduce `i _`. Apply `DifferentiableOn.mul (differentiableOn_const _)` to reduce the goal to its premises. Apply `DifferentiableOn.fun_sum` to reduce the goal to its premises.

Introduce `j _`. Conclude with `(hdiff i j).mul (differentiableOn_const _)`. Apply `DifferentiableOn.fun_sum` to reduce the goal to its premises. Introduce `k _`. Simplify using `only [div_eq_mul_inv]`.

Apply `DifferentiableOn.mul_const` to reduce the goal to its premises. Apply `DifferentiableOn.mul_const` to reduce the goal to its premises. Conclude with `differentiableOn_pi.mp differentiableOn_id (Fin.castLE ha k)`. Establish `hQ : ∀ k : Fin a, dotProduct vC (((B k).map (Int.cast : ℤ → ℂ)).mulVec vC) = ((m k : ℤ) : ℂ)`. Introduce `k`.

Simplify using `[vC, m, dotProduct, Matrix.mulVec, Int.cast_sum, Int.cast_mul]`. Establish `hinv : ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → ∀ k : Fin n, (k : ℕ) < a → h (s + Pi.single k (2 * Real.pi * Complex.I)) = h s`. Introduce `s hs hb k hk`. Take `⟨k', rfl⟩ : ∃ k' : Fin a, Fin.castLE ha k' = k` from `⟨⟨k, hk⟩, Fin.ext rfl⟩`. Establish `hτ` using `hmono s hs hb k'`.

Simplify using `only [h]`. Rewrite using `[hτ, Matrix.add_mulVec, dotProduct_add, hQ k']`. Establish `hsum : ∑ j, (s + Pi.single (Fin.castLE ha k') (2 * Real.pi * Complex.I) : Fin n → ℂ) (Fin.castLE ha j) * ((m j : ℤ) : ℂ) / (2 * Real.pi * Complex.I) = ∑ j, s (Fin.castLE ha j) * ((m j : ℤ) : ℂ) / (2 * Real.pi * Complex.I) + ((m k' : ℤ) : ℂ)`. Simplify using `only [Pi.add_apply, add_mul, add_div, Finset.sum_add_distrib]`. Use `congr 1`.

Simplify using `only [Pi.single_apply, (Fin.castLE_injective ha).eq_iff, ite_mul, zero_mul, ite_div, zero_div, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hsum]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨H, hHd, hHe⟩` from `GlobalTheory.T.exists_holomorphic_descent_punctPolydisc_logCover n a ρ₁ h hρ0 hρ1 hdh hinv`.

Set `m' : Fin n → ℕ` to `fun j => if hj : (j : ℕ) < a then (m ⟨j, hj⟩).toNat else 0`. Establish `hm0 : ∀ k, (((m k).toNat : ℕ) : ℂ) = ((m k : ℤ) : ℂ)` using `fun k => by`. Use `Int.toNat_of_nonneg (hm k)` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `hbound : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ₁, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Complex.exp (2 * Real.pi * Complex.I * H z)‖ * ∏ k, ‖z k‖ ^ m' k ≤ 1`.

Introduce `z hz hz0`. Set `s : Fin n → ℂ` to `fun j => if (j : ℕ) < a then Complex.log (z j) else z j`. Establish `hzj : ∀ j, ‖z j‖ < ρ₁` using `fun j => lt_of_le_of_lt (norm_le_pi_norm z j) (by simpa using hz)`. Establish `hls : logExp a s = z`. Use function extensionality and compare the values at `j`.

Simplify using `only [logExp, s]`. Use `split_ifs with hj`. Conclude with `Complex.exp_log (hz0 j hj)`. Both sides reduce to the same expression. Establish `hsD : s ∈ logDom n a`.

Simplify using `only [logDom, Set.mem_setOf_eq]`. Introduce `j`. Simplify using `only [s]`. Use `split_ifs with hj`. Rewrite using `[Complex.log_re]`.

Conclude with `Real.log_neg (norm_pos_iff.2 (hz0 j hj)) (lt_of_lt_of_le (hzj j) hρ1)`. Conclude with `lt_of_lt_of_le (hzj j) hρ1`. Establish `hb' : logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁` using `by rw [hls]; exact hz`. Establish `hHz : h s = H z` using `by rw [hHe s hsD hb', hls]`. Establish `hprod : ∏ j, (z j) ^ m' j = ∏ k : Fin a, (z (Fin.castLE ha k)) ^ (m k).toNat`.

Use `symm`. Apply `Finset.prod_of_injOn (Fin.castLE ha)` to reduce the goal to its premises. Introduce `x _ y _ hxy`. Conclude with `Fin.castLE_injective ha hxy`. Introduce `x _`.

Simplify using the standard rewrite rules. Introduce `j _ hj`. Establish `: ¬ (j : ℕ) < a`. Introduce `hlt; apply hj; exact ⟨⟨j, hlt⟩, by simp, Fin.ext rfl⟩`. Simplify using `[m', this]`.

Introduce `k _`. Simplify using `[m', Fin.coe_castLE, k.isLt]`. Establish `hexp : ∀ k : Fin a, (z (Fin.castLE ha k)) ^ (m k).toNat = Complex.exp (s (Fin.castLE ha k) * ((m k : ℤ) : ℂ))`. Introduce `k`. Establish `hk : ((Fin.castLE ha k : Fin n) : ℕ) < a` using `by simp`.

Rewrite using `[mul_comm, ← hm0 k, Complex.exp_nat_mul]`. Use `congr 1`. Simplify using `only [s, if_pos hk]`. Conclude with `(Complex.exp_log (hz0 _ hk)).symm`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[norm_mul, norm_prod, hHz]`. Simplify using `only [norm_pow]`. Use `_ = ‖Complex.exp (2 * Real.pi * Complex.I * dotProduct vC ((τ s).mulVec vC))‖ := by`. Rewrite using `[hprod, Finset.prod_congr rfl (fun k _ => hexp k), ← Complex.exp_sum, ← Complex.exp_add]`. Use `congr 2`.

Simplify using `only [h]`. Rewrite using `[mul_sub, Finset.mul_sum, Finset.sum_congr rfl (fun k _ => hcd _)]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ 1 := periodVec_norm_exp_le _ (hpos s hsD hb').2 v`. Take `⟨F, hFd, hFe⟩` from `GlobalTheory.T.exists_holomorphic_extension_across_coordinate_hyperplanes n a ρ₁ H m' hρ0 hHd hbound`.

Use `⟨F, hFd, fun s hs hb => ?_⟩` and prove the remaining obligations. Rewrite using `[hFe _ hb (fun k hk => by simp [logExp, hk, Complex.exp_ne_zero])]`. Conclude with `hHe s hs hb`.
-/
theorem periodVec_extends : ∀ (n a g : ℕ) (ha : a ≤ n) (ρ₁ : ℝ) (τ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (v : Fin g → ℤ), 0 < ρ₁ → ρ₁ ≤ 1 → (∀ i j, DifferentiableOn ℂ (fun s => τ s i j) {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁}) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).IsSymm ∧ ((τ s).map Complex.im).PosDef) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → ∀ k : Fin a, τ (s + Pi.single (Fin.castLE ha k) (2 * Real.pi * Complex.I)) = τ s + (B k).map (Int.cast : ℤ → ℂ)) → (∀ k, 0 ≤ dotProduct v ((B k).mulVec v)) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F (Metric.ball 0 ρ₁) ∧ ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → dotProduct (fun i => (v i : ℂ)) ((τ s).mulVec (fun i => (v i : ℂ))) - ∑ k, s (Fin.castLE ha k) * ((dotProduct v ((B k).mulVec v) : ℤ) : ℂ) / (2 * Real.pi * Complex.I) = F (logExp a s) := by
  intro n a g ha ρ₁ τ B v hρ0 hρ1 hdiff hpos hmono hm
  let vC : Fin g → ℂ := fun i => (v i : ℂ)
  let m : Fin a → ℤ := fun k => dotProduct v ((B k).mulVec v)
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hcd : ∀ x : ℂ, 2 * Real.pi * Complex.I * (x / (2 * Real.pi * Complex.I)) = x := fun x => by
    field_simp
  let h : (Fin n → ℂ) → ℂ := fun s => dotProduct vC ((τ s).mulVec vC) -
    ∑ k, s (Fin.castLE ha k) * ((m k : ℤ) : ℂ) / (2 * Real.pi * Complex.I)
  have hdh : DifferentiableOn ℂ h
      {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁} := by
    apply DifferentiableOn.sub
    · simp only [dotProduct, Matrix.mulVec]
      apply DifferentiableOn.fun_sum; intro i _
      apply DifferentiableOn.mul (differentiableOn_const _)
      apply DifferentiableOn.fun_sum; intro j _
      exact (hdiff i j).mul (differentiableOn_const _)
    · apply DifferentiableOn.fun_sum; intro k _
      simp only [div_eq_mul_inv]
      apply DifferentiableOn.mul_const
      apply DifferentiableOn.mul_const
      exact differentiableOn_pi.mp differentiableOn_id (Fin.castLE ha k)
  have hQ : ∀ k : Fin a, dotProduct vC (((B k).map (Int.cast : ℤ → ℂ)).mulVec vC) = ((m k : ℤ) : ℂ) := by
    intro k
    simp [vC, m, dotProduct, Matrix.mulVec, Int.cast_sum, Int.cast_mul]
  have hinv : ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ →
      ∀ k : Fin n, (k : ℕ) < a → h (s + Pi.single k (2 * Real.pi * Complex.I)) = h s := by
    intro s hs hb k hk
    obtain ⟨k', rfl⟩ : ∃ k' : Fin a, Fin.castLE ha k' = k := ⟨⟨k, hk⟩, Fin.ext rfl⟩
    have hτ := hmono s hs hb k'
    simp only [h]
    rw [hτ, Matrix.add_mulVec, dotProduct_add, hQ k']
    have hsum : ∑ j, (s + Pi.single (Fin.castLE ha k') (2 * Real.pi * Complex.I) : Fin n → ℂ) (Fin.castLE ha j)
        * ((m j : ℤ) : ℂ) / (2 * Real.pi * Complex.I)
        = ∑ j, s (Fin.castLE ha j) * ((m j : ℤ) : ℂ) / (2 * Real.pi * Complex.I) + ((m k' : ℤ) : ℂ) := by
      simp only [Pi.add_apply, add_mul, add_div, Finset.sum_add_distrib]
      congr 1
      simp only [Pi.single_apply, (Fin.castLE_injective ha).eq_iff, ite_mul, zero_mul, ite_div, zero_div,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      field_simp
    rw [hsum]; ring
  obtain ⟨H, hHd, hHe⟩ := GlobalTheory.T.exists_holomorphic_descent_punctPolydisc_logCover n a ρ₁ h hρ0 hρ1 hdh hinv
  let m' : Fin n → ℕ := fun j => if hj : (j : ℕ) < a then (m ⟨j, hj⟩).toNat else 0
  have hm0 : ∀ k, (((m k).toNat : ℕ) : ℂ) = ((m k : ℤ) : ℂ) := fun k => by
    have := Int.toNat_of_nonneg (hm k)
    exact_mod_cast this
  have hbound : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ₁, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) →
      ‖Complex.exp (2 * Real.pi * Complex.I * H z)‖ * ∏ k, ‖z k‖ ^ m' k ≤ 1 := by
    intro z hz hz0
    let s : Fin n → ℂ := fun j => if (j : ℕ) < a then Complex.log (z j) else z j
    have hzj : ∀ j, ‖z j‖ < ρ₁ := fun j =>
      lt_of_le_of_lt (norm_le_pi_norm z j) (by simpa using hz)
    have hls : logExp a s = z := by
      funext j; simp only [logExp, s]; split_ifs with hj
      · exact Complex.exp_log (hz0 j hj)
      · rfl
    have hsD : s ∈ logDom n a := by
      simp only [logDom, Set.mem_setOf_eq]
      intro j; simp only [s]; split_ifs with hj
      · rw [Complex.log_re]
        exact Real.log_neg (norm_pos_iff.2 (hz0 j hj)) (lt_of_lt_of_le (hzj j) hρ1)
      · exact lt_of_lt_of_le (hzj j) hρ1
    have hb' : logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ := by rw [hls]; exact hz
    have hHz : h s = H z := by rw [hHe s hsD hb', hls]
    have hprod : ∏ j, (z j) ^ m' j = ∏ k : Fin a, (z (Fin.castLE ha k)) ^ (m k).toNat := by
      symm
      apply Finset.prod_of_injOn (Fin.castLE ha)
      · intro x _ y _ hxy; exact Fin.castLE_injective ha hxy
      · intro x _; simp
      · intro j _ hj
        have : ¬ (j : ℕ) < a := by
          intro hlt; apply hj; exact ⟨⟨j, hlt⟩, by simp, Fin.ext rfl⟩
        simp [m', this]
      · intro k _; simp [m', Fin.coe_castLE, k.isLt]
    have hexp : ∀ k : Fin a, (z (Fin.castLE ha k)) ^ (m k).toNat
        = Complex.exp (s (Fin.castLE ha k) * ((m k : ℤ) : ℂ)) := by
      intro k
      have hk : ((Fin.castLE ha k : Fin n) : ℕ) < a := by simp
      rw [mul_comm, ← hm0 k, Complex.exp_nat_mul]
      congr 1
      simp only [s, if_pos hk]; exact (Complex.exp_log (hz0 _ hk)).symm
    calc ‖Complex.exp (2 * Real.pi * Complex.I * H z)‖ * ∏ k, ‖z k‖ ^ m' k
        = ‖Complex.exp (2 * Real.pi * Complex.I * h s) * ∏ k, z k ^ m' k‖ := by
          rw [norm_mul, norm_prod, hHz]; simp only [norm_pow]
      _ = ‖Complex.exp (2 * Real.pi * Complex.I * dotProduct vC ((τ s).mulVec vC))‖ := by
          rw [hprod, Finset.prod_congr rfl (fun k _ => hexp k), ← Complex.exp_sum, ← Complex.exp_add]
          congr 2
          simp only [h]
          rw [mul_sub, Finset.mul_sum, Finset.sum_congr rfl (fun k _ => hcd _)]
          ring
      _ ≤ 1 := periodVec_norm_exp_le _ (hpos s hsD hb').2 v
  obtain ⟨F, hFd, hFe⟩ := GlobalTheory.T.exists_holomorphic_extension_across_coordinate_hyperplanes n a ρ₁ H m' hρ0 hHd hbound
  refine ⟨F, hFd, fun s hs hb => ?_⟩
  rw [hFe _ hb (fun k hk => by simp [logExp, hk, Complex.exp_ne_zero])]
  exact hHe s hs hb

end GlobalTheory
