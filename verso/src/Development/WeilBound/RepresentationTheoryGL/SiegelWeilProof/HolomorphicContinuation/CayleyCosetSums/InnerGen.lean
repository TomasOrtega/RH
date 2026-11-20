import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.TraceTransposeMul

noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.HSt.L3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR.G

variable {m n : ℕ}

/- English proof (translation)
Take `⟨_, _, h⟩` from `hψ`. Establish `hπ : (2 * (Real.pi : ℂ)) ≠ 0`. Establish `h0 : (2 * Real.pi : ℝ) ≠ 0` using `by positivity`. Conclude with `h0` after adjusting the coercions. Establish `hβH : (((2 * (Real.pi : ℂ)))⁻¹ • Qᵀ).IsHermitian`.

Unfold `Matrix.IsHermitian`. Rewrite using `[Matrix.conjTranspose_smul, hQ.transpose.eq]`. Use `congr 1`. Simplify using `[Complex.conj_ofReal]`. Establish `hβd : (((2 * (Real.pi : ℂ)))⁻¹ • Qᵀ).det = 0`.

Rewrite using `[Matrix.det_smul, Matrix.det_transpose, hd, mul_zero]`. Establish `key` using `h _ hβH hβd`. Rewrite using `[← key]`. Use `congr 1`. Use extensionality with `s`.

Simplify using `only [eTr]`. Use `congr 2`. Rewrite using `[Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, trace_transpose_mul' (herm s) Q]`. Clear the denominators using the available nonvanishing facts.
-/
theorem inner_gen (ψ : (Fin n → Fin n → ℝ) → ℂ) (hψ : IsSingTest ψ) (Q : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q.IsHermitian) (hd : Q.det = 0) :
    ∫ s, ψ s * Complex.exp (Complex.I * ((herm s)ᵀ * Q).trace) = 0 := by
  obtain ⟨_, _, h⟩ := hψ
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 := by
    have h0 : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    exact_mod_cast h0
  have hβH : (((2 * (Real.pi : ℂ)))⁻¹ • Qᵀ).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, hQ.transpose.eq]
    congr 1
    simp [Complex.conj_ofReal]
  have hβd : (((2 * (Real.pi : ℂ)))⁻¹ • Qᵀ).det = 0 := by
    rw [Matrix.det_smul, Matrix.det_transpose, hd, mul_zero]
  have key := h _ hβH hβd
  rw [← key]
  congr 1
  ext s
  simp only [eTr]
  congr 2
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, trace_transpose_mul' (herm s) Q]
  field_simp

open PositivityTheory.Rg.Sw.WR.G.GM in
/- English proof (translation)
Establish `hψ0` using `hψ`. Take `⟨hψc, hψs, -⟩` from `hψ0`. Establish `hRR : R * R⁻¹ = 1` using `Matrix.mul_nonsing_inv R hR`. Establish `hRRh : (R⁻¹)ᴴ * Rᴴ = 1`. Rewrite using `[← Matrix.conjTranspose_mul, hRR, Matrix.conjTranspose_one]`.

Establish `hBH : ∀ s : Fin n → Fin n → ℝ, (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ).IsHermitian`. Introduce `s`. Establish `h` using `Matrix.isHermitian_conjTranspose_mul_mul (R⁻¹)ᴴ (hH.add (GM.herm_isHermitian s))`. Rewrite `h` using `[Matrix.conjTranspose_conjTranspose]`. Then use the resulting hypothesis. Establish `hD : ∀ s : Fin n → Fin n → ℝ, (1 - Complex.I • (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ)).det ≠ 0`.

Introduce `s`. Establish `h` using `GM.det_ne_zero (hBH s) 1`. Simplify using `using h`. Establish `hfac : ∀ s : Fin n → Fin n → ℝ, R * Rᴴ - Complex.I • (H0 + herm s) = R * (1 - Complex.I • (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ)) * Rᴴ`. Introduce `s`.

Establish `hM : R * (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ) * Rᴴ = H0 + herm s`. Simplify using `only [← Matrix.mul_assoc, hRR, Matrix.one_mul]`. Rewrite using `[Matrix.mul_assoc, hRRh, Matrix.mul_one]`. Rewrite using `[Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, hM]`. Establish `hbase : ∀ s : Fin n → Fin n → ℝ, secN (fun _ : Fin m => true) 1 1 1 (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ) = ((Real.pi : ℂ) ^ n / (1 - Complex.I • (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ)).det) ^ m`.

Introduce `s`. Establish `hA : ∀ a : Fin m, Amat (fun _ : Fin m => true) 1 1 (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ) a = (1 - Complex.I • (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ))ᵀ`. Introduce `a`. Simplify using `[Amat, sgn, Matrix.transpose_sub, Matrix.transpose_smul]`. Rewrite using `[base m n _ 1 1 one_pos _ (hBH s)]`.

Simplify using `only [hA, Matrix.det_transpose, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Establish `hdR : R.det ≠ 0` using `hR.ne_zero`. Establish `hdRh : Rᴴ.det ≠ 0`. Rewrite using `[Matrix.det_conjTranspose]`. Conclude with `star_ne_zero.2 hdR`.

Establish `hπ : (Real.pi : ℂ) ^ n ≠ 0` using `pow_ne_zero _ (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)`. Establish `halg : ∀ (P D A B Y : ℂ), P ≠ 0 → D ≠ 0 → A ≠ 0 → B ≠ 0 → Y * (A * D * B)⁻¹ ^ m = (A * B * P)⁻¹ ^ m * (Y * (P / D) ^ m)`. Introduce `P D A B Y hP hD' hA' hB'`. Establish `k : (A * D * B)⁻¹ = (A * B * P)⁻¹ * (P / D)`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[k, mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Establish `hpt : ∀ s : Fin n → Fin n → ℝ, ψ s * ((R * Rᴴ - Complex.I • (H0 + herm s)).det)⁻¹ ^ m = ((R.det * Rᴴ.det) * (Real.pi : ℂ) ^ n)⁻¹ ^ m * (ψ s * secN (fun _ : Fin m => true) 1 1 1 (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ))`. Introduce `s`. Rewrite using `[hfac s, Matrix.det_mul, Matrix.det_mul, hbase s]`.

Conclude with `halg _ _ _ _ _ hπ (hD s) hdR hdRh`. Establish `hgi : Integrable (fun x : Fin m → Fin n → ℂ => evX (1 : PX m n) x * gs 1 x) volume` using `integP m n 1 one_pos 1`. Establish `hψi : Integrable ψ volume` using `hψc.integrable_of_hasCompactSupport hψs`. Establish `hherm : Continuous (herm : (Fin n → Fin n → ℝ) → Matrix (Fin n) (Fin n) ℂ)`. Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations.

Simplify using `only [herm]`. Use `fun_prop`. Establish `hint : Integrable (Function.uncurry fun (s : Fin n → Fin n → ℝ) (x : Fin m → Fin n → ℂ) => ψ s * (evX (1 : PX m n) x * gs 1 x * Complex.exp (Complex.I * ((1 : ℝ) : ℂ) * (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x).trace))) (volume.prod volume)`. Use `Integrable.mono' (hψi.norm.mul_prod hgi.norm) ?_ ?_` and prove the remaining obligations. Apply `Continuous.aestronglyMeasurable` to reduce the goal to its premises.

Establish `h1 : Continuous fun p : (Fin n → Fin n → ℝ) × (Fin m → Fin n → ℂ) => R⁻¹ * (H0 + herm p.1) * (R⁻¹)ᴴ * gramX (fun _ : Fin m => true) p.2` using `((continuous_const.matrix_mul (continuous_const.add (hherm.comp continuous_fst))).matrix_mul continuous_const).matrix_mul ((continuous_gramX _).comp continuous_snd)`. Conclude with `(hψc.comp continuous_fst).mul ((((GM.continuous_evX 1).comp continuous_snd).mul ((GI.continuous_gs 1).comp continuous_snd)).mul (Complex.continuous_exp.comp (continuous_const.mul h1.matrix_trace)))`. Use `Filter.Eventually.of_forall fun p => le_of_eq ?_` and prove the remaining obligations. Take `⟨s, x⟩` from `p`. Simplify using `only [Function.uncurry_apply_pair, norm_mul]`.

Rewrite using `[GM.norm_phase (hBH s) x, mul_one]`. Establish `hin : ∀ x : Fin m → Fin n → ℂ, ∫ s, ψ s * (evX (1 : PX m n) x * gs 1 x * Complex.exp (Complex.I * ((1 : ℝ) : ℂ) * (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x).trace)) = 0`. Introduce `x`. Establish `hGH : ((R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x * R⁻¹)ᵀ.IsHermitian` using `(Matrix.isHermitian_conjTranspose_mul_mul R⁻¹ (GM.gramX_isHermitian _ x)).transpose`. Establish `hGd : ((R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x * R⁻¹)ᵀ.det = 0`.

Rewrite using `[Matrix.det_transpose, Matrix.det_mul, Matrix.det_mul, det_gram_eq_zero hmn x, mul_zero, zero_mul]`. Establish `htr : ∀ s : Fin n → Fin n → ℝ, (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x).trace = (H0 * ((R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x * R⁻¹)).trace + ((herm s)ᵀ * ((R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x * R⁻¹)ᵀ).trace`. Introduce `s`. Establish `h1 : (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x).trace = ((H0 + herm s) * ((R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x * R⁻¹)).trace`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[Matrix.trace_mul_comm R⁻¹]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[h1, Matrix.add_mul, Matrix.trace_add]`. Use `congr 1`. Rewrite using `[← Matrix.trace_transpose (herm s * _), Matrix.transpose_mul, Matrix.trace_mul_comm]`.

Establish `hrw : ∀ s : Fin n → Fin n → ℝ, ψ s * (evX (1 : PX m n) x * gs 1 x * Complex.exp (Complex.I * ((1 : ℝ) : ℂ) * (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x).trace)) = (evX (1 : PX m n) x * gs 1 x * Complex.exp (Complex.I * (H0 * ((R⁻¹)ᴴ * gramX (fun _ : Fin m => …`. Introduce `s`. Rewrite using `[htr s, Complex.ofReal_one, mul_one, mul_add, Complex.exp_add]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hrw]`.

Rewrite using `[integral_const_mul, inner_gen ψ hψ _ hGH hGd, mul_zero]`. Establish `hmain : ∫ s, ψ s * secN (fun _ : Fin m => true) 1 1 1 (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ) = 0`. Simplify using `only [secN]`. Simplify using `only [← integral_const_mul]`. Rewrite using `[integral_integral_swap hint]`.

Simplify using `only [hin, integral_zero]`. Simplify using `only [hpt]`. Rewrite using `[integral_const_mul, hmain, mul_zero]`.
-/
theorem core2 (hmn : m < n) (R : Matrix (Fin n) (Fin n) ℂ) (hR : IsUnit R.det) (H0 : Matrix (Fin n) (Fin n) ℂ)
    (hH : H0.IsHermitian) (ψ : (Fin n → Fin n → ℝ) → ℂ) (hψ : IsSingTest ψ) :
    ∫ s, ψ s * ((R * Rᴴ - Complex.I • (H0 + herm s)).det)⁻¹ ^ m = 0 := by
  have hψ0 := hψ
  obtain ⟨hψc, hψs, -⟩ := hψ0
  have hRR : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hR
  have hRRh : (R⁻¹)ᴴ * Rᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hRR, Matrix.conjTranspose_one]
  have hBH : ∀ s : Fin n → Fin n → ℝ, (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ).IsHermitian := by
    intro s
    have h := Matrix.isHermitian_conjTranspose_mul_mul (R⁻¹)ᴴ (hH.add (GM.herm_isHermitian s))
    rwa [Matrix.conjTranspose_conjTranspose] at h
  have hD : ∀ s : Fin n → Fin n → ℝ, (1 - Complex.I • (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ)).det ≠ 0 := by
    intro s
    have h := GM.det_ne_zero (hBH s) 1
    simpa using h
  have hfac : ∀ s : Fin n → Fin n → ℝ, R * Rᴴ - Complex.I • (H0 + herm s) =
      R * (1 - Complex.I • (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ)) * Rᴴ := by
    intro s
    have hM : R * (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ) * Rᴴ = H0 + herm s := by
      simp only [← Matrix.mul_assoc, hRR, Matrix.one_mul]
      rw [Matrix.mul_assoc, hRRh, Matrix.mul_one]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, hM]
  have hbase : ∀ s : Fin n → Fin n → ℝ, secN (fun _ : Fin m => true) 1 1 1 (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ) =
      ((Real.pi : ℂ) ^ n / (1 - Complex.I • (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ)).det) ^ m := by
    intro s
    have hA : ∀ a : Fin m, Amat (fun _ : Fin m => true) 1 1 (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ) a =
        (1 - Complex.I • (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ))ᵀ := by
      intro a
      simp [Amat, sgn, Matrix.transpose_sub, Matrix.transpose_smul]
    rw [base m n _ 1 1 one_pos _ (hBH s)]
    simp only [hA, Matrix.det_transpose, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hdR : R.det ≠ 0 := hR.ne_zero
  have hdRh : Rᴴ.det ≠ 0 := by
    rw [Matrix.det_conjTranspose]
    exact star_ne_zero.2 hdR
  have hπ : (Real.pi : ℂ) ^ n ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)
  have halg : ∀ (P D A B Y : ℂ), P ≠ 0 → D ≠ 0 → A ≠ 0 → B ≠ 0 →
      Y * (A * D * B)⁻¹ ^ m = (A * B * P)⁻¹ ^ m * (Y * (P / D) ^ m) := by
    intro P D A B Y hP hD' hA' hB'
    have k : (A * D * B)⁻¹ = (A * B * P)⁻¹ * (P / D) := by
      field_simp
    rw [k, mul_pow]
    ring
  have hpt : ∀ s : Fin n → Fin n → ℝ, ψ s * ((R * Rᴴ - Complex.I • (H0 + herm s)).det)⁻¹ ^ m =
      ((R.det * Rᴴ.det) * (Real.pi : ℂ) ^ n)⁻¹ ^ m *
        (ψ s * secN (fun _ : Fin m => true) 1 1 1 (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ)) := by
    intro s
    rw [hfac s, Matrix.det_mul, Matrix.det_mul, hbase s]
    exact halg _ _ _ _ _ hπ (hD s) hdR hdRh
  have hgi : Integrable (fun x : Fin m → Fin n → ℂ => evX (1 : PX m n) x * gs 1 x) volume :=
    integP m n 1 one_pos 1
  have hψi : Integrable ψ volume := hψc.integrable_of_hasCompactSupport hψs
  have hherm : Continuous (herm : (Fin n → Fin n → ℝ) → Matrix (Fin n) (Fin n) ℂ) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [herm]
    fun_prop
  have hint : Integrable (Function.uncurry fun (s : Fin n → Fin n → ℝ) (x : Fin m → Fin n → ℂ) =>
      ψ s * (evX (1 : PX m n) x * gs 1 x *
        Complex.exp (Complex.I * ((1 : ℝ) : ℂ) *
          (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x).trace)))
      (volume.prod volume) := by
    refine Integrable.mono' (hψi.norm.mul_prod hgi.norm) ?_ ?_
    · apply Continuous.aestronglyMeasurable
      have h1 : Continuous fun p : (Fin n → Fin n → ℝ) × (Fin m → Fin n → ℂ) =>
          R⁻¹ * (H0 + herm p.1) * (R⁻¹)ᴴ * gramX (fun _ : Fin m => true) p.2 :=
        ((continuous_const.matrix_mul (continuous_const.add (hherm.comp continuous_fst))).matrix_mul
          continuous_const).matrix_mul ((continuous_gramX _).comp continuous_snd)
      exact (hψc.comp continuous_fst).mul ((((GM.continuous_evX 1).comp continuous_snd).mul
        ((GI.continuous_gs 1).comp continuous_snd)).mul
        (Complex.continuous_exp.comp (continuous_const.mul h1.matrix_trace)))
    · refine Filter.Eventually.of_forall fun p => le_of_eq ?_
      obtain ⟨s, x⟩ := p
      simp only [Function.uncurry_apply_pair, norm_mul]
      rw [GM.norm_phase (hBH s) x, mul_one]
  have hin : ∀ x : Fin m → Fin n → ℂ, ∫ s, ψ s * (evX (1 : PX m n) x * gs 1 x *
        Complex.exp (Complex.I * ((1 : ℝ) : ℂ) *
          (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x).trace)) = 0 := by
    intro x
    have hGH : ((R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x * R⁻¹)ᵀ.IsHermitian :=
      (Matrix.isHermitian_conjTranspose_mul_mul R⁻¹ (GM.gramX_isHermitian _ x)).transpose
    have hGd : ((R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x * R⁻¹)ᵀ.det = 0 := by
      rw [Matrix.det_transpose, Matrix.det_mul, Matrix.det_mul, det_gram_eq_zero hmn x, mul_zero, zero_mul]
    have htr : ∀ s : Fin n → Fin n → ℝ,
        (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x).trace =
          (H0 * ((R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x * R⁻¹)).trace +
          ((herm s)ᵀ * ((R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x * R⁻¹)ᵀ).trace := by
      intro s
      have h1 : (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x).trace =
          ((H0 + herm s) * ((R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x * R⁻¹)).trace := by
        simp only [Matrix.mul_assoc]
        rw [Matrix.trace_mul_comm R⁻¹]
        simp only [Matrix.mul_assoc]
      rw [h1, Matrix.add_mul, Matrix.trace_add]
      congr 1
      rw [← Matrix.trace_transpose (herm s * _), Matrix.transpose_mul, Matrix.trace_mul_comm]
    have hrw : ∀ s : Fin n → Fin n → ℝ, ψ s * (evX (1 : PX m n) x * gs 1 x *
        Complex.exp (Complex.I * ((1 : ℝ) : ℂ) *
          (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x).trace)) =
        (evX (1 : PX m n) x * gs 1 x *
          Complex.exp (Complex.I * (H0 * ((R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x * R⁻¹)).trace)) *
        (ψ s * Complex.exp (Complex.I *
          ((herm s)ᵀ * ((R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x * R⁻¹)ᵀ).trace)) := by
      intro s
      rw [htr s, Complex.ofReal_one, mul_one, mul_add, Complex.exp_add]
      ring
    simp only [hrw]
    rw [integral_const_mul, inner_gen ψ hψ _ hGH hGd, mul_zero]
  have hmain : ∫ s, ψ s * secN (fun _ : Fin m => true) 1 1 1 (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ) = 0 := by
    simp only [secN]
    simp only [← integral_const_mul]
    rw [integral_integral_swap hint]
    simp only [hin, integral_zero]
  simp only [hpt]
  rw [integral_const_mul, hmain, mul_zero]

end PositivityTheory.Rg.Sw.HSt.L3
