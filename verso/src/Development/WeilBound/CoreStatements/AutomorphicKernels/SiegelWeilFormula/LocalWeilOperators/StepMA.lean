import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.StepNC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzLinearChangeStatement

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Simplify using `[dZ, Matrix.fromBlocks_multiply, smul_smul, inv_mul_cancel₀ h, mul_inv_cancel₀ h]`.
-/
theorem dZ_conj_diag {n : ℕ} {ζ : ℂ} (h : ζ ≠ 0) (A D : Matrix (Fin n) (Fin n) ℂ) :
    dZ n ζ⁻¹ * Matrix.fromBlocks A 0 0 D * dZ n ζ = Matrix.fromBlocks A 0 0 D := by
  simp [dZ, Matrix.fromBlocks_multiply, smul_smul, inv_mul_cancel₀ h, mul_inv_cancel₀ h]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, Matrix.map_apply]`.
-/
theorem mapStar_mulR {p q r : Type} [Fintype q] (A : Matrix p q ℂ) (B : Matrix q r ℂ) :
    (A * B).map star = A.map star * B.map star := by
  ext i j
  simp [Matrix.mul_apply, Matrix.map_apply]

namespace RD

variable {d : SD σ} (R : RD d) (w : InfinitePlace F)

/- English proof (translation)
Establish `hζ0 : R.ζ ≠ 0` using `Krd.zeta_ne R.hζ`. Use `set M := inFrame d.b (R.ι w y) with hM`. Establish `hw : d.cw w M = Matrix.fromBlocks A 0 0 D` using `by rw [hM, R.cw_iota_pf w y, hy, dZ_conj_diag hζ0]`. Establish `ho : ∀ w', w' ≠ w → d.cw w' M = 1` using `fun w' h => R.off_w w w' y h`. Establish `hf : finOne F • M = finOne F • 1` using `R.off_f w y`.

Establish `o1` using `one_blocks (n := d.n) (1 : ℂ)`. Establish `of` using `one_blocks (n := d.n) (finOne F • (1 : AE F E))`. Simplify using `only [one_smul] at o1`. Establish `hf' : finOne F • M = (finOne F • (1 : AE F E)) • (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))`. Rewrite using `[hf, smul_one_smul]`.

Establish `z0 : ∀ w', d.cw w' (0 : Matrix (Fin d.n) (Fin d.n) (AE F E)) = 0` using `fun w' => Matrix.map_zero _ (map_zero _)`. Establish `e12 : M.toBlocks₁₂ = 0`. Apply `Place.cw_ext d` to reduce the goal to its premises. Introduce `w'`. Rewrite using `[z0]`.

Use `show (d.cw w' M).toBlocks₁₂ = 0`. Distinguish the cases in `h : w' = w`. Rewrite using `[h, hw]`. Simplify using the standard rewrite rules. Rewrite using `[ho w' h]`.

Conclude with `o1.2.1`. Use `show (finOne F • M).toBlocks₁₂ = _`. Rewrite using `[hf', of.2.1, smul_zero]`. Establish `e21 : M.toBlocks₂₁ = 0`. Apply `Place.cw_ext d` to reduce the goal to its premises.

Introduce `w'`. Rewrite using `[z0]`. Use `show (d.cw w' M).toBlocks₂₁ = 0`. Distinguish the cases in `h : w' = w`. Rewrite using `[h, hw]`.

Simplify using the standard rewrite rules. Rewrite using `[ho w' h]`. Conclude with `o1.2.2.1`. Use `show (finOne F • M).toBlocks₂₁ = _`. Rewrite using `[hf', of.2.2.1, smul_zero]`.

Use `⟨?_, ?_, ?_, fun w' h => ⟨?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]`. Rewrite using `[e12, e21]`. Use `show (d.cw w M).toBlocks₁₁ = _`. Rewrite using `[hw]`.

Simplify using the standard rewrite rules. Use `show (d.cw w M).toBlocks₂₂ = _`. Rewrite using `[hw]`. Simplify using the standard rewrite rules. Use `show (d.cw w' M).toBlocks₁₁ = _`.

Rewrite using `[ho w' h]`. Conclude with `o1.1`. Use `show (d.cw w' M).toBlocks₂₂ = _`. Rewrite using `[ho w' h]`. Conclude with `o1.2.2.2`.

Use `show (finOne F • M).toBlocks₁₁ = _`. Rewrite using `[hf', of.1, smul_one_smul]`. Use `show (finOne F • M).toBlocks₂₂ = _`. Rewrite using `[hf', of.2.2.2, smul_one_smul]`.
-/
theorem frame_diag (y : GR d.n) (A D : Matrix (Fin d.n) (Fin d.n) ℂ) (hy : mR y = Matrix.fromBlocks A 0 0 D) :
    inFrame d.b (R.ι w y) = Matrix.fromBlocks (inFrame d.b (R.ι w y)).toBlocks₁₁ 0 0 (inFrame d.b (R.ι w y)).toBlocks₂₂ ∧
    d.cw w (inFrame d.b (R.ι w y)).toBlocks₁₁ = A ∧ d.cw w (inFrame d.b (R.ι w y)).toBlocks₂₂ = D ∧
    (∀ w', w' ≠ w → d.cw w' (inFrame d.b (R.ι w y)).toBlocks₁₁ = 1 ∧ d.cw w' (inFrame d.b (R.ι w y)).toBlocks₂₂ = 1) ∧
    finOne F • (inFrame d.b (R.ι w y)).toBlocks₁₁ = finOne F • 1 ∧
    finOne F • (inFrame d.b (R.ι w y)).toBlocks₂₂ = finOne F • 1 := by
  have hζ0 : R.ζ ≠ 0 := Krd.zeta_ne R.hζ
  set M := inFrame d.b (R.ι w y) with hM
  have hw : d.cw w M = Matrix.fromBlocks A 0 0 D := by rw [hM, R.cw_iota_pf w y, hy, dZ_conj_diag hζ0]
  have ho : ∀ w', w' ≠ w → d.cw w' M = 1 := fun w' h => R.off_w w w' y h
  have hf : finOne F • M = finOne F • 1 := R.off_f w y
  have o1 := one_blocks (n := d.n) (1 : ℂ)
  have of := one_blocks (n := d.n) (finOne F • (1 : AE F E))
  simp only [one_smul] at o1
  have hf' : finOne F • M = (finOne F • (1 : AE F E)) • (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) := by
    rw [hf, smul_one_smul]
  have z0 : ∀ w', d.cw w' (0 : Matrix (Fin d.n) (Fin d.n) (AE F E)) = 0 := fun w' => Matrix.map_zero _ (map_zero _)
  have e12 : M.toBlocks₁₂ = 0 := by
    apply Place.cw_ext d
    · intro w'
      rw [z0]
      show (d.cw w' M).toBlocks₁₂ = 0
      by_cases h : w' = w
      · rw [h, hw]; simp
      · rw [ho w' h]; exact o1.2.1
    · show (finOne F • M).toBlocks₁₂ = _
      rw [hf', of.2.1, smul_zero]
  have e21 : M.toBlocks₂₁ = 0 := by
    apply Place.cw_ext d
    · intro w'
      rw [z0]
      show (d.cw w' M).toBlocks₂₁ = 0
      by_cases h : w' = w
      · rw [h, hw]; simp
      · rw [ho w' h]; exact o1.2.2.1
    · show (finOne F • M).toBlocks₂₁ = _
      rw [hf', of.2.2.1, smul_zero]
  refine ⟨?_, ?_, ?_, fun w' h => ⟨?_, ?_⟩, ?_, ?_⟩
  · conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
    rw [e12, e21]
  · show (d.cw w M).toBlocks₁₁ = _
    rw [hw]; simp
  · show (d.cw w M).toBlocks₂₂ = _
    rw [hw]; simp
  · show (d.cw w' M).toBlocks₁₁ = _
    rw [ho w' h]; exact o1.1
  · show (d.cw w' M).toBlocks₂₂ = _
    rw [ho w' h]; exact o1.2.2.2
  · show (finOne F • M).toBlocks₁₁ = _
    rw [hf', of.1, smul_one_smul]
  · show (finOne F • M).toBlocks₂₂ = _
    rw [hf', of.2.2.2, smul_one_smul]

/- English proof (translation)
Introduce `h`. Establish `h1 : absE F E x * absE F E x⁻¹ = 1` using `by rw [← map_mul, mul_inv_cancel, map_one]`. Establish `h0 : absE F E x = 0` using `by exact_mod_cast h`. Rewrite `h1` using `[h0, zero_mul]`. Conclude with `zero_ne_one h1`.
-/
theorem absE_ne (x : (AE F E)ˣ) : (absE F E x : ℝ) ≠ 0 := by
  intro h
  have h1 : absE F E x * absE F E x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have h0 : absE F E x = 0 := by exact_mod_cast h
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1

/- English proof (translation)
Introduce `y a ha hy`. Establish `haH : IsUnit aᴴ.det` using `by rw [Matrix.det_conjTranspose]; exact ha.star`. Establish `hyi : mR y⁻¹ = Matrix.fromBlocks a⁻¹ 0 0 aᴴ`. Establish `h1 : mR y * mR y⁻¹ = 1` using `by show ((y * y⁻¹ : GR d.n) : GL (Fin d.n ⊕ Fin d.n) ℂ).1 = 1`. Rewrite using `[mul_inv_cancel]`.

Both sides reduce to the same expression. Establish `h2 : Matrix.fromBlocks a⁻¹ 0 0 aᴴ * mR y = 1`. Rewrite using `[hy, mLoc, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]`. Simplify using `[Matrix.nonsing_inv_mul _ ha, Matrix.mul_nonsing_inv _ haH]`. Combine the equalities or inequalities in the displayed calculation.

Take `⟨hM, -, -, -, -, -⟩` from `R.frame_diag w y a (aᴴ)⁻¹ hy`. Take `⟨hM', -, hD', hO', -, hF'⟩` from `R.frame_diag w y⁻¹ a⁻¹ aᴴ hyi`. Use `set M := inFrame d.b (R.ι w y) with hMdef`. Use `set M' := inFrame d.b (R.ι w y⁻¹) with hM'def`. Establish `hMM : M * M' = 1`.

Rewrite using `[hMdef, hM'def, ← d.inFrame_mul, ← map_mul, mul_inv_cancel, map_one, d.inFrame_one]`. Establish `hMM' : M' * M = 1`. Rewrite using `[hMdef, hM'def, ← d.inFrame_mul, ← map_mul, inv_mul_cancel, map_one, d.inFrame_one]`. Establish `bl : ∀ {P Q : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)}, P = Matrix.fromBlocks P.toBlocks₁₁ 0 0 P.toBlocks₂₂ → Q = Matrix.fromBlocks Q.toBlocks₁₁ 0 0 Q.toBlocks₂₂ → P * Q = 1 → P.toBlocks₁₁ * Q.toBlocks₁₁ = 1 ∧ P.toBlocks₂₂ * Q.toBlocks₂₂ = 1`. Introduce `P Q hP hQ hPQ`.

Rewrite `hPQ` using `[hP, hQ, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]`. Simplify using `only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at hPQ`. Take `⟨h1, -, -, h4⟩` from `Matrix.fromBlocks_inj.mp hPQ`. Conclude with `⟨h1, h4⟩`. Take `⟨t1, u1⟩` from `bl hM hM' hMM`.

Take `⟨t2, u2⟩` from `bl hM' hM hMM'`. Set `t : GL (Fin d.n) (AE F E)` to `⟨M.toBlocks₁₁, M'.toBlocks₁₁, t1, t2⟩`. Set `u : GL (Fin d.n) (AE F E)` to `⟨M.toBlocks₂₂, M'.toBlocks₂₂, u1, u2⟩`. Establish `hMtu : inFrame d.b (R.ι w y) = Matrix.fromBlocks t.1 0 0 u.1` using `hM`. Use `set c : ℂ := (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) * (((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ) with hc`.

Use `⟨c, ?_, fun f hf => ?_, fun Ψ hΨ => ⟨hΨ, fun f hf Φ hΦ hTΦ => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hc]`. Use `mul_ne_zero (Circle.coe_ne_zero _) ?_` and prove the remaining obligations. Rewrite using `[Complex.ofReal_ne_zero]`. Conclude with `(Real.rpow_pos_of_pos (lt_of_le_of_ne (NNReal.coe_nonneg _) (absE_ne _).symm) _).ne'`.

Take `⟨φ, rfl⟩` from `hf`. Take `⟨ψ, hψ⟩` from `GlobalTheory.T.schwartz_linear_change d.m d.n c a ha φ`. Conclude with `⟨ψ, hψ⟩`. Use function extensionality and compare the values at `X`. Rewrite using `[(hT.2.1 F E σ d Φ hΦ).2.1 (R.ι w y) t u hMtu X, hTΦ]`.

Establish `hui : (u⁻¹).1 = M'.toBlocks₂₂` using `rfl`. Rewrite using `[hui]`. Use `set Z := X * (M'.toBlocks₂₂)ᵀ - X with hZ`. Establish `hZo : ∀ w', w' ≠ w → d.cw w' Z = 0`. Introduce `w' h`.

Rewrite using `[hZ, show d.cw w' (X * (M'.toBlocks₂₂)ᵀ - X) = d.cw w' X * (d.cw w' M'.toBlocks₂₂)ᵀ - d.cw w' X from by`. Rewrite using `[← Krd.cw_transpose d, ← cw_mulR]`. Conclude with `Matrix.map_sub _ (map_sub _) _ _, (hO' w' h).2, Matrix.transpose_one,`. Use the proof step `Matrix.mul_one, sub_self]`. Establish `hZf : finOne F • Z = 0`.

Rewrite using `[hZ, smul_sub, ← Matrix.mul_smul, ← Matrix.transpose_smul, hF', Matrix.transpose_smul, Matrix.transpose_one, Matrix.mul_smul, Matrix.mul_one, sub_self]`. Establish `hX : X * (M'.toBlocks₂₂)ᵀ = X + Z` using `by rw [hZ]; abel`. Establish `hloc : R.loc w (X * (M'.toBlocks₂₂)ᵀ) = Matrix.of (R.loc w X) * a`. Simplify using `only [RD.loc]`. Rewrite using `[cw_mulR, Krd.cw_transpose d, hD', ← Matrix.mul_assoc, mapStar_mulR]`.

Use `congr 1`. Use extensionality with `i j`. Simplify using `[Matrix.conjTranspose_apply]`. Simplify using `only [RD.tens, id]`. Rewrite using `[hloc, hX, hΨ X Z hZo hZf, hc]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem stepM_pf (hT : TAll) : ∀ (y : GR d.n) (a : Matrix (Fin d.n) (Fin d.n) ℂ), IsUnit a.det → mR y = mLoc a →
    ∃ c : ℂ, c ≠ 0 ∧ R.StepOK w (R.ι w y) (fun f u => c * f (Matrix.of u * a)) id := by
  intro y a ha hy
  have haH : IsUnit aᴴ.det := by rw [Matrix.det_conjTranspose]; exact ha.star

  have hyi : mR y⁻¹ = Matrix.fromBlocks a⁻¹ 0 0 aᴴ := by
    have h1 : mR y * mR y⁻¹ = 1 := by
      show ((y * y⁻¹ : GR d.n) : GL (Fin d.n ⊕ Fin d.n) ℂ).1 = 1
      rw [mul_inv_cancel]; rfl
    have h2 : Matrix.fromBlocks a⁻¹ 0 0 aᴴ * mR y = 1 := by
      rw [hy, mLoc, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
      simp [Matrix.nonsing_inv_mul _ ha, Matrix.mul_nonsing_inv _ haH]
    calc mR y⁻¹ = (Matrix.fromBlocks a⁻¹ 0 0 aᴴ * mR y) * mR y⁻¹ := by rw [h2, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  obtain ⟨hM, -, -, -, -, -⟩ := R.frame_diag w y a (aᴴ)⁻¹ hy
  obtain ⟨hM', -, hD', hO', -, hF'⟩ := R.frame_diag w y⁻¹ a⁻¹ aᴴ hyi
  set M := inFrame d.b (R.ι w y) with hMdef
  set M' := inFrame d.b (R.ι w y⁻¹) with hM'def
  have hMM : M * M' = 1 := by
    rw [hMdef, hM'def, ← d.inFrame_mul, ← map_mul, mul_inv_cancel, map_one, d.inFrame_one]
  have hMM' : M' * M = 1 := by
    rw [hMdef, hM'def, ← d.inFrame_mul, ← map_mul, inv_mul_cancel, map_one, d.inFrame_one]
  have bl : ∀ {P Q : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)},
      P = Matrix.fromBlocks P.toBlocks₁₁ 0 0 P.toBlocks₂₂ → Q = Matrix.fromBlocks Q.toBlocks₁₁ 0 0 Q.toBlocks₂₂ →
      P * Q = 1 → P.toBlocks₁₁ * Q.toBlocks₁₁ = 1 ∧ P.toBlocks₂₂ * Q.toBlocks₂₂ = 1 := by
    intro P Q hP hQ hPQ
    rw [hP, hQ, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one] at hPQ
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at hPQ
    obtain ⟨h1, -, -, h4⟩ := Matrix.fromBlocks_inj.mp hPQ
    exact ⟨h1, h4⟩
  obtain ⟨t1, u1⟩ := bl hM hM' hMM
  obtain ⟨t2, u2⟩ := bl hM' hM hMM'
  let t : GL (Fin d.n) (AE F E) := ⟨M.toBlocks₁₁, M'.toBlocks₁₁, t1, t2⟩
  let u : GL (Fin d.n) (AE F E) := ⟨M.toBlocks₂₂, M'.toBlocks₂₂, u1, u2⟩
  have hMtu : inFrame d.b (R.ι w y) = Matrix.fromBlocks t.1 0 0 u.1 := hM
  set c : ℂ := (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
    (((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ) with hc
  refine ⟨c, ?_, fun f hf => ?_, fun Ψ hΨ => ⟨hΨ, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · rw [hc]
    refine mul_ne_zero (Circle.coe_ne_zero _) ?_
    rw [Complex.ofReal_ne_zero]
    exact (Real.rpow_pos_of_pos (lt_of_le_of_ne (NNReal.coe_nonneg _) (absE_ne _).symm) _).ne'
  · obtain ⟨φ, rfl⟩ := hf
    obtain ⟨ψ, hψ⟩ := GlobalTheory.T.schwartz_linear_change d.m d.n c a ha φ
    exact ⟨ψ, hψ⟩
  · funext X
    rw [(hT.2.1 F E σ d Φ hΦ).2.1 (R.ι w y) t u hMtu X, hTΦ]
    have hui : (u⁻¹).1 = M'.toBlocks₂₂ := rfl
    rw [hui]
    set Z := X * (M'.toBlocks₂₂)ᵀ - X with hZ
    have hZo : ∀ w', w' ≠ w → d.cw w' Z = 0 := by
      intro w' h
      rw [hZ, show d.cw w' (X * (M'.toBlocks₂₂)ᵀ - X) = d.cw w' X * (d.cw w' M'.toBlocks₂₂)ᵀ - d.cw w' X from by
        rw [← Krd.cw_transpose d, ← cw_mulR]; exact Matrix.map_sub _ (map_sub _) _ _, (hO' w' h).2, Matrix.transpose_one,
        Matrix.mul_one, sub_self]
    have hZf : finOne F • Z = 0 := by
      rw [hZ, smul_sub, ← Matrix.mul_smul, ← Matrix.transpose_smul, hF', Matrix.transpose_smul, Matrix.transpose_one,
        Matrix.mul_smul, Matrix.mul_one, sub_self]
    have hX : X * (M'.toBlocks₂₂)ᵀ = X + Z := by rw [hZ]; abel
    have hloc : R.loc w (X * (M'.toBlocks₂₂)ᵀ) = Matrix.of (R.loc w X) * a := by
      simp only [RD.loc]
      rw [cw_mulR, Krd.cw_transpose d, hD', ← Matrix.mul_assoc, mapStar_mulR]
      congr 1
      ext i j
      simp [Matrix.conjTranspose_apply]
    simp only [RD.tens, id]
    rw [hloc, hX, hΨ X Z hZo hZf, hc]
    ring

end RD

end PositivityTheory.SiegelWeilFormula

end
