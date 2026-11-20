import Development.WeilBound.ThetaLifts.Reductions.MetaplecticDerivatives.ContinuousPair

noncomputable section

open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL
open scoped Real

namespace PositivityTheory.ThKR.Mp

variable {l : Type} [Fintype l] [DecidableEq l]

namespace C

/- English proof (translation)
Use extensionality with `a b`. Establish `e : ∀ x y : ℂ, x * (I * y) = I * (x * y)` using `fun x y => mul_left_comm x I y`. Simplify using `only [upperParabolic, loQ, Matrix.mul_apply, Matrix.add_apply, Matrix.map_apply, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.of_apply, Fintype.sum_sum_type, Complex.ofReal_add, Complex.ofReal_sum, Complex.ofReal_mul, mul_sub, Finset.sum_sub_distrib, mul_add, Finset.mul_sum, e]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem upperPart_mul (s s' : Mat l) :
    upperParabolic (s * s') = s.toBlocks₁₁.map Complex.ofReal * upperParabolic s' + s.toBlocks₁₂.map Complex.ofReal * loQ s' := by
  ext a b
  have e : ∀ x y : ℂ, x * (I * y) = I * (x * y) := fun x y => mul_left_comm x I y
  simp only [upperParabolic, loQ, Matrix.mul_apply, Matrix.add_apply, Matrix.map_apply, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
    Matrix.of_apply, Fintype.sum_sum_type, Complex.ofReal_add, Complex.ofReal_sum, Complex.ofReal_mul, mul_sub,
    Finset.sum_sub_distrib, mul_add, Finset.mul_sum, e]
  ring

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.mul_apply]`.
-/
theorem map_ofReal_mul (M N : Matrix l l ℝ) :
    (M * N).map Complex.ofReal = M.map Complex.ofReal * N.map Complex.ofReal := by
  ext i j
  simp [Matrix.mul_apply]

/- English proof (translation)
The claim follows from `(RingHom.map_det Complex.ofRealHom M).symm`.
-/
theorem det_map_ofReal (M : Matrix l l ℝ) : (M.map Complex.ofReal).det = (M.det : ℂ) :=
  (RingHom.map_det Complex.ofRealHom M).symm

/- English proof (translation)
Establish `hu : IsUnit s.toBlocks₁₁.det` using `isUnit_iff_ne_zero.2 hd`. Establish `hAS : s.toBlocks₁₁ * (s.toBlocks₁₁⁻¹ * s.toBlocks₁₂) = s.toBlocks₁₂`. Rewrite using `[← Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.one_mul]`. Establish `hB : s.toBlocks₁₂.map Complex.ofReal = s.toBlocks₁₁.map Complex.ofReal * (s.toBlocks₁₁⁻¹ * s.toBlocks₁₂).map Complex.ofReal`. Rewrite using `[← map_ofReal_mul, hAS]`.

Rewrite using `[dd, upperPart_mul, hB, Matrix.mul_assoc, ← Matrix.mul_add, det_mul, det_map_ofReal]`.
-/
theorem dd_mul_eq (s s' : Mat l) (hd : s.toBlocks₁₁.det ≠ 0) :
    dd (s * s') = (s.toBlocks₁₁.det : ℂ) *
      (upperParabolic s' + (s.toBlocks₁₁⁻¹ * s.toBlocks₁₂).map Complex.ofReal * loQ s').det := by
  have hu : IsUnit s.toBlocks₁₁.det := isUnit_iff_ne_zero.2 hd
  have hAS : s.toBlocks₁₁ * (s.toBlocks₁₁⁻¹ * s.toBlocks₁₂) = s.toBlocks₁₂ := by
    rw [← Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.one_mul]
  have hB : s.toBlocks₁₂.map Complex.ofReal =
      s.toBlocks₁₁.map Complex.ofReal * (s.toBlocks₁₁⁻¹ * s.toBlocks₁₂).map Complex.ofReal := by
    rw [← map_ofReal_mul, hAS]
  rw [dd, upperPart_mul, hB, Matrix.mul_assoc, ← Matrix.mul_add, det_mul, det_map_ofReal]

/- English proof (translation)
Establish `h1` using `congrArg Matrix.toBlocks₁₁ h`. Simplify using `only [Matrix.J, fromBlocks_transpose, fromBlocks_multiply, toBlocks_fromBlocks₁₁] at h1`. Simplify using `only [Matrix.mul_zero, Matrix.mul_one, zero_add, add_zero, Matrix.mul_neg, Matrix.neg_mul] at h1`. Conclude with `add_neg_eq_zero.1 h1`.
-/
theorem blocks_symm {A B C D : Matrix l l ℝ} (h : fromBlocks A B C D * Matrix.J l ℝ * (fromBlocks A B C D)ᵀ = Matrix.J l ℝ) :
    B * Aᵀ = A * Bᵀ := by
  have h1 := congrArg Matrix.toBlocks₁₁ h
  simp only [Matrix.J, fromBlocks_transpose, fromBlocks_multiply, toBlocks_fromBlocks₁₁] at h1
  simp only [Matrix.mul_zero, Matrix.mul_one, zero_add, add_zero, Matrix.mul_neg, Matrix.neg_mul] at h1
  exact add_neg_eq_zero.1 h1

/- English proof (translation)
Establish `hAB : s.1.toBlocks₁₂ * s.1.toBlocks₁₁ᵀ = s.1.toBlocks₁₁ * s.1.toBlocks₁₂ᵀ`. Establish `h` using `SymplecticGroup.mem_iff.1 s.2`. Rewrite `h` using `[← fromBlocks_toBlocks s.1]`. Conclude with `blocks_symm h`. Establish `hu : IsUnit s.1.toBlocks₁₁.det` using `isUnit_iff_ne_zero.2 hd`.

Establish `hut : IsUnit s.1.toBlocks₁₁ᵀ.det` using `by rw [det_transpose]; exact hu`. Use `show (s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂)ᵀ = s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂`. Rewrite using `[transpose_mul, transpose_nonsing_inv]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]`.

Use `_ = s.1.toBlocks₁₁⁻¹ * (s.1.toBlocks₁₂ * s.1.toBlocks₁₁ᵀ) * (s.1.toBlocks₁₁ᵀ)⁻¹ := by rw [hAB]`. Use `_ = s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂ := by`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hut, Matrix.mul_one]`.
-/
theorem isSymm_inv_mul (s : Sp l) (hd : s.1.toBlocks₁₁.det ≠ 0) :
    (s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂).IsSymm := by
  have hAB : s.1.toBlocks₁₂ * s.1.toBlocks₁₁ᵀ = s.1.toBlocks₁₁ * s.1.toBlocks₁₂ᵀ := by
    have h := SymplecticGroup.mem_iff.1 s.2
    rw [← fromBlocks_toBlocks s.1] at h
    exact blocks_symm h
  have hu : IsUnit s.1.toBlocks₁₁.det := isUnit_iff_ne_zero.2 hd
  have hut : IsUnit s.1.toBlocks₁₁ᵀ.det := by rw [det_transpose]; exact hu
  show (s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂)ᵀ = s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂
  rw [transpose_mul, transpose_nonsing_inv]
  calc s.1.toBlocks₁₂ᵀ * (s.1.toBlocks₁₁ᵀ)⁻¹
      = s.1.toBlocks₁₁⁻¹ * (s.1.toBlocks₁₁ * s.1.toBlocks₁₂ᵀ) * (s.1.toBlocks₁₁ᵀ)⁻¹ := by
        rw [← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]
    _ = s.1.toBlocks₁₁⁻¹ * (s.1.toBlocks₁₂ * s.1.toBlocks₁₁ᵀ) * (s.1.toBlocks₁₁ᵀ)⁻¹ := by rw [hAB]
    _ = s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hut, Matrix.mul_one]

/- English proof (translation)
Establish `h2 : s.1ᵀ * (Matrix.J l ℝ * s.1) = Matrix.J l ℝ`. Use `SymplecticGroup.mem_iff.1 (SymplecticGroup.transpose_mem s.2)` as an intermediate fact. Rewrite `this` using `[transpose_transpose, Matrix.mul_assoc]`. Then use the resulting hypothesis. Rewrite using `[sympl_eq, sympl_eq, mulVec_mulVec, ← Matrix.vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, h2]`.
-/
theorem sympl_sp (s : Sp l) (w w' : l ⊕ l → ℝ) : sympl (s.1 *ᵥ w) (s.1 *ᵥ w') = sympl w w' := by
  have h2 : s.1ᵀ * (Matrix.J l ℝ * s.1) = Matrix.J l ℝ := by
    have := SymplecticGroup.mem_iff.1 (SymplecticGroup.transpose_mem s.2)
    rwa [transpose_transpose, Matrix.mul_assoc] at this
  rw [sympl_eq, sympl_eq, mulVec_mulVec, ← Matrix.vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, h2]

/- English proof (translation)
Simplify using `only [sec, big, ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, SchwartzMap.smul_apply, ph_apply, dil_apply hA.ringInverse, map_zero, inner_zero_left, mul_zero, ofReal_zero, zero_mul, Complex.exp_zero, one_mul, smul_eq_mul]`.
-/
theorem sec_apply_zero (s : Mat l) (hA : IsUnit (bl Sum.inl Sum.inl s)) (f : Sch l) :
    sec s f 0 = (((√|s.toBlocks₁₁.det|)⁻¹ : ℝ) : ℂ) *
      fou l (ph (-(Ring.inverse (bl Sum.inl Sum.inl s) * bl Sum.inl Sum.inr s)) (fouInv l f)) 0 := by
  simp only [sec, big, ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, SchwartzMap.smul_apply, ph_apply,
    dil_apply hA.ringInverse, map_zero, inner_zero_left, mul_zero, ofReal_zero, zero_mul, Complex.exp_zero, one_mul,
    smul_eq_mul]

end C

open C

/- English proof (translation)
Introduce `s hd`. Establish `hu : IsUnit s.1.toBlocks₁₁.det` using `isUnit_iff_ne_zero.2 hd`. Set `uA : (Eu l →L[ℝ] Eu l)ˣ` to `⟨Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) s.1.toBlocks₁₁, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) s.1.toBlocks₁₁⁻¹, by rw [← map_mul, mul_nonsing_inv _ hu, map_one], by rw [← map_mul, nonsing_inv_mul _ hu, map_one]⟩`. Establish `hA : IsUnit (bl Sum.inl Sum.inl s.1)` using `⟨uA, rfl⟩`. Establish `hinv : Ring.inverse (bl Sum.inl Sum.inl s.1) = Matrix.toEuclideanCLM (𝕜` using `ℝ) (n := l) s.1.toBlocks₁₁⁻¹ := Ring.inverse_unit uA`.

Establish `hAiB : Ring.inverse (bl Sum.inl Sum.inl s.1) * bl Sum.inl Sum.inr s.1 = Matrix.toEuclideanCLM (𝕜` using `ℝ) (n := l) (s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂) := by`. Rewrite using `[hinv, map_mul]`. Both sides reduce to the same expression. Establish `hdA : (bl Sum.inl Sum.inl s.1).det = s.1.toBlocks₁₁.det` using `det_bl _ _ _`. Establish `hdet : (Ring.inverse (bl Sum.inl Sum.inl s.1)).det * (bl Sum.inl Sum.inl s.1).det = 1`.

Use `congrArg ContinuousLinearMap.det (Ring.inverse_mul_cancel _ hA)` as an intermediate fact. Simplify `this` using `[ContinuousLinearMap.det]`. Use `set c : ℝ := (√|s.1.toBlocks₁₁.det|)⁻¹ with hcdef`. Establish `hcsq : c ^ 2 = |s.1.toBlocks₁₁.det|⁻¹`. Rewrite using `[hcdef, inv_pow, Real.sq_sqrt (abs_nonneg _)]`.

Establish `hc : c ^ 2 = |(Ring.inverse (bl Sum.inl Sum.inl s.1)).det|`. Rewrite using `[hcsq, eq_inv_of_mul_eq_one_left hdet, hdA, abs_inv]`. Establish `hc0 : c ≠ 0` using `inv_ne_zero (Real.sqrt_pos.2 (abs_pos.2 hd)).ne'`. Choose the witnesses or unpack the hypotheses as in `⟨z, hz1, hz, hzpos⟩ : ∃ z : ℂ, ‖z‖ = 1 ∧ z ^ 2 * ((c : ℂ) ^ 2 * (s.1.toBlocks₁₁.det : ℂ)) = 1 ∧ (0 < s.1.toBlocks₁₁.det → z = 1) := by`. Distinguish the cases in `hpos : 0 < s.1.toBlocks₁₁.det`.

Establish `e : c ^ 2 * s.1.toBlocks₁₁.det = 1`. Rewrite using `[hcsq, abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']`. Use `⟨1, by simp, ?_, fun _ => rfl⟩` and prove the remaining obligations. Establish `e2 : ((c : ℂ) ^ 2 * (s.1.toBlocks₁₁.det : ℂ)) = ((c ^ 2 * s.1.toBlocks₁₁.det : ℝ) : ℂ)` using `by push_cast; ring`. Rewrite using `[e2, e]`.

Simplify using the standard rewrite rules. Establish `hneg : s.1.toBlocks₁₁.det < 0` using `lt_of_le_of_ne (not_lt.1 hpos) hd`. Establish `e : c ^ 2 * s.1.toBlocks₁₁.det = -1`. Rewrite using `[hcsq, abs_of_neg hneg, inv_neg, neg_mul, inv_mul_cancel₀ hd]`. Use `⟨I, by simp, ?_, fun h => absurd h hpos⟩` and prove the remaining obligations.

Establish `e2 : ((c : ℂ) ^ 2 * (s.1.toBlocks₁₁.det : ℂ)) = ((c ^ 2 * s.1.toBlocks₁₁.det : ℝ) : ℂ)` using `by push_cast; ring`. Rewrite using `[e2, e, I_sq]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hz0 : z ≠ 0` using `fun h => by simp [h] at hz1`.

Establish `hU : IsUnit (z • sec s.1)`. Rewrite using `[Algebra.smul_def]`. Conclude with `((IsUnit.mk0 z hz0).map _).mul (isUnit_big hA.ringInverse _ _ hc0)`. Establish `hiso` using `iso_big hA.ringInverse (bl Sum.inl Sum.inr s.1) (bl Sum.inr Sum.inl s.1) hc`. Establish `hI : Impl (fun w => s.1 *ᵥ w) (z • sec s.1).toLinearMap`.

Use `⟨fun f => ?_, fun w => (intw_of_sympl (sympl_sp s) hA c w).smul z⟩` and prove the remaining obligations. Use `show ‖schwartzToL2 l ((z • sec s.1) f)‖ = ‖schwartzToL2 l f‖`. Rewrite using `[ContinuousLinearMap.smul_apply, map_smul, norm_smul, hz1, one_mul]`. Conclude with `hiso f`. Establish `hN : Nrm s.1 (z • sec s.1)`.

Introduce `s' f hf`. Establish `key` using `h2 _ (isSymm_inv_mul s hd) s' f hf`. Establish `ev : (z • sec s.1) f 0 = z * ((c : ℂ) * fou l (ph (-(Matrix.toEuclideanCLM (𝕜` using `ℝ) (n := l) (s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂))) (fouInv l f)) 0) := by`. Rewrite using `[ContinuousLinearMap.smul_apply, SchwartzMap.smul_apply, smul_eq_mul, sec_apply_zero s.1 hA f, hAiB]`. Rewrite using `[ev, dd_mul_eq s.1 s'.1 hd, ← key]`.

Combine the equalities or inequalities in the displayed calculation. Take `⟨g, hg1, hg2⟩` from `h1 s _ hU hI hN`. Conclude with `⟨g, z, hg1, hg2, hzpos⟩`.
-/
theorem secEx_of (h1 : MkElt l) (h2 : NrmUp l) : SecEx l := by
  intro s hd
  have hu : IsUnit s.1.toBlocks₁₁.det := isUnit_iff_ne_zero.2 hd
  let uA : (Eu l →L[ℝ] Eu l)ˣ :=
    ⟨Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) s.1.toBlocks₁₁, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) s.1.toBlocks₁₁⁻¹,
      by rw [← map_mul, mul_nonsing_inv _ hu, map_one], by rw [← map_mul, nonsing_inv_mul _ hu, map_one]⟩
  have hA : IsUnit (bl Sum.inl Sum.inl s.1) := ⟨uA, rfl⟩
  have hinv : Ring.inverse (bl Sum.inl Sum.inl s.1) = Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) s.1.toBlocks₁₁⁻¹ :=
    Ring.inverse_unit uA
  have hAiB : Ring.inverse (bl Sum.inl Sum.inl s.1) * bl Sum.inl Sum.inr s.1 =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) (s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂) := by
    rw [hinv, map_mul]
    rfl
  have hdA : (bl Sum.inl Sum.inl s.1).det = s.1.toBlocks₁₁.det := det_bl _ _ _
  have hdet : (Ring.inverse (bl Sum.inl Sum.inl s.1)).det * (bl Sum.inl Sum.inl s.1).det = 1 := by
    have := congrArg ContinuousLinearMap.det (Ring.inverse_mul_cancel _ hA)
    simpa [ContinuousLinearMap.det] using this
  set c : ℝ := (√|s.1.toBlocks₁₁.det|)⁻¹ with hcdef
  have hcsq : c ^ 2 = |s.1.toBlocks₁₁.det|⁻¹ := by
    rw [hcdef, inv_pow, Real.sq_sqrt (abs_nonneg _)]
  have hc : c ^ 2 = |(Ring.inverse (bl Sum.inl Sum.inl s.1)).det| := by
    rw [hcsq, eq_inv_of_mul_eq_one_left hdet, hdA, abs_inv]
  have hc0 : c ≠ 0 := inv_ne_zero (Real.sqrt_pos.2 (abs_pos.2 hd)).ne'
  obtain ⟨z, hz1, hz, hzpos⟩ : ∃ z : ℂ, ‖z‖ = 1 ∧ z ^ 2 * ((c : ℂ) ^ 2 * (s.1.toBlocks₁₁.det : ℂ)) = 1 ∧
      (0 < s.1.toBlocks₁₁.det → z = 1) := by
    by_cases hpos : 0 < s.1.toBlocks₁₁.det
    · have e : c ^ 2 * s.1.toBlocks₁₁.det = 1 := by
        rw [hcsq, abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']
      refine ⟨1, by simp, ?_, fun _ => rfl⟩
      have e2 : ((c : ℂ) ^ 2 * (s.1.toBlocks₁₁.det : ℂ)) = ((c ^ 2 * s.1.toBlocks₁₁.det : ℝ) : ℂ) := by push_cast; ring
      rw [e2, e]
      simp
    · have hneg : s.1.toBlocks₁₁.det < 0 := lt_of_le_of_ne (not_lt.1 hpos) hd
      have e : c ^ 2 * s.1.toBlocks₁₁.det = -1 := by
        rw [hcsq, abs_of_neg hneg, inv_neg, neg_mul, inv_mul_cancel₀ hd]
      refine ⟨I, by simp, ?_, fun h => absurd h hpos⟩
      have e2 : ((c : ℂ) ^ 2 * (s.1.toBlocks₁₁.det : ℂ)) = ((c ^ 2 * s.1.toBlocks₁₁.det : ℝ) : ℂ) := by push_cast; ring
      rw [e2, e, I_sq]
      push_cast
      ring
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz1
  have hU : IsUnit (z • sec s.1) := by
    rw [Algebra.smul_def]
    exact ((IsUnit.mk0 z hz0).map _).mul (isUnit_big hA.ringInverse _ _ hc0)
  have hiso := iso_big hA.ringInverse (bl Sum.inl Sum.inr s.1) (bl Sum.inr Sum.inl s.1) hc
  have hI : Impl (fun w => s.1 *ᵥ w) (z • sec s.1).toLinearMap := by
    refine ⟨fun f => ?_, fun w => (intw_of_sympl (sympl_sp s) hA c w).smul z⟩
    show ‖schwartzToL2 l ((z • sec s.1) f)‖ = ‖schwartzToL2 l f‖
    rw [ContinuousLinearMap.smul_apply, map_smul, norm_smul, hz1, one_mul]
    exact hiso f
  have hN : Nrm s.1 (z • sec s.1) := by
    intro s' f hf
    have key := h2 _ (isSymm_inv_mul s hd) s' f hf
    have ev : (z • sec s.1) f 0 = z * ((c : ℂ) *
        fou l (ph (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) (s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂))) (fouInv l f)) 0) := by
      rw [ContinuousLinearMap.smul_apply, SchwartzMap.smul_apply, smul_eq_mul, sec_apply_zero s.1 hA f, hAiB]
    rw [ev, dd_mul_eq s.1 s'.1 hd, ← key]
    calc _ = (z ^ 2 * ((c : ℂ) ^ 2 * (s.1.toBlocks₁₁.det : ℂ))) *
          ((fou l (ph (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) (s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂))) (fouInv l f)) 0) ^ 2 *
            (upperParabolic s'.1 + (s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂).map Complex.ofReal * loQ s'.1).det) := by ring
      _ = _ := by rw [hz, one_mul]
  obtain ⟨g, hg1, hg2⟩ := h1 s _ hU hI hN
  exact ⟨g, z, hg1, hg2, hzpos⟩

namespace C

def lo (t : ℝ) : Mat l := fromBlocks 1 0 (t • 1) 1

/- English proof (translation)
Rewrite using `[SymplecticGroup.mem_iff, lo, Matrix.J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]`. Simplify using the standard rewrite rules.
-/
theorem lo_mem (t : ℝ) : lo (l := l) t ∈ Matrix.symplecticGroup l ℝ := by
  rw [SymplecticGroup.mem_iff, lo, Matrix.J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp

/- English proof (translation)
Rewrite using `[lo, lo, fromBlocks_multiply]`. Simplify using the standard rewrite rules.
-/
theorem lo_mul (t : ℝ) : lo (l := l) t * lo (-t) = 1 := by
  rw [lo, lo, fromBlocks_multiply]
  simp

/- English proof (translation)
Use `conv_lhs => rw [← fromBlocks_toBlocks s, lo, fromBlocks_multiply, toBlocks_fromBlocks₁₁]`. Simplify using the standard rewrite rules.
-/
theorem toBlocks₁₁_mul_lo (s : Mat l) (t : ℝ) : (s * lo t).toBlocks₁₁ = s.toBlocks₁₁ + t • s.toBlocks₁₂ := by
  conv_lhs => rw [← fromBlocks_toBlocks s, lo, fromBlocks_multiply, toBlocks_fromBlocks₁₁]
  simp

/- English proof (translation)
Set `M : Matrix l l (Polynomial ℝ)` to `Matrix.of fun a b => Polynomial.C (s (.inl a) (.inl b)) + Polynomial.X * Polynomial.C (s (.inl a) (.inr b))`. Establish `hev : ∀ t : ℝ, Polynomial.eval t M.det = (s.toBlocks₁₁ + t • s.toBlocks₁₂).det` using `fun t => by`. Establish `e : Polynomial.eval t M.det = ((Polynomial.evalRingHom t).mapMatrix M).det` using `RingHom.map_det (Polynomial.evalRingHom t) M`. Rewrite using `[e]`. Use `congr 1`.

Use extensionality with `a b`. Simplify using `[M, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂]`. Expand and normalize the polynomial expressions, which then agree. Establish `hev' : Polynomial.eval₂ Complex.ofRealHom (-I) M.det = dd s`. Establish `e : Polynomial.eval₂ Complex.ofRealHom (-I) M.det = ((Polynomial.eval₂RingHom Complex.ofRealHom (-I)).mapMatrix M).det` using `RingHom.map_det (Polynomial.eval₂RingHom Complex.ofRealHom (-I)) M`.

Rewrite using `[e, dd]`. Use `congr 1`. Use extensionality with `a b`. Simplify using `[M, upperParabolic]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hP : M.det ≠ 0` using `fun h0 => h (by rw [← hev', h0, Polynomial.eval₂_zero])`. Assume the negation of the conclusion as `hall`. Use `push Not at hall`. Apply `hP` to reduce the goal to its premises. Apply `Polynomial.eq_zero_of_infinite_isRoot` to reduce the goal to its premises.

Use `Set.infinite_univ (α := ℝ)` and compare the differences between its conclusion and the goal. Use extensionality with `t`. Simplify using `only [Set.mem_setOf_eq, Polynomial.IsRoot.def, hev, hall, Set.mem_univ]`.
-/
theorem exists_det_ne (s : Mat l) (h : dd s ≠ 0) : ∃ t : ℝ, (s.toBlocks₁₁ + t • s.toBlocks₁₂).det ≠ 0 := by
  let M : Matrix l l (Polynomial ℝ) := Matrix.of fun a b =>
    Polynomial.C (s (.inl a) (.inl b)) + Polynomial.X * Polynomial.C (s (.inl a) (.inr b))
  have hev : ∀ t : ℝ, Polynomial.eval t M.det = (s.toBlocks₁₁ + t • s.toBlocks₁₂).det := fun t => by
    have e : Polynomial.eval t M.det = ((Polynomial.evalRingHom t).mapMatrix M).det :=
      RingHom.map_det (Polynomial.evalRingHom t) M
    rw [e]
    congr 1
    ext a b
    simp [M, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂]
    ring
  have hev' : Polynomial.eval₂ Complex.ofRealHom (-I) M.det = dd s := by
    have e : Polynomial.eval₂ Complex.ofRealHom (-I) M.det =
        ((Polynomial.eval₂RingHom Complex.ofRealHom (-I)).mapMatrix M).det :=
      RingHom.map_det (Polynomial.eval₂RingHom Complex.ofRealHom (-I)) M
    rw [e, dd]
    congr 1
    ext a b
    simp [M, upperParabolic]
    ring
  have hP : M.det ≠ 0 := fun h0 => h (by rw [← hev', h0, Polynomial.eval₂_zero])
  by_contra hall
  push Not at hall
  apply hP
  apply Polynomial.eq_zero_of_infinite_isRoot
  convert Set.infinite_univ (α := ℝ)
  ext t
  simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, hev, hall, Set.mem_univ]

end C

/- English proof (translation)
Introduce `s`. Take `⟨t, ht⟩` from `exists_det_ne s.1 (h1 s)`. Set `n : Sp l` to `⟨lo t, lo_mem t⟩`. Set `m : Sp l` to `⟨lo (-t), lo_mem (-t)⟩`. Establish `e1 : (s * n).1.toBlocks₁₁.det ≠ 0` using `by show (s.1 * lo t).toBlocks₁₁.det ≠ 0`.

Rewrite using `[toBlocks₁₁_mul_lo]`. Conclude with `ht`. Establish `e2 : m.1.toBlocks₁₁.det ≠ 0` using `by show (lo (l := l) (-t)).toBlocks₁₁.det ≠ 0`. Simplify using `[lo]`. Take `⟨g1, -, hg1, -⟩` from `h2 (s * n) e1`.

Take `⟨g2, -, hg2, -⟩` from `h2 m e2`. Use `⟨g1 * g2, ?_⟩` and prove the remaining obligations. Establish `hnm : n * m = 1` using `Subtype.ext (lo_mul t)`. Rewrite using `[map_mul, hg1, hg2, mul_assoc, hnm, mul_one]`.
-/
theorem surj_of (h1 : DdNe l) (h2 : SecEx l) : Surj l := by
  intro s
  obtain ⟨t, ht⟩ := exists_det_ne s.1 (h1 s)
  let n : Sp l := ⟨lo t, lo_mem t⟩
  let m : Sp l := ⟨lo (-t), lo_mem (-t)⟩
  have e1 : (s * n).1.toBlocks₁₁.det ≠ 0 := by
    show (s.1 * lo t).toBlocks₁₁.det ≠ 0
    rw [toBlocks₁₁_mul_lo]
    exact ht
  have e2 : m.1.toBlocks₁₁.det ≠ 0 := by
    show (lo (l := l) (-t)).toBlocks₁₁.det ≠ 0
    simp [lo]
  obtain ⟨g1, -, hg1, -⟩ := h2 (s * n) e1
  obtain ⟨g2, -, hg2, -⟩ := h2 m e2
  refine ⟨g1 * g2, ?_⟩
  have hnm : n * m = 1 := Subtype.ext (lo_mul t)
  rw [map_mul, hg1, hg2, mul_assoc, hnm, mul_one]

end PositivityTheory.ThKR.Mp
