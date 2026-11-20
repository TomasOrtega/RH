import Formalism.FlagUnipotentLattices.UnipotentStabiliserCharacterisation
import Formalism.FormalDegreeBessel.FinalG

namespace Formalism.HermitianLatticeCounting.P
section GrpL
open Formalism.HermitianLatticeCounting.ExpansionTerms MeasureTheory Real
open scoped FourierTransform RealInnerProductSpace

/- English proof (translation)
Unfold `TruncationCutoff`. Distinguish the cases in `ht : t = 0`. Simplify using `[ht]`. Establish `hpt : π * t ≠ 0` using `mul_ne_zero Real.pi_ne_zero ht`. Rewrite using `[if_neg hpt, if_neg ht, div_mul_eq_div_div]`.
-/
lemma gl_cut_scale (x t : ℝ) : TruncationCutoff 3 x (π * t) = TruncationCutoff 3 (x / π) t := by
  unfold TruncationCutoff
  by_cases ht : t = 0
  · simp [ht]
  · have hpt : π * t ≠ 0 := mul_ne_zero Real.pi_ne_zero ht
    rw [if_neg hpt, if_neg ht, div_mul_eq_div_div]

/- English proof (translation)
Rewrite using `[Real.fourier_eq']`. Use `congr 1`. Use extensionality with `c`. Rewrite using `[smul_eq_mul]`. Use `congr 2`.

Establish `: ⟪c, w⟫ = c.re * w.re + c.im * w.im`. Rewrite using `[Complex.inner]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Simplify using `only [Complex.mul_im, Complex.neg_im, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma gl_fourier_eq (φ : ℂ → ℂ) (w : ℂ) :
    𝓕 φ w = ∫ c : ℂ, Complex.exp (2 * Complex.I *
      (((-(Complex.I * (π : ℂ) * (starRingEnd ℂ) w)) * c).im : ℂ)) * φ c := by
  rw [Real.fourier_eq']
  congr 1
  ext c
  rw [smul_eq_mul]
  congr 2
  have : ⟪c, w⟫ = c.re * w.re + c.im * w.im := by
    rw [Complex.inner]
    simp
    ring
  rw [this]
  simp only [Complex.mul_im, Complex.neg_im, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  push_cast
  ring

/- English proof (translation)
Introduce `φ x M hc hi hx hb c`. Take `⟨hI, hV⟩` from `hE 3 (x / π) (by norm_num) (div_pos hx pi_pos)`. Establish `hbd : ∀ w : ℂ, ‖𝓕 φ w‖ ≤ M * TruncationCutoff 3 (x / π) ‖w‖`. Introduce `w`. Rewrite using `[gl_fourier_eq, ← gl_cut_scale]`.

Use `hb (-(Complex.I * (π : ℂ) * (starRingEnd ℂ) w))` as an intermediate fact. Establish `hn : ‖(-(Complex.I * (π : ℂ) * (starRingEnd ℂ) w))‖ = π * ‖w‖`. Rewrite using `[norm_neg, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, RCLike.norm_conj, Real.norm_of_nonneg pi_pos.le]`. Rewrite `this` using `[hn]`. Then use the resulting hypothesis. Establish `hcont : Continuous (𝓕 φ)` using `VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hi`.

Establish `hFi : Integrable (𝓕 φ)` using `(hI.const_mul M).mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall hbd)`. Establish `hinv : 𝓕⁻ (𝓕 φ) c = φ c` using `hi.fourierInv_fourier_eq hFi hc.continuousAt`. Rewrite using `[← hinv, Real.fourierInv_eq]`. Combine the equalities or inequalities in the displayed calculation. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem lemSSupBound_of (hE : Formalism.HermitianLatticeCounting.ExpansionTerms.CutoffIntegralFormula) : Formalism.HermitianLatticeCounting.ExpansionTerms.LemSSupBound := by
  intro φ x M hc hi hx hb c
  obtain ⟨hI, hV⟩ := hE 3 (x / π) (by norm_num) (div_pos hx pi_pos)
  have hbd : ∀ w : ℂ, ‖𝓕 φ w‖ ≤ M * TruncationCutoff 3 (x / π) ‖w‖ := by
    intro w
    rw [gl_fourier_eq, ← gl_cut_scale]
    have := hb (-(Complex.I * (π : ℂ) * (starRingEnd ℂ) w))
    have hn : ‖(-(Complex.I * (π : ℂ) * (starRingEnd ℂ) w))‖ = π * ‖w‖ := by
      rw [norm_neg, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, RCLike.norm_conj,
        Real.norm_of_nonneg pi_pos.le]
    rwa [hn] at this
  have hcont : Continuous (𝓕 φ) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hi
  have hFi : Integrable (𝓕 φ) :=
    (hI.const_mul M).mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall hbd)
  have hinv : 𝓕⁻ (𝓕 φ) c = φ c := hi.fourierInv_fourier_eq hFi hc.continuousAt
  rw [← hinv, Real.fourierInv_eq]
  calc ‖∫ v, 𝐞 ⟪v, c⟫ • 𝓕 φ v‖ ≤ ∫ v, ‖𝐞 ⟪v, c⟫ • 𝓕 φ v‖ := norm_integral_le_integral_norm _
    _ = ∫ v, ‖𝓕 φ v‖ := by simp_rw [Circle.norm_smul]
    _ ≤ ∫ v : ℂ, M * TruncationCutoff 3 (x / π) ‖v‖ := integral_mono hFi.norm (hI.const_mul M) hbd
    _ = M * (π * (x / π) ^ 2 * (3 / (3 - 2))) := by rw [integral_const_mul, hV]
    _ = 3 / π * x ^ 2 * M := by
      field_simp
      ring

/- English proof (translation)
Establish `h` using `integrable_fun_norm_addHaar (E := ℂ) (volume : Measure ℂ) (f := f)`. Simplify `h` using `[Complex.finrank_real_complex]`.
-/
lemma gl_radial_integrable (f : ℝ → ℝ) :
    Integrable (fun x : ℂ => f ‖x‖) ↔ IntegrableOn (fun y : ℝ => y * f y) (Set.Ioi 0) := by
  have h := integrable_fun_norm_addHaar (E := ℂ) (volume : Measure ℂ) (f := f)
  simpa [Complex.finrank_real_complex] using h

/- English proof (translation)
Establish `h` using `integral_fun_norm_addHaar (E := ℂ) (volume : Measure ℂ) f`. Establish `hv : (volume : Measure ℂ).real (Metric.ball 0 1) = π`. Simplify using `[Measure.real, Complex.volume_ball]`. Rewrite using `[h, hv]`. Simplify using `[Complex.finrank_real_complex]`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma gl_radial_integral (f : ℝ → ℝ) :
    ∫ x : ℂ, f ‖x‖ = 2 * π * ∫ y in Set.Ioi (0 : ℝ), y * f y := by
  have h := integral_fun_norm_addHaar (E := ℂ) (volume : Measure ℂ) f
  have hv : (volume : Measure ℂ).real (Metric.ball 0 1) = π := by
    simp [Measure.real, Complex.volume_ball]
  rw [h, hv]
  simp [Complex.finrank_real_complex]
  ring

/- English proof (translation)
Unfold `TruncationCutoff`. Rewrite using `[if_neg hy.ne', min_eq_left, mul_one]`. Conclude with `Real.one_le_rpow ((one_le_div hy).mpr h) hK`.
-/
lemma gl_cut_le {K L y : ℝ} (hK : 0 ≤ K) (hy : 0 < y) (h : y ≤ L) : y * TruncationCutoff K L y = y := by
  unfold TruncationCutoff
  rw [if_neg hy.ne', min_eq_left, mul_one]
  exact Real.one_le_rpow ((one_le_div hy).mpr h) hK

/- English proof (translation)
Establish `hy : 0 < y` using `hL.trans h`. Unfold `TruncationCutoff`. Rewrite using `[if_neg hy.ne', min_eq_right]`. Rewrite using `[Real.div_rpow hL.le hy.le, Real.rpow_sub hy, Real.rpow_one]`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `Real.rpow_le_one (div_nonneg hL.le hy.le) ((div_le_one hy).mpr h.le) hK`.
-/
lemma gl_cut_gt {K L y : ℝ} (hK : 0 ≤ K) (hL : 0 < L) (h : L < y) :
    y * TruncationCutoff K L y = L ^ K * y ^ (1 - K) := by
  have hy : 0 < y := hL.trans h
  unfold TruncationCutoff
  rw [if_neg hy.ne', min_eq_right]
  · rw [Real.div_rpow hL.le hy.le, Real.rpow_sub hy, Real.rpow_one]
    ring
  · exact Real.rpow_le_one (div_nonneg hL.le hy.le) ((div_le_one hy).mpr h.le) hK

/- English proof (translation)
Establish `hE : Set.EqOn (fun y : ℝ => y * TruncationCutoff K L y) (fun y => y) (Set.Ioc 0 L)` using `fun y hy => gl_cut_le hK hy.1 hy.2`. Use `IntegrableOn.congr_fun ?_ hE.symm measurableSet_Ioc` and prove the remaining obligations. Conclude with `(continuous_id'.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self`.
-/
lemma integrableOn_Ioc_truncated_power_moment {K L : ℝ} (hK : 0 ≤ K) :
    IntegrableOn (fun y : ℝ => y * TruncationCutoff K L y) (Set.Ioc 0 L) := by
  have hE : Set.EqOn (fun y : ℝ => y * TruncationCutoff K L y) (fun y => y) (Set.Ioc 0 L) :=
    fun y hy => gl_cut_le hK hy.1 hy.2
  refine IntegrableOn.congr_fun ?_ hE.symm measurableSet_Ioc
  exact (continuous_id'.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self

/- English proof (translation)
Establish `hE : Set.EqOn (fun y : ℝ => y * TruncationCutoff K L y) (fun y => L ^ K * y ^ (1 - K)) (Set.Ioi L)` using `fun y hy => gl_cut_gt (by linarith) hL hy`. Use `IntegrableOn.congr_fun ?_ hE.symm measurableSet_Ioi` and prove the remaining obligations. Conclude with `Integrable.const_mul (integrableOn_Ioi_rpow_of_lt (by linarith) hL) _`.
-/
lemma integrableOn_Ioi_truncated_power_moment {K L : ℝ} (hK : 2 < K) (hL : 0 < L) :
    IntegrableOn (fun y : ℝ => y * TruncationCutoff K L y) (Set.Ioi L) := by
  have hE : Set.EqOn (fun y : ℝ => y * TruncationCutoff K L y) (fun y => L ^ K * y ^ (1 - K)) (Set.Ioi L) :=
    fun y hy => gl_cut_gt (by linarith) hL hy
  refine IntegrableOn.congr_fun ?_ hE.symm measurableSet_Ioi
  exact Integrable.const_mul (integrableOn_Ioi_rpow_of_lt (by linarith) hL) _

/- English proof (translation)
Introduce `K L hK hL`. Establish `hK0 : 0 ≤ K` using `by linarith`. Establish `hU : Set.Ioi (0 : ℝ) = Set.Ioc 0 L ∪ Set.Ioi L` using `(Set.Ioc_union_Ioi_eq_Ioi hL.le).symm`. Prove the components needed by the constructor for the conclusion. Rewrite using `[gl_radial_integrable (fun y => TruncationCutoff K L y), hU]`.

Conclude with `(integrableOn_Ioc_truncated_power_moment hK0).union (integrableOn_Ioi_truncated_power_moment hK hL)`. Rewrite using `[gl_radial_integral (fun y => TruncationCutoff K L y), hU, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi (integrableOn_Ioc_truncated_power_moment hK0) (integrableOn_Ioi_truncated_power_moment hK hL), setIntegral_congr_fun measurableSet_Ioc (fun y hy => gl_cut_ …`. Establish `e : L ^ K * L ^ (1 - K + 1) = L ^ 2`. Rewrite using `[← Real.rpow_add hL, ← Real.rpow_natCast]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hK2 : K - 2 ≠ 0` using `by linarith [hK]`. Establish `hK3 : 1 - K + 1 ≠ 0`. Introduce `h`.

Apply `hK2` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e2 : L ^ K * (-L ^ (1 - K + 1) / (1 - K + 1)) = L ^ 2 / (K - 2)`. Rewrite using `[← e]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
lemma gl_e3Integral : Formalism.HermitianLatticeCounting.ExpansionTerms.CutoffIntegralFormula := by
  intro K L hK hL
  have hK0 : 0 ≤ K := by linarith
  have hU : Set.Ioi (0 : ℝ) = Set.Ioc 0 L ∪ Set.Ioi L := (Set.Ioc_union_Ioi_eq_Ioi hL.le).symm
  constructor
  · rw [gl_radial_integrable (fun y => TruncationCutoff K L y), hU]
    exact (integrableOn_Ioc_truncated_power_moment hK0).union (integrableOn_Ioi_truncated_power_moment hK hL)
  · rw [gl_radial_integral (fun y => TruncationCutoff K L y), hU,
      setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi (integrableOn_Ioc_truncated_power_moment hK0)
        (integrableOn_Ioi_truncated_power_moment hK hL),
      setIntegral_congr_fun measurableSet_Ioc (fun y hy => gl_cut_le hK0 hy.1 hy.2),
      setIntegral_congr_fun measurableSet_Ioi (fun y hy => gl_cut_gt hK0 hL hy),
      integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : 1 - K < -1) hL,
      ← intervalIntegral.integral_of_le hL.le, integral_id]
    have e : L ^ K * L ^ (1 - K + 1) = L ^ 2 := by
      rw [← Real.rpow_add hL, ← Real.rpow_natCast]
      congr 1
      push_cast
      ring
    have hK2 : K - 2 ≠ 0 := by linarith [hK]
    have hK3 : 1 - K + 1 ≠ 0 := by
      intro h
      apply hK2
      linarith
    have e2 : L ^ K * (-L ^ (1 - K + 1) / (1 - K + 1)) = L ^ 2 / (K - 2) := by
      rw [← e]
      field_simp
      ring
    rw [e2]
    field_simp
    ring

/- English proof (translation)
The claim follows from `lemSSupBound_of gl_e3Integral`.
-/
theorem sup_bound_of_truncated_integral : Formalism.HermitianLatticeCounting.ExpansionTerms.LemSSupBound := lemSSupBound_of gl_e3Integral

end GrpL
end Formalism.HermitianLatticeCounting.P

namespace Formalism.HermitianLatticeCounting.P
section GA
open Formalism.HermitianLatticeCounting.ExpansionTerms
open Finset Matrix
open scoped ComplexConjugate fwdDiff

/- English proof (translation)
Introduce `V _ _ h hs e v x y`. Simplify using `only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, map_smulₛₗ, smul_eq_mul, RingHom.id_apply]`. Rewrite using `[← hs y v, ← hs y e]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rank_two_operator_skew_hermitian : Formalism.HermitianLatticeCounting.ExpansionTerms.RankTwoOperatorSkewHermitian := by
  intro V _ _ h hs e v x y
  simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, map_smulₛₗ, smul_eq_mul,
    RingHom.id_apply]
  rw [← hs y v, ← hs y e]
  ring

end GA
end Formalism.HermitianLatticeCounting.P

namespace Formalism.HermitianLatticeCounting.P
section GG
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset Matrix

/- English proof (translation)
Establish `a1` using `c.sizeUpTo_index_le i`. Establish `a2 : (i : ℕ) < c.sizeUpTo ((c.index i : ℕ) + 1)` using `c.lt_sizeUpTo_index_succ i`. Break down `lt_trichotomy (c.index i : ℕ) a with hlt | heq | hgt` into its components or cases. Use `c.monotone_sizeUpTo (show (c.index i : ℕ) + 1 ≤ a from hlt)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Conclude with `heq`. Use `c.monotone_sizeUpTo (show a + 1 ≤ (c.index i : ℕ) from hgt)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
lemma gg_index_eq {d : ℕ} (c : Composition d) (i : Fin d) (a : ℕ)
    (h1 : c.sizeUpTo a ≤ (i : ℕ)) (h2 : (i : ℕ) < c.sizeUpTo (a + 1)) : (c.index i : ℕ) = a := by
  have a1 := c.sizeUpTo_index_le i
  have a2 : (i : ℕ) < c.sizeUpTo ((c.index i : ℕ) + 1) := c.lt_sizeUpTo_index_succ i
  rcases lt_trichotomy (c.index i : ℕ) a with hlt | heq | hgt
  · have := c.monotone_sizeUpTo (show (c.index i : ℕ) + 1 ≤ a from hlt); omega
  · exact heq
  · have := c.monotone_sizeUpTo (show a + 1 ≤ (c.index i : ℕ) from hgt); omega

/- English proof (translation)
Proceed by induction on `s with`. Consider the case `zero => simp`. Consider the case `succ s ih`. Rewrite using `[Matrix.det_succ_row_zero, Finset.sum_eq_single (Fin.last s)]`. Establish `: ((Matrix.of fun i j : Fin (s + 1) => if (i : ℕ) + (j : ℕ) + 1 = s + 1 then t else 0).submatrix Fin.succ (Fin.last s).succAbove) = Matrix.of fun i j : Fin s => if (i : ℕ) + (j : ℕ) + 1 = s then t else 0`.

Use extensionality with `i j`. Simplify using `only [Matrix.submatrix_apply, Matrix.of_apply, Fin.succAbove_last, Fin.val_succ, Fin.val_castSucc]`. Use `congr 1`. Conclude with `propext ⟨fun h => by omega, fun h => by omega⟩`. Rewrite using `[this, ih]`.

Simplify using `only [Matrix.of_apply, Fin.val_zero, Fin.val_last, zero_add, if_true]`. Establish `hc : (s + 1).choose 2 = s + s.choose 2`. Rewrite using `[Nat.choose_succ_succ' s 1, Nat.choose_one_right]`. Rewrite using `[hc]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `j _ hj`. Establish `: ¬ (((0 : Fin (s + 1)) : ℕ) + (j : ℕ) + 1 = s + 1)`. Introduce `h`. Apply `hj` to reduce the goal to its premises. Use `ext`.

Simplify using `at h ⊢`. Use linear arithmetic over natural numbers and integers. Simplify using `only [Matrix.of_apply, this, if_false]`. Expand and normalize the polynomial expressions, which then agree. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`.
-/
lemma gg_antidiag_det {R : Type*} [CommRing R] (t : R) (s : ℕ) :
    (Matrix.of fun i j : Fin s => if (i : ℕ) + (j : ℕ) + 1 = s then t else 0).det =
      (-1) ^ (s.choose 2) * t ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Matrix.det_succ_row_zero, Finset.sum_eq_single (Fin.last s)]
    · have : ((Matrix.of fun i j : Fin (s + 1) => if (i : ℕ) + (j : ℕ) + 1 = s + 1 then t else 0).submatrix
          Fin.succ (Fin.last s).succAbove) =
          Matrix.of fun i j : Fin s => if (i : ℕ) + (j : ℕ) + 1 = s then t else 0 := by
        ext i j
        simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.succAbove_last, Fin.val_succ,
          Fin.val_castSucc]
        congr 1
        exact propext ⟨fun h => by omega, fun h => by omega⟩
      rw [this, ih]
      simp only [Matrix.of_apply, Fin.val_zero, Fin.val_last, zero_add, if_true]
      have hc : (s + 1).choose 2 = s + s.choose 2 := by
        rw [Nat.choose_succ_succ' s 1, Nat.choose_one_right]
      rw [hc]
      ring
    · intro j _ hj
      have : ¬ (((0 : Fin (s + 1)) : ℕ) + (j : ℕ) + 1 = s + 1) := by
        intro h
        apply hj
        ext
        simp at h ⊢
        omega
      simp only [Matrix.of_apply, this, if_false]
      ring
    · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Unfold `leadingPrincipalMinor`. Rewrite using `[Matrix.twoBlockTriangular_det _ (fun x : {i : Fin d // (i : ℕ) < q + s} => (x.1 : ℕ) < q)]`. Use `congr 1`. Set `e : {i : Fin d // (i : ℕ) < q} ≃ {x : {i : Fin d // (i : ℕ) < q + s} // (x.1 : ℕ) < q}` to `{ toFun := fun i => ⟨⟨i.1, by have := i.2; omega⟩, i.2⟩ invFun := fun x => ⟨x.1.1, x.2⟩ left_inv := fun i => rfl right_inv := fun x => rfl }`. Rewrite using `[← Matrix.det_submatrix_equiv_self e]`.

Both sides reduce to the same expression. Set `e : Fin s ≃ {x : {i : Fin d // (i : ℕ) < q + s} // ¬ (x.1 : ℕ) < q}` to `{ toFun := fun i => ⟨⟨⟨q + i, by have := i.2; omega⟩, by have := i.2; simp⟩, by simp⟩ invFun := fun x => ⟨(x.1.1 : ℕ) - q, by have := x.1.2; have := x.2; omega⟩ left_inv := fun i => by ext; simp right_inv := fun x => by`. Use `x.2` as an intermediate fact. Use `ext`. Simplify using the standard rewrite rules.

Use `omega }`. Rewrite using `[← Matrix.det_submatrix_equiv_self e, ← gg_antidiag_det]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `only [Matrix.submatrix_apply, Matrix.toSquareBlockProp_def, Matrix.of_apply, e, Equiv.coe_fn_mk]`.

Rewrite using `[hD _ _ (by simp) (by simp) (by simp) (by simp)]`. Use `congr 1`. Conclude with `propext ⟨fun h => by simp at h; omega, fun h => by simp; omega⟩`. Introduce `i hi j hj`. Conclude with `h0 i.1 j.1 (not_lt.mp hi) i.2 hj`.
-/
lemma gg_step {d : ℕ} {R : Type*} [CommRing R] (Z : Matrix (Fin d) (Fin d) R) (q s : ℕ) (t : R)
    (hqs : q + s ≤ d)
    (h0 : ∀ i j : Fin d, q ≤ (i : ℕ) → (i : ℕ) < q + s → (j : ℕ) < q → Z i j = 0)
    (hD : ∀ i j : Fin d, q ≤ (i : ℕ) → (i : ℕ) < q + s → q ≤ (j : ℕ) → (j : ℕ) < q + s →
      Z i j = if (i : ℕ) + (j : ℕ) + 1 = 2 * q + s then t else 0) :
    leadingPrincipalMinor Z (q + s) = leadingPrincipalMinor Z q * ((-1) ^ (s.choose 2) * t ^ s) := by
  unfold leadingPrincipalMinor
  rw [Matrix.twoBlockTriangular_det _ (fun x : {i : Fin d // (i : ℕ) < q + s} => (x.1 : ℕ) < q)]
  · congr 1
    · let e : {i : Fin d // (i : ℕ) < q} ≃
          {x : {i : Fin d // (i : ℕ) < q + s} // (x.1 : ℕ) < q} :=
        { toFun := fun i => ⟨⟨i.1, by have := i.2; omega⟩, i.2⟩
          invFun := fun x => ⟨x.1.1, x.2⟩
          left_inv := fun i => rfl
          right_inv := fun x => rfl }
      rw [← Matrix.det_submatrix_equiv_self e]
      rfl
    · let e : Fin s ≃ {x : {i : Fin d // (i : ℕ) < q + s} // ¬ (x.1 : ℕ) < q} :=
        { toFun := fun i => ⟨⟨⟨q + i, by have := i.2; omega⟩, by have := i.2; simp⟩, by simp⟩
          invFun := fun x => ⟨(x.1.1 : ℕ) - q, by have := x.1.2; have := x.2; omega⟩
          left_inv := fun i => by ext; simp
          right_inv := fun x => by
            have := x.2
            ext
            simp
            omega }
      rw [← Matrix.det_submatrix_equiv_self e, ← gg_antidiag_det]
      congr 1
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.toSquareBlockProp_def, Matrix.of_apply, e,
        Equiv.coe_fn_mk]
      rw [hD _ _ (by simp) (by simp) (by simp) (by simp)]
      congr 1
      exact propext ⟨fun h => by simp at h; omega, fun h => by simp; omega⟩
  · intro i hi j hj
    exact h0 i.1 j.1 (not_lt.mp hi) i.2 hj

/- English proof (translation)
Introduce `R _ d c t q hq hne`. Establish `hqd : q < d` using `lt_of_le_of_ne hq (by rw [← c.sizeUpTo_length]; exact hne _)`. Use `set a : ℕ := (c.index ⟨q, hqd⟩ : ℕ) with ha`. Establish `h1 : c.sizeUpTo a ≤ q` using `c.sizeUpTo_index_le ⟨q, hqd⟩`. Establish `h2 : q < c.sizeUpTo (a + 1)` using `c.lt_sizeUpTo_index_succ ⟨q, hqd⟩`.

Establish `h1' : c.sizeUpTo a < q` using `lt_of_le_of_ne h1 (fun h => hne a h.symm)`. Unfold `leadingPrincipalMinor`. Apply `Matrix.det_eq_zero_of_row_eq_zero (⟨⟨c.sizeUpTo a, by omega⟩, h1'⟩ : {i : Fin d // (i : ℕ) < q})` to reduce the goal to its premises. Introduce `j`. Establish `hj` using `j.2`.

Establish `hidx : (c.index ⟨c.sizeUpTo a, by omega⟩ : ℕ) = a` using `gg_index_eq c _ a le_rfl (by simp; omega)`. Simplify using `only [Matrix.submatrix_apply, blockAntidiagonalMatrix]`. Rewrite using `[if_neg]`. Introduce and unpack `⟨-, h⟩`. Rewrite `h` using `[hidx]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem leading_minor_vanishes_off_block_ends : Formalism.HermitianLatticeCounting.ExpansionTerms.LeadingMinorVanishesOffBlockEnds := by
  intro R _ d c t q hq hne
  have hqd : q < d := lt_of_le_of_ne hq (by rw [← c.sizeUpTo_length]; exact hne _)
  set a : ℕ := (c.index ⟨q, hqd⟩ : ℕ) with ha
  have h1 : c.sizeUpTo a ≤ q := c.sizeUpTo_index_le ⟨q, hqd⟩
  have h2 : q < c.sizeUpTo (a + 1) := c.lt_sizeUpTo_index_succ ⟨q, hqd⟩
  have h1' : c.sizeUpTo a < q := lt_of_le_of_ne h1 (fun h => hne a h.symm)
  unfold leadingPrincipalMinor
  apply Matrix.det_eq_zero_of_row_eq_zero (⟨⟨c.sizeUpTo a, by omega⟩, h1'⟩ : {i : Fin d // (i : ℕ) < q})
  intro j
  have hj := j.2
  have hidx : (c.index ⟨c.sizeUpTo a, by omega⟩ : ℕ) = a :=
    gg_index_eq c _ a le_rfl (by simp; omega)
  simp only [Matrix.submatrix_apply, blockAntidiagonalMatrix]
  rw [if_neg]
  rintro ⟨-, h⟩
  rw [hidx] at h
  omega

/- English proof (translation)
Introduce `R _ d c t p`. Proceed by induction on `p with`. Consider the case `zero`. Establish `: IsEmpty {i : Fin d // (i : ℕ) < c.sizeUpTo 0}` using `⟨fun i => by have := i.2; simp at this⟩`. Simplify using `[leadingPrincipalMinor]`.

Consider the case `succ p ih`. Distinguish the cases in `hp : p < c.length`. Establish `hs : c.sizeUpTo (p + 1) = c.sizeUpTo p + c.blocksFun ⟨p, hp⟩` using `c.sizeUpTo_succ' ⟨p, hp⟩`. Establish `hle : c.sizeUpTo p + c.blocksFun ⟨p, hp⟩ ≤ d` using `hs ▸ c.sizeUpTo_le _`. Establish `hf : univ.filter (fun a : Fin c.length => (a : ℕ) < p + 1) = insert ⟨p, hp⟩ (univ.filter (fun a : Fin c.length => (a : ℕ) < p))`.

Use extensionality with `a`. Simplify using `only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hf, Finset.prod_insert (by simp), ← ih, hs, mul_comm]`. Apply `gg_step _ _ _ _ hle` to reduce the goal to its premises.

Introduce `i j hi1 hi2 hj`. Establish `hidx : (c.index i : ℕ) = p` using `gg_index_eq c i p hi1 (by omega)`. Simplify using `only [blockAntidiagonalMatrix]`. Rewrite using `[if_neg]`. Introduce and unpack `⟨h, -⟩`.

Use `c.sizeUpTo_index_le j` as an intermediate fact. Rewrite `this` using `[← h, hidx]`. Use linear arithmetic over natural numbers and integers. Introduce `i j hi1 hi2 hj1 hj2`. Establish `hidx : (c.index i : ℕ) = p` using `gg_index_eq c i p hi1 (by omega)`.

Establish `hjdx : (c.index j : ℕ) = p` using `gg_index_eq c j p hj1 (by omega)`. Establish `hi' : c.index i = ⟨p, hp⟩` using `Fin.ext hidx`. Establish `hj' : c.index j = ⟨p, hp⟩` using `Fin.ext hjdx`. Simplify using `only [blockAntidiagonalMatrix, hi', hj', true_and]`. Use `congr 1`.

Conclude with `propext ⟨fun h => by omega, fun h => by omega⟩`. Establish `hp' : c.length ≤ p` using `not_lt.mp hp`. Establish `he : c.sizeUpTo (p + 1) = c.sizeUpTo p`. Rewrite using `[c.sizeUpTo_ofLength_le (p + 1) (by omega), c.sizeUpTo_ofLength_le p hp']`. Rewrite using `[he, ih]`.

Apply `Finset.prod_congr _ (fun _ _ => rfl)` to reduce the goal to its premises. Use extensionality with `a`. Use `a.2` as an intermediate fact. Simplify using `only [mem_filter, mem_univ, true_and]`. Use linear arithmetic over natural numbers and integers.
-/
theorem leading_minor_at_block_end : Formalism.HermitianLatticeCounting.ExpansionTerms.LeadingMinorAtBlockEnd := by
  intro R _ d c t p
  induction p with
  | zero =>
    have : IsEmpty {i : Fin d // (i : ℕ) < c.sizeUpTo 0} := ⟨fun i => by have := i.2; simp at this⟩
    simp [leadingPrincipalMinor]
  | succ p ih =>
    by_cases hp : p < c.length
    · have hs : c.sizeUpTo (p + 1) = c.sizeUpTo p + c.blocksFun ⟨p, hp⟩ := c.sizeUpTo_succ' ⟨p, hp⟩
      have hle : c.sizeUpTo p + c.blocksFun ⟨p, hp⟩ ≤ d := hs ▸ c.sizeUpTo_le _
      have hf : univ.filter (fun a : Fin c.length => (a : ℕ) < p + 1) =
          insert ⟨p, hp⟩ (univ.filter (fun a : Fin c.length => (a : ℕ) < p)) := by
        ext a
        simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
        omega
      rw [hf, Finset.prod_insert (by simp), ← ih, hs, mul_comm]
      apply gg_step _ _ _ _ hle
      · intro i j hi1 hi2 hj
        have hidx : (c.index i : ℕ) = p := gg_index_eq c i p hi1 (by omega)
        simp only [blockAntidiagonalMatrix]
        rw [if_neg]
        rintro ⟨h, -⟩
        have := c.sizeUpTo_index_le j
        rw [← h, hidx] at this
        omega
      · intro i j hi1 hi2 hj1 hj2
        have hidx : (c.index i : ℕ) = p := gg_index_eq c i p hi1 (by omega)
        have hjdx : (c.index j : ℕ) = p := gg_index_eq c j p hj1 (by omega)
        have hi' : c.index i = ⟨p, hp⟩ := Fin.ext hidx
        have hj' : c.index j = ⟨p, hp⟩ := Fin.ext hjdx
        simp only [blockAntidiagonalMatrix, hi', hj', true_and]
        congr 1
        exact propext ⟨fun h => by omega, fun h => by omega⟩
    · have hp' : c.length ≤ p := not_lt.mp hp
      have he : c.sizeUpTo (p + 1) = c.sizeUpTo p := by
        rw [c.sizeUpTo_ofLength_le (p + 1) (by omega), c.sizeUpTo_ofLength_le p hp']
      rw [he, ih]
      apply Finset.prod_congr _ (fun _ _ => rfl)
      ext a
      have := a.2
      simp only [mem_filter, mem_univ, true_and]
      omega

end GG
end Formalism.HermitianLatticeCounting.P

namespace Formalism.HermitianLatticeCounting.P
section GF
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset Matrix

/- English proof (translation)
Unfold `IsLowerUnitriangular at hl`. Use extensionality with `a c`. Simplify using `only [Matrix.submatrix_apply, Matrix.mul_apply]`. Establish `e1` using `Finset.sum_image (s := Finset.univ) (g := ρ) (f := fun x => l (ρ a) x * M x (κ c)) (fun b _ b' _ h => hinj h)`. Rewrite using `[← e1]`.

Use `(Finset.sum_subset (Finset.subset_univ _) fun x _ hx => ?_).symm` and prove the remaining obligations. Establish `hlt : ρ a < x`. Assume the negation of the conclusion as `hle`. Use `push_neg at hle`. Take `⟨b, hb⟩` from `hdown a x hle`.

Conclude with `hx (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, hb⟩)`. Rewrite using `[hl.2 _ _ hlt, zero_mul]`.
-/
lemma gf_lower_sub {R : Type*} [CommRing R] {d : ℕ} {α β β' : Type*} [Fintype α] (ρ : α → Fin d)
    (hinj : Function.Injective ρ) (hdown : ∀ a x, x ≤ ρ a → ∃ b, ρ b = x)
    (l : Matrix (Fin d) (Fin d) R) (hl : IsLowerUnitriangular l) (M : Matrix (Fin d) β R) (κ : β' → β) :
    (l * M).submatrix ρ κ = l.submatrix ρ ρ * M.submatrix ρ κ := by
  unfold IsLowerUnitriangular at hl
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  have e1 := Finset.sum_image (s := Finset.univ) (g := ρ)
    (f := fun x => l (ρ a) x * M x (κ c)) (fun b _ b' _ h => hinj h)
  rw [← e1]
  refine (Finset.sum_subset (Finset.subset_univ _) fun x _ hx => ?_).symm
  have hlt : ρ a < x := by
    by_contra hle
    push_neg at hle
    obtain ⟨b, hb⟩ := hdown a x hle
    exact hx (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, hb⟩)
  rw [hl.2 _ _ hlt, zero_mul]

/- English proof (translation)
Unfold `IsUpperUnitriangular at hu`. Use extensionality with `c a`. Simplify using `only [Matrix.submatrix_apply, Matrix.mul_apply]`. Establish `e1` using `Finset.sum_image (s := Finset.univ) (g := ρ) (f := fun x => M (κ c) x * u x (ρ a)) (fun b _ b' _ h => hinj h)`. Rewrite using `[← e1]`.

Use `(Finset.sum_subset (Finset.subset_univ _) fun x _ hx => ?_).symm` and prove the remaining obligations. Establish `hlt : ρ a < x`. Assume the negation of the conclusion as `hle`. Use `push_neg at hle`. Take `⟨b, hb⟩` from `hdown a x hle`.

Conclude with `hx (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, hb⟩)`. Rewrite using `[hu.2 _ _ hlt, mul_zero]`.
-/
lemma gf_upper_sub {R : Type*} [CommRing R] {d : ℕ} {α β β' : Type*} [Fintype α] (ρ : α → Fin d)
    (hinj : Function.Injective ρ) (hdown : ∀ a x, x ≤ ρ a → ∃ b, ρ b = x)
    (u : Matrix (Fin d) (Fin d) R) (hu : IsUpperUnitriangular u) (M : Matrix β (Fin d) R) (κ : β' → β) :
    (M * u).submatrix κ ρ = M.submatrix κ ρ * u.submatrix ρ ρ := by
  unfold IsUpperUnitriangular at hu
  ext c a
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  have e1 := Finset.sum_image (s := Finset.univ) (g := ρ)
    (f := fun x => M (κ c) x * u x (ρ a)) (fun b _ b' _ h => hinj h)
  rw [← e1]
  refine (Finset.sum_subset (Finset.subset_univ _) fun x _ hx => ?_).symm
  have hlt : ρ a < x := by
    by_contra hle
    push_neg at hle
    obtain ⟨b, hb⟩ := hdown a x hle
    exact hx (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, hb⟩)
  rw [hu.2 _ _ hlt, mul_zero]

/- English proof (translation)
Unfold `IsLowerUnitriangular at hl`. Rewrite using `[Matrix.det_of_lowerTriangular (l.submatrix ρ ρ) (fun a b hab => hl.2 _ _ (hmono hab))]`. Simplify using `[Matrix.submatrix_apply, hl.1]`.
-/
lemma gf_lower_det {R : Type*} [CommRing R] {d : ℕ} {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (ρ : α → Fin d) (hmono : StrictMono ρ) (l : Matrix (Fin d) (Fin d) R) (hl : IsLowerUnitriangular l) :
    (l.submatrix ρ ρ).det = 1 := by
  unfold IsLowerUnitriangular at hl
  rw [Matrix.det_of_lowerTriangular (l.submatrix ρ ρ) (fun a b hab => hl.2 _ _ (hmono hab))]
  simp [Matrix.submatrix_apply, hl.1]

/- English proof (translation)
Unfold `IsUpperUnitriangular at hu`. Rewrite using `[Matrix.det_of_upperTriangular (M := u.submatrix ρ ρ) (fun a b hab => hu.2 _ _ (hmono hab))]`. Simplify using `[Matrix.submatrix_apply, hu.1]`.
-/
lemma gf_upper_det {R : Type*} [CommRing R] {d : ℕ} {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (ρ : α → Fin d) (hmono : StrictMono ρ) (u : Matrix (Fin d) (Fin d) R) (hu : IsUpperUnitriangular u) :
    (u.submatrix ρ ρ).det = 1 := by
  unfold IsUpperUnitriangular at hu
  rw [Matrix.det_of_upperTriangular (M := u.submatrix ρ ρ) (fun a b hab => hu.2 _ _ (hmono hab))]
  simp [Matrix.submatrix_apply, hu.1]

/- English proof (translation)
Introduce `R _ d Z l u q hl hu`. Unfold `leadingPrincipalMinor`. Establish `hinj : Function.Injective (fun i : {i : Fin d // (i : ℕ) < q} => i.1)` using `Subtype.val_injective`. Establish `hdown : ∀ (a : {i : Fin d // (i : ℕ) < q}) (x : Fin d), x ≤ a.1 → ∃ b : {i : Fin d // (i : ℕ) < q}, b.1 = x` using `fun a x hx => ⟨⟨x, Nat.lt_of_le_of_lt hx a.2⟩, rfl⟩`. Establish `hmono : StrictMono (fun i : {i : Fin d // (i : ℕ) < q} => i.1)` using `fun a b h => h`.

Rewrite using `[gf_upper_sub _ hinj hdown u hu (l * Z) _, gf_lower_sub _ hinj hdown l hl Z _, Matrix.det_mul, Matrix.det_mul, gf_lower_det _ hmono l hl, gf_upper_det _ hmono u hu, one_mul, mul_one]`.
-/
theorem invariant_value_holds : Formalism.HermitianLatticeCounting.ExpansionTerms.LeadingMinorUnipotentInvariant := by
  intro R _ d Z l u q hl hu
  unfold leadingPrincipalMinor
  have hinj : Function.Injective (fun i : {i : Fin d // (i : ℕ) < q} => i.1) := Subtype.val_injective
  have hdown : ∀ (a : {i : Fin d // (i : ℕ) < q}) (x : Fin d), x ≤ a.1 →
      ∃ b : {i : Fin d // (i : ℕ) < q}, b.1 = x :=
    fun a x hx => ⟨⟨x, Nat.lt_of_le_of_lt hx a.2⟩, rfl⟩
  have hmono : StrictMono (fun i : {i : Fin d // (i : ℕ) < q} => i.1) := fun a b h => h
  rw [gf_upper_sub _ hinj hdown u hu (l * Z) _, gf_lower_sub _ hinj hdown l hl Z _, Matrix.det_mul,
    Matrix.det_mul, gf_lower_det _ hmono l hl, gf_upper_det _ hmono u hu, one_mul, mul_one]

/- English proof (translation)
Unfold `leadingPrincipalMinor`. Set `e : Fin q ≃ {i : Fin d // (i : ℕ) < q}` to `{ toFun := fun k => ⟨Fin.castLE h k, k.2⟩ invFun := fun i => ⟨i.1, i.2⟩ left_inv := fun k => Fin.ext rfl right_inv := fun i => Subtype.ext (Fin.ext rfl) }`. Conclude with `(Matrix.det_submatrix_equiv_self e _).symm`.
-/
lemma gf_lead_eq {R : Type*} [CommRing R] {d : ℕ} (Z : Matrix (Fin d) (Fin d) R) (q : ℕ) (h : q ≤ d) :
    leadingPrincipalMinor Z q = (Z.submatrix (Fin.castLE h) (Fin.castLE h)).det := by
  unfold leadingPrincipalMinor
  let e : Fin q ≃ {i : Fin d // (i : ℕ) < q} :=
    { toFun := fun k => ⟨Fin.castLE h k, k.2⟩
      invFun := fun i => ⟨i.1, i.2⟩
      left_inv := fun k => Fin.ext rfl
      right_inv := fun i => Subtype.ext (Fin.ext rfl) }
  exact (Matrix.det_submatrix_equiv_self e _).symm

/- English proof (translation)
Unfold `IsLowerUnitriangular`. Conclude with `⟨fun i => Matrix.one_apply_eq i, fun i j h => Matrix.one_apply_ne (ne_of_lt h)⟩`.
-/
lemma gf_one_lower {R : Type*} [CommRing R] {d : ℕ} : IsLowerUnitriangular (1 : Matrix (Fin d) (Fin d) R) := by
  unfold IsLowerUnitriangular
  exact ⟨fun i => Matrix.one_apply_eq i, fun i j h => Matrix.one_apply_ne (ne_of_lt h)⟩

/- English proof (translation)
Introduce `R _ d c t l u hl hu i j' hi hj'`. Establish `hid : (i : ℕ) + 1 ≤ d` using `Nat.succ_le_of_lt i.isLt`. Take `⟨ρ, hρ⟩ : ∃ ρ : Fin ((i : ℕ) + 1) → Fin d, ρ = fun a => Fin.castLE hid a` from `⟨_, rfl⟩`. Take `⟨κ, hκ⟩ : ∃ κ : Fin ((i : ℕ) + 1) → Fin d, κ = fun b : Fin ((i : ℕ) + 1) => if (b : ℕ) < (i : ℕ) then Fin.castLE hid b else j'` from `⟨_, rfl⟩`. Establish `hmono : StrictMono ρ` using `by subst hρ; exact fun a b h => h`.

Establish `hdown : ∀ a x, x ≤ ρ a → ∃ b, ρ b = x`. Substitute `hρ` using the available equality. Conclude with `fun a x hx => ⟨⟨x.1, lt_of_le_of_lt hx a.2⟩, rfl⟩`. Establish `key : mixedMinor (l * blockAntidiagonalMatrix c t * u) i j' = ((blockAntidiagonalMatrix c t * u).submatrix ρ κ).det`. Establish `h0 : mixedMinor (l * blockAntidiagonalMatrix c t * u) i j' = ((l * (blockAntidiagonalMatrix c t * u)).submatrix ρ κ).det`.

Substitute `hρ hκ` using the available equality. Rewrite using `[← Matrix.mul_assoc]`. Both sides reduce to the same expression. Rewrite using `[h0, gf_lower_sub ρ hmono.injective hdown l hl, Matrix.det_mul, gf_lower_det ρ hmono l hl, one_mul]`. Establish `hend : (i : ℕ) < c.sizeUpTo ((c.index i : ℕ) + 1)` using `c.lt_sizeUpTo_index_succ i`.

Establish `hrow : ∀ y : Fin d, (y : ℕ) + 1 < c.sizeUpTo ((c.index i : ℕ) + 1) → (blockAntidiagonalMatrix c t * u) i y = 0`. Introduce `y hy`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero (fun x _ => ?_)` and prove the remaining obligations. Unfold `blockAntidiagonalMatrix`.

Use `split_ifs with h`. Establish `h1 : y < x`. Rewrite using `[Fin.lt_def]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hu.2 _ _ h1, mul_zero]`.

Rewrite using `[zero_mul]`. Establish `hlast : ρ (Fin.last (i : ℕ)) = i` using `by subst hρ; exact Fin.ext rfl`. Establish `hκlt : ∀ b : Fin ((i : ℕ) + 1), (b : ℕ) < (i : ℕ) → ((κ b : Fin d) : ℕ) = (b : ℕ)`. Introduce `b hb`. Substitute `hκ` using the available equality.

Simplify using `[hb]`. Establish `hκlast : κ (Fin.last (i : ℕ)) = j'` using `by subst hκ; simp`. Establish `hrow0 : ∀ b : Fin ((i : ℕ) + 1), b ≠ Fin.last (i : ℕ) → ((blockAntidiagonalMatrix c t * u).submatrix ρ κ) (Fin.last (i : ℕ)) b = 0`. Introduce `b hb`. Establish `hb' : (b : ℕ) < (i : ℕ)` using `Fin.val_lt_last hb`.

Rewrite using `[Matrix.submatrix_apply, hlast]`. Apply `hrow` to reduce the goal to its premises. Rewrite using `[hκlt b hb']`. Use linear arithmetic over natural numbers and integers. Prove the components needed by the constructor for the conclusion.

Introduce `hj`. Rewrite using `[key]`. Apply `Matrix.det_eq_zero_of_row_eq_zero (Fin.last (i : ℕ))` to reduce the goal to its premises. Introduce `b`. Distinguish the cases in `hb : b = Fin.last (i : ℕ)`.

Rewrite using `[hb, Matrix.submatrix_apply, hlast, hκlast]`. Conclude with `hrow j' hj`. Conclude with `hrow0 b hb`. Introduce `hj`. Rewrite using `[key, Matrix.det_succ_row _ (Fin.last (i : ℕ)), Finset.sum_eq_single (Fin.last (i : ℕ))]`.

Establish `h1 : ((blockAntidiagonalMatrix c t * u).submatrix ρ κ) (Fin.last (i : ℕ)) (Fin.last (i : ℕ)) = t (c.index i)`. Rewrite using `[Matrix.submatrix_apply, hlast, hκlast, Matrix.mul_apply, Finset.sum_eq_single j']`. Rewrite using `[hu.1, mul_one]`. Unfold `blockAntidiagonalMatrix`. Rewrite using `[if_pos]`.

Conclude with `⟨hj'.symm, by omega⟩`. Introduce `x _ hx`. Unfold `blockAntidiagonalMatrix`. Rewrite using `[if_neg, zero_mul]`. Introduce and unpack `⟨_, h2⟩`.

Apply `hx` to reduce the goal to its premises. Apply `Fin.ext` to reduce the goal to its premises. Use linear arithmetic over natural numbers and integers. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.

Establish `h2 : ((blockAntidiagonalMatrix c t * u).submatrix ρ κ).submatrix (Fin.last (i : ℕ)).succAbove (Fin.last (i : ℕ)).succAbove = (blockAntidiagonalMatrix c t * u).submatrix (Fin.castLE (le_of_lt i.isLt)) (Fin.castLE (le_of_lt i.isLt))`. Use extensionality with `a b`. Simplify using `only [Matrix.submatrix_apply, Fin.succAbove_last]`. Establish `ha : ρ a.castSucc = Fin.castLE (le_of_lt i.isLt) a` using `by subst hρ; exact Fin.ext rfl`. Establish `hb : κ b.castSucc = Fin.castLE (le_of_lt i.isLt) b`.

Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[hκlt _ (by simp)]`. Both sides reduce to the same expression. Rewrite using `[ha, hb]`. Establish `h3 : leadingPrincipalMinor (blockAntidiagonalMatrix c t * u) (i : ℕ) = leadingPrincipalMinor (blockAntidiagonalMatrix c t) (i : ℕ)`.

Use `invariant_value_holds R d (blockAntidiagonalMatrix c t) 1 u (i : ℕ) gf_one_lower hu` as an intermediate fact. Rewrite `this` using `[Matrix.one_mul]`. Then use the resulting hypothesis. Rewrite using `[h1, h2, ← gf_lead_eq, h3]`. Establish `h4 : ((-1 : R)) ^ (((Fin.last (i : ℕ) : Fin ((i : ℕ) + 1)) : ℕ) + ((Fin.last (i : ℕ) : Fin ((i : ℕ) + 1)) : ℕ)) = 1` using `Even.neg_one_pow ⟨_, rfl⟩`. Rewrite using `[h4, one_mul, mul_comm]`.

Introduce `b _ hb`. Rewrite using `[hrow0 b hb, mul_zero, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem mixed_minor_vanishing : Formalism.HermitianLatticeCounting.ExpansionTerms.MixedMinorVanishing := by
  intro R _ d c t l u hl hu i j' hi hj'
  have hid : (i : ℕ) + 1 ≤ d := Nat.succ_le_of_lt i.isLt
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Fin ((i : ℕ) + 1) → Fin d, ρ = fun a => Fin.castLE hid a := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : Fin ((i : ℕ) + 1) → Fin d,
      κ = fun b : Fin ((i : ℕ) + 1) => if (b : ℕ) < (i : ℕ) then Fin.castLE hid b else j' := ⟨_, rfl⟩
  have hmono : StrictMono ρ := by subst hρ; exact fun a b h => h
  have hdown : ∀ a x, x ≤ ρ a → ∃ b, ρ b = x := by
    subst hρ
    exact fun a x hx => ⟨⟨x.1, lt_of_le_of_lt hx a.2⟩, rfl⟩
  have key : mixedMinor (l * blockAntidiagonalMatrix c t * u) i j' = ((blockAntidiagonalMatrix c t * u).submatrix ρ κ).det := by
    have h0 : mixedMinor (l * blockAntidiagonalMatrix c t * u) i j' = ((l * (blockAntidiagonalMatrix c t * u)).submatrix ρ κ).det := by
      subst hρ hκ
      rw [← Matrix.mul_assoc]
      rfl
    rw [h0, gf_lower_sub ρ hmono.injective hdown l hl, Matrix.det_mul, gf_lower_det ρ hmono l hl,
      one_mul]
  have hend : (i : ℕ) < c.sizeUpTo ((c.index i : ℕ) + 1) := c.lt_sizeUpTo_index_succ i
  have hrow : ∀ y : Fin d, (y : ℕ) + 1 < c.sizeUpTo ((c.index i : ℕ) + 1) →
      (blockAntidiagonalMatrix c t * u) i y = 0 := by
    intro y hy
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero (fun x _ => ?_)
    unfold blockAntidiagonalMatrix
    split_ifs with h
    · have h1 : y < x := by
        rw [Fin.lt_def]; omega
      rw [hu.2 _ _ h1, mul_zero]
    · rw [zero_mul]
  have hlast : ρ (Fin.last (i : ℕ)) = i := by subst hρ; exact Fin.ext rfl
  have hκlt : ∀ b : Fin ((i : ℕ) + 1), (b : ℕ) < (i : ℕ) → ((κ b : Fin d) : ℕ) = (b : ℕ) := by
    intro b hb; subst hκ; simp [hb]
  have hκlast : κ (Fin.last (i : ℕ)) = j' := by subst hκ; simp
  have hrow0 : ∀ b : Fin ((i : ℕ) + 1), b ≠ Fin.last (i : ℕ) →
      ((blockAntidiagonalMatrix c t * u).submatrix ρ κ) (Fin.last (i : ℕ)) b = 0 := by
    intro b hb
    have hb' : (b : ℕ) < (i : ℕ) := Fin.val_lt_last hb
    rw [Matrix.submatrix_apply, hlast]
    apply hrow
    rw [hκlt b hb']; omega
  constructor
  · intro hj
    rw [key]
    apply Matrix.det_eq_zero_of_row_eq_zero (Fin.last (i : ℕ))
    intro b
    by_cases hb : b = Fin.last (i : ℕ)
    · rw [hb, Matrix.submatrix_apply, hlast, hκlast]
      exact hrow j' hj
    · exact hrow0 b hb
  · intro hj
    rw [key, Matrix.det_succ_row _ (Fin.last (i : ℕ)), Finset.sum_eq_single (Fin.last (i : ℕ))]
    · have h1 : ((blockAntidiagonalMatrix c t * u).submatrix ρ κ) (Fin.last (i : ℕ)) (Fin.last (i : ℕ)) =
          t (c.index i) := by
        rw [Matrix.submatrix_apply, hlast, hκlast, Matrix.mul_apply, Finset.sum_eq_single j']
        · rw [hu.1, mul_one]
          unfold blockAntidiagonalMatrix
          rw [if_pos]
          exact ⟨hj'.symm, by omega⟩
        · intro x _ hx
          unfold blockAntidiagonalMatrix
          rw [if_neg, zero_mul]
          rintro ⟨_, h2⟩
          apply hx
          apply Fin.ext
          omega
        · intro h; exact absurd (Finset.mem_univ _) h
      have h2 : ((blockAntidiagonalMatrix c t * u).submatrix ρ κ).submatrix (Fin.last (i : ℕ)).succAbove
          (Fin.last (i : ℕ)).succAbove =
          (blockAntidiagonalMatrix c t * u).submatrix (Fin.castLE (le_of_lt i.isLt)) (Fin.castLE (le_of_lt i.isLt)) := by
        ext a b
        simp only [Matrix.submatrix_apply, Fin.succAbove_last]
        have ha : ρ a.castSucc = Fin.castLE (le_of_lt i.isLt) a := by subst hρ; exact Fin.ext rfl
        have hb : κ b.castSucc = Fin.castLE (le_of_lt i.isLt) b := by
          apply Fin.ext
          rw [hκlt _ (by simp)]
          rfl
        rw [ha, hb]
      have h3 : leadingPrincipalMinor (blockAntidiagonalMatrix c t * u) (i : ℕ) = leadingPrincipalMinor (blockAntidiagonalMatrix c t) (i : ℕ) := by
        have := invariant_value_holds R d (blockAntidiagonalMatrix c t) 1 u (i : ℕ) gf_one_lower hu
        rwa [Matrix.one_mul] at this
      rw [h1, h2, ← gf_lead_eq, h3]
      have h4 : ((-1 : R)) ^ (((Fin.last (i : ℕ) : Fin ((i : ℕ) + 1)) : ℕ) +
          ((Fin.last (i : ℕ) : Fin ((i : ℕ) + 1)) : ℕ)) = 1 := Even.neg_one_pow ⟨_, rfl⟩
      rw [h4, one_mul, mul_comm]
    · intro b _ hb
      rw [hrow0 b hb, mul_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Set `B : Matrix n n O` to `fun i j => ⟨A i j, h i j⟩`. Establish `hB : A = B.map O.subtype` using `by ext i j; rfl`. Establish `e` using `RingHom.map_det O.subtype B`. Rewrite `e` using `[RingHom.mapMatrix_apply]`. Rewrite using `[hB, ← e]`.

Conclude with `(B.det).2`.
-/
lemma gf_det_mem {K : Type*} [Field K] (O : Subring K) {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (h : ∀ i j, A i j ∈ O) : A.det ∈ O := by
  let B : Matrix n n O := fun i j => ⟨A i j, h i j⟩
  have hB : A = B.map O.subtype := by ext i j; rfl
  have e := RingHom.map_det O.subtype B
  rw [RingHom.mapMatrix_apply] at e
  rw [hB, ← e]
  exact (B.det).2

/- English proof (translation)
Introduce `K _ O d c t ht l u hl hu hO`. Establish `hmem : ∀ q, leadingPrincipalMinor (blockAntidiagonalMatrix c t) q ∈ O`. Introduce `q`. Rewrite using `[← invariant_value_holds K d (blockAntidiagonalMatrix c t) l u q hl hu]`. Unfold `leadingPrincipalMinor`.

Conclude with `gf_det_mem O _ fun i j => hO _ _`. Establish `hne : ∀ p, leadingPrincipalMinor (blockAntidiagonalMatrix c t) (c.sizeUpTo p) ≠ 0`. Introduce `p`. Rewrite using `[hV K d c t p]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun x _ => mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (pow_ne_zero _ (ht x))`.

Use `⟨fun p => ⟨hmem _, hne p⟩, fun a => ?_⟩` and prove the remaining obligations. Establish `hlt : c.sizeUpTo (a : ℕ) < c.sizeUpTo ((a : ℕ) + 1)` using `c.sizeUpTo_strict_mono a.2`. Establish `hle : c.sizeUpTo ((a : ℕ) + 1) ≤ d` using `c.sizeUpTo_le _`. Set `i : Fin d` to `⟨c.sizeUpTo (a : ℕ), by omega⟩`. Set `j' : Fin d` to `⟨c.sizeUpTo ((a : ℕ) + 1) - 1, by omega⟩`.

Establish `hi : (c.index i : ℕ) = a` using `gg_index_eq c i a le_rfl hlt`. Establish `hj : (c.index j' : ℕ) = a` using `gg_index_eq c j' a (show c.sizeUpTo (a : ℕ) ≤ c.sizeUpTo ((a : ℕ) + 1) - 1 by omega) (show c.sizeUpTo ((a : ℕ) + 1) - 1 < c.sizeUpTo ((a : ℕ) + 1) by omega)`. Establish `hia : c.index i = a` using `Fin.ext hi`. Establish `hja : c.index j' = c.index i` using `Fin.ext (hj.trans hi.symm)`. Establish `hmix` using `(mixed_minor_vanishing K d c t l u hl hu i j' (by rw [hi]) hja).2 (show c.sizeUpTo ((a : ℕ) + 1) - 1 + 1 = c.sizeUpTo ((c.index i : ℕ) + 1) by rw [hi]; omega)`.

Rewrite `hmix` using `[hia]`. Establish `e : leadingPrincipalMinor (blockAntidiagonalMatrix c t) (c.sizeUpTo (a : ℕ)) * t a = mixedMinor (l * blockAntidiagonalMatrix c t * u) i j'` using `hmix.symm`. Rewrite using `[e]`. Unfold `mixedMinor`. Conclude with `gf_det_mem O _ fun x y => hO _ _`.
-/
theorem orbit_integral_entries_of_leading_minor_at_block_end (hV : Formalism.HermitianLatticeCounting.ExpansionTerms.LeadingMinorAtBlockEnd) : Formalism.HermitianLatticeCounting.ExpansionTerms.OrbitIntegralEntries := by
  intro K _ O d c t ht l u hl hu hO
  have hmem : ∀ q, leadingPrincipalMinor (blockAntidiagonalMatrix c t) q ∈ O := by
    intro q
    rw [← invariant_value_holds K d (blockAntidiagonalMatrix c t) l u q hl hu]
    unfold leadingPrincipalMinor
    exact gf_det_mem O _ fun i j => hO _ _
  have hne : ∀ p, leadingPrincipalMinor (blockAntidiagonalMatrix c t) (c.sizeUpTo p) ≠ 0 := by
    intro p
    rw [hV K d c t p]
    exact Finset.prod_ne_zero_iff.mpr fun x _ =>
      mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (pow_ne_zero _ (ht x))
  refine ⟨fun p => ⟨hmem _, hne p⟩, fun a => ?_⟩
  have hlt : c.sizeUpTo (a : ℕ) < c.sizeUpTo ((a : ℕ) + 1) := c.sizeUpTo_strict_mono a.2
  have hle : c.sizeUpTo ((a : ℕ) + 1) ≤ d := c.sizeUpTo_le _
  let i : Fin d := ⟨c.sizeUpTo (a : ℕ), by omega⟩
  let j' : Fin d := ⟨c.sizeUpTo ((a : ℕ) + 1) - 1, by omega⟩
  have hi : (c.index i : ℕ) = a := gg_index_eq c i a le_rfl hlt
  have hj : (c.index j' : ℕ) = a := gg_index_eq c j' a
    (show c.sizeUpTo (a : ℕ) ≤ c.sizeUpTo ((a : ℕ) + 1) - 1 by omega)
    (show c.sizeUpTo ((a : ℕ) + 1) - 1 < c.sizeUpTo ((a : ℕ) + 1) by omega)
  have hia : c.index i = a := Fin.ext hi
  have hja : c.index j' = c.index i := Fin.ext (hj.trans hi.symm)
  have hmix := (mixed_minor_vanishing K d c t l u hl hu i j' (by rw [hi]) hja).2
    (show c.sizeUpTo ((a : ℕ) + 1) - 1 + 1 = c.sizeUpTo ((c.index i : ℕ) + 1) by rw [hi]; omega)
  rw [hia] at hmix
  have e : leadingPrincipalMinor (blockAntidiagonalMatrix c t) (c.sizeUpTo (a : ℕ)) * t a = mixedMinor (l * blockAntidiagonalMatrix c t * u) i j' := hmix.symm
  rw [e]
  unfold mixedMinor
  exact gf_det_mem O _ fun x y => hO _ _

end GF
end Formalism.HermitianLatticeCounting.P

namespace Formalism.HermitianLatticeCounting.P
section GH
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset Matrix

def gh_G {n β K : Type*} [DecidableEq n] [Zero K] (b : n → β) (σ : n → n) (t : β → K) : Matrix n n K :=
  fun i j => if j = σ i then t (b i) else 0

section abs
variable {n β K : Type*} [Fintype n] [DecidableEq n] [LinearOrder n] [LinearOrder β] [Field K]
  {b : n → β} {σ : n → n}

omit [LinearOrder β] in
/- English proof (translation)
Rewrite using `[Matrix.det_of_upperTriangular (fun i j hij => h2 i j hij)]`. Simplify using `[h1]`.
-/
lemma gh_det_upper {u : Matrix n n K} (h1 : ∀ i, u i i = 1) (h2 : ∀ i j, j < i → u i j = 0) :
    u.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => h2 i j hij)]
  simp [h1]

end abs

/- English proof (translation)
The claim follows from `c.lt_sizeUpTo_index_succ j`.
-/
lemma gh_lt {d : ℕ} (c : Composition d) (j : Fin d) :
    (j : ℕ) < c.sizeUpTo ((c.index j : ℕ) + 1) := c.lt_sizeUpTo_index_succ j

def gh_sig {d : ℕ} (c : Composition d) (i : Fin d) : Fin d :=
  ⟨c.sizeUpTo (c.index i : ℕ) + c.sizeUpTo ((c.index i : ℕ) + 1) - 1 - (i : ℕ), by
    have a1 := gh_lt c i
    have a2 := c.sizeUpTo_index_le i
    have a3 := c.sizeUpTo_le ((c.index i : ℕ) + 1)
    omega⟩

end GH
end Formalism.HermitianLatticeCounting.P

namespace Formalism.HermitianLatticeCounting.P

section GI
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset Matrix
open scoped ComplexConjugate

/- English proof (translation)
Unfold `leadingPrincipalMinor`. Set `e : Fin r ≃ {i : Fin (r + 1) // (i : ℕ) < r}` to `{ toFun := fun k => ⟨Fin.castSucc k, k.2⟩ invFun := fun i => ⟨i.1, i.2⟩ left_inv := fun k => Fin.ext rfl right_inv := fun i => Subtype.ext (Fin.ext rfl) }`. Conclude with `(Matrix.det_submatrix_equiv_self e _).symm`.
-/
lemma gi_lead_eq {R : Type*} [CommRing R] (r : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R) :
    leadingPrincipalMinor Z r = (Z.submatrix Fin.castSucc Fin.castSucc).det := by
  unfold leadingPrincipalMinor
  let e : Fin r ≃ {i : Fin (r + 1) // (i : ℕ) < r} :=
    { toFun := fun k => ⟨Fin.castSucc k, k.2⟩
      invFun := fun i => ⟨i.1, i.2⟩
      left_inv := fun k => Fin.ext rfl
      right_inv := fun i => Subtype.ext (Fin.ext rfl) }
  exact (Matrix.det_submatrix_equiv_self e _).symm

/- English proof (translation)
Rewrite using `[gi_lead_eq, Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last, Fin.val_last, Even.neg_one_pow ⟨r, rfl⟩, one_mul]`.
-/
lemma gi_adj_last {R : Type*} [CommRing R] (r : ℕ) (M : Matrix (Fin (r + 1)) (Fin (r + 1)) R) :
    M.adjugate (Fin.last r) (Fin.last r) = leadingPrincipalMinor M r := by
  rw [gi_lead_eq, Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last, Fin.val_last,
    Even.neg_one_pow ⟨r, rfl⟩, one_mul]

/- English proof (translation)
Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[map_sum, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[map_smulₛₗ, map_smul, LinearMap.smul_apply]`.

Simplify using `only [smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma gi_sesq_sum {V ι : Type*} [AddCommGroup V] [Module ℂ V] [Fintype ι] (h : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (c : ι → ℂ) (y : ι → V) :
    h (∑ a, c a • y a) (∑ b, c b • y b) = ∑ b, ∑ a, c a * conj (c b) * h (y a) (y b) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smulₛₗ, map_smul, LinearMap.smul_apply]
  simp only [smul_eq_mul]
  ring

/- English proof (translation)
Introduce `V _ _ h hh r y f' T T' hT' hy hf x0 om al hx0 hom hx`. Use `set M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Matrix.of fun a b => h (y a) (f' b) with hM`. Use `set L := Fin.last r with hL`. Establish `hA : ∀ x ∈ Submodule.span ℂ (f' '' {b | b ≠ L}), ∀ b, h x (f' b) = 0`. Introduce `x hx b`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨c, hc, rfl⟩` from `hx`. Rewrite using `[hf, if_neg (fun hh => hc hh.1)]`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => simp [hx, hy]`. Consider the case `smul a x _ hx => simp [hx]`. Establish `hB : ∀ u : V, (∀ b, h u (f' b) = 0) → ∀ x ∈ Submodule.span ℂ (f' '' {b | b ≠ L}), h u x = 0`. Introduce `u hu x hx`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨c, _, rfl⟩` from `hx`. Conclude with `hu c`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => simp [hx, hy]`.

Consider the case `smul a x _ hx => simp [hx]`. Establish `e00 : h x0 x0 = 0` using `hB x0 (hA x0 hx0) x0 hx0`. Establish `e0f : h x0 (f' L) = 0` using `hA x0 hx0 L`. Establish `ef0 : h (f' L) x0 = 0` using `by rw [hh, e0f, map_zero]`. Establish `eo0 : h om x0 = 0` using `hB om hom x0 hx0`.

Establish `e0o : h x0 om = 0` using `by rw [hh, eo0, map_zero]`. Establish `eof : h om (f' L) = 0` using `hom L`. Establish `efo : h (f' L) om = 0` using `by rw [hh, eof, map_zero]`. Establish `eff : h (f' L) (f' L) = -(T' : ℂ)` using `by rw [hf, if_pos ⟨rfl, rfl⟩]`. Use `set x' : V := ∑ a, M.adjugate L a • y a with hx'`.

Establish `p1 : h x' (f' L) = M.det`. Establish `: h x' (f' L) = (M.adjugate * M) L L`. Rewrite using `[hx', Matrix.mul_apply, map_sum, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, LinearMap.smul_apply, smul_eq_mul]`.

Both sides reduce to the same expression. Rewrite using `[this, Matrix.adjugate_mul]`. Simplify using the standard rewrite rules. Establish `p2 : h x' (f' L) = al * -(T' : ℂ)`. Rewrite using `[hx]`.

Simplify using `[e0f, eof, eff]`. Establish `n1 : h x' x' = M.adjugate L L * conj (M.adjugate L L) * -(T : ℂ)`. Rewrite using `[hx', gi_sesq_sum, Finset.sum_eq_single L, Finset.sum_eq_single L]`. Rewrite using `[hy, if_pos ⟨rfl, rfl⟩]`. Introduce `a _ ha`.

Rewrite using `[hy, if_neg (fun hh => ha hh.1), mul_zero]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations. Rewrite using `[hy, if_neg (fun hh => hb hh.2), mul_zero]`.

Simplify using the standard rewrite rules. Establish `n2 : h x' x' = al * conj al * -(T' : ℂ) + h om om`. Rewrite using `[hx]`. Simplify using `only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, map_smulₛₗ, e00, e0f, ef0, eo0, e0o, eof, efo, eff, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hT'c : (T' : ℂ) ≠ 0` using `by exact_mod_cast hT'`. Establish `hal : al = - M.det / (T' : ℂ)`. Clear the denominators using the available nonvanishing facts. Take the linear combination `p2 - p1`. Rewrite `n1` using `[gi_adj_last]`.

Establish `hcT : conj (T' : ℂ) = (T' : ℂ)` using `Complex.conj_ofReal T'`. Rewrite using `[Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]`. Establish `key : h om om = leadingPrincipalMinor M r * conj (leadingPrincipalMinor M r) * -(T : ℂ) - al * conj al * -(T' : ℂ)`. Take the linear combination `n1 - n2`. Rewrite using `[key, hal]`.

Simplify using `only [map_div₀, map_neg, hcT]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dual_vector_norm_sq : Formalism.HermitianLatticeCounting.ExpansionTerms.DualVectorNormSq := by
  intro V _ _ h hh r y f' T T' hT' hy hf x0 om al hx0 hom hx
  set M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Matrix.of fun a b => h (y a) (f' b) with hM
  set L := Fin.last r with hL

  have hA : ∀ x ∈ Submodule.span ℂ (f' '' {b | b ≠ L}), ∀ b, h x (f' b) = 0 := by
    intro x hx b
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      rw [hf, if_neg (fun hh => hc hh.1)]
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [hx]
  have hB : ∀ u : V, (∀ b, h u (f' b) = 0) → ∀ x ∈ Submodule.span ℂ (f' '' {b | b ≠ L}), h u x = 0 := by
    intro u hu x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, _, rfl⟩ := hx
      exact hu c
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [hx]
  have e00 : h x0 x0 = 0 := hB x0 (hA x0 hx0) x0 hx0
  have e0f : h x0 (f' L) = 0 := hA x0 hx0 L
  have ef0 : h (f' L) x0 = 0 := by rw [hh, e0f, map_zero]
  have eo0 : h om x0 = 0 := hB om hom x0 hx0
  have e0o : h x0 om = 0 := by rw [hh, eo0, map_zero]
  have eof : h om (f' L) = 0 := hom L
  have efo : h (f' L) om = 0 := by rw [hh, eof, map_zero]
  have eff : h (f' L) (f' L) = -(T' : ℂ) := by rw [hf, if_pos ⟨rfl, rfl⟩]
  set x' : V := ∑ a, M.adjugate L a • y a with hx'

  have p1 : h x' (f' L) = M.det := by
    have : h x' (f' L) = (M.adjugate * M) L L := by
      rw [hx', Matrix.mul_apply, map_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
      rfl
    rw [this, Matrix.adjugate_mul]
    simp
  have p2 : h x' (f' L) = al * -(T' : ℂ) := by
    rw [hx]
    simp [e0f, eof, eff]

  have n1 : h x' x' = M.adjugate L L * conj (M.adjugate L L) * -(T : ℂ) := by
    rw [hx', gi_sesq_sum, Finset.sum_eq_single L, Finset.sum_eq_single L]
    · rw [hy, if_pos ⟨rfl, rfl⟩]
    · intro a _ ha
      rw [hy, if_neg (fun hh => ha hh.1), mul_zero]
    · simp
    · intro b _ hb
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [hy, if_neg (fun hh => hb hh.2), mul_zero]
    · simp
  have n2 : h x' x' = al * conj al * -(T' : ℂ) + h om om := by
    rw [hx]
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, map_smulₛₗ, e00, e0f, ef0,
      eo0, e0o, eof, efo, eff, smul_eq_mul]
    ring
  have hT'c : (T' : ℂ) ≠ 0 := by exact_mod_cast hT'
  have hal : al = - M.det / (T' : ℂ) := by
    field_simp
    linear_combination p2 - p1
  rw [gi_adj_last] at n1
  have hcT : conj (T' : ℂ) = (T' : ℂ) := Complex.conj_ofReal T'
  rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
  have key : h om om = leadingPrincipalMinor M r * conj (leadingPrincipalMinor M r) * -(T : ℂ) - al * conj al * -(T' : ℂ) := by
    linear_combination n1 - n2
  rw [key, hal]
  simp only [map_div₀, map_neg, hcT]
  field_simp
  ring

end GI

end Formalism.HermitianLatticeCounting.P

namespace Formalism.HermitianLatticeCounting.P
section GJ
open Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts Matrix Finset

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h b`. Use function extensionality and compare the values at `i`. Establish `e` using `congrFun (congrFun h i) b`. Rewrite `e` using `[Matrix.mul_apply, Matrix.mul_apply]`.

Simplify using `only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[e]`. Conclude with `Finset.sum_congr rfl fun e _ => mul_comm _ _`. Introduce `h`. Use extensionality with `i b`.

Establish `e` using `congrFun (h b) i`. Simplify using `only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at e`. Rewrite using `[Matrix.mul_apply, Matrix.mul_apply, e]`. Conclude with `Finset.sum_congr rfl fun e _ => mul_comm _ _`.
-/
lemma gj_cols {m n : ℕ} (s : Matrix (Fin m) (Fin m) ℂ) (F : Matrix (Fin m) (Fin n) ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ) :
    s * F = F * U ↔ ∀ b, s *ᵥ (fun i => F i b) = ∑ e, U e b • (fun i => F i e) := by
  constructor
  · intro h b
    funext i
    have e := congrFun (congrFun h i) b
    rw [Matrix.mul_apply, Matrix.mul_apply] at e
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [e]
    exact Finset.sum_congr rfl fun e _ => mul_comm _ _
  · intro h
    ext i b
    have e := congrFun (h b) i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at e
    rw [Matrix.mul_apply, Matrix.mul_apply, e]
    exact Finset.sum_congr rfl fun e _ => mul_comm _ _

/- English proof (translation)
Simplify using `only [fvec, dif_pos hc, bvec, eI, Pi.single_apply, Fin.ext_iff, Fin.val_mk]`.
-/
lemma gj_fvec_apply (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin (r + 1)) (hc : c.val < r)
    (i : Fin (2 * r + k + 1)) : fvec k r z c i = if i.val = c.val then 1 else 0 := by
  simp only [fvec, dif_pos hc, bvec, eI, Pi.single_apply, Fin.ext_iff, Fin.val_mk]

def gj_h (k r : ℕ) (p : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := fun i j =>
  if (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k) then p i j else if i = j then 1 else 0

end GJ
end Formalism.HermitianLatticeCounting.P

namespace Formalism.HermitianLatticeCounting.P

section GK
open Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.QuantumDeterminants Matrix

/- English proof (translation)
Simplify using `only [herm, Matrix.mulVec_add, dotProduct_add]`.
-/
lemma gk_herm_add_left {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (u v w : ι → ℂ) :
    herm H (u + v) w = herm H u w + herm H v w := by
  simp only [herm, Matrix.mulVec_add, dotProduct_add]

/- English proof (translation)
Simplify using `only [herm, star_add, add_dotProduct]`.
-/
lemma gk_herm_add_right {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (u v w : ι → ℂ) :
    herm H u (v + w) = herm H u v + herm H u w := by
  simp only [herm, star_add, add_dotProduct]

/- English proof (translation)
Simplify using `only [herm, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]`.
-/
lemma gk_herm_smul_left {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (c : ℂ) (u w : ι → ℂ) :
    herm H (c • u) w = c * herm H u w := by
  simp only [herm, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

/- English proof (translation)
Simplify using `only [herm, star_smul, smul_dotProduct, smul_eq_mul]`.
-/
lemma gk_herm_smul_right {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (c : ℂ) (u w : ι → ℂ) :
    herm H u (c • w) = star c * herm H u w := by
  simp only [herm, star_smul, smul_dotProduct, smul_eq_mul]

noncomputable def gk_Q (k r : ℕ) : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] (Fin (r + 1) → ℂ) :=
  LinearMap.pi fun a =>
    if h : a.val < r then
      LinearMap.proj (R := ℂ) (φ := fun _ : Fin (2 * r + k + 1) => ℂ) (eI k r ⟨a.val, h⟩) -
        LinearMap.proj (R := ℂ) (φ := fun _ : Fin (2 * r + k + 1) => ℂ) (esI k r ⟨a.val, h⟩)
    else LinearMap.proj (R := ℂ) (φ := fun _ : Fin (2 * r + k + 1) => ℂ) ⟨r + k, by omega⟩

noncomputable def gk_E (r : ℕ) : (Option (Fin (r + 1)) → ℂ) →ₗ[ℂ] (Fin (r + 1) ⊕ Fin (r + 1) → ℂ) :=
  LinearMap.pi fun i =>
    Sum.elim (fun a => LinearMap.proj (R := ℂ) (φ := fun _ : Option (Fin (r + 1)) => ℂ) (some a)) (fun _ => 0) i

end GK

end Formalism.HermitianLatticeCounting.P

namespace Formalism.HermitianLatticeCounting.P

section GD
open Formalism.HermitianLatticeCounting.ExpansionTerms
open Finset Matrix Polynomial
open scoped ComplexConjugate TensorProduct

end GD

end Formalism.HermitianLatticeCounting.P

namespace Formalism.HermitianLatticeCounting.P

section GE
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset Matrix Polynomial
open scoped ComplexConjugate

/- English proof (translation)
Rewrite using `[coeff_det_one_add_X_smul_eq_sum_minors]`. Establish `h` using `Finset.powersetCard_self (Finset.univ : Finset (Fin i))`. Rewrite `h` using `[Finset.card_fin]`. Rewrite using `[h, Finset.sum_singleton]`. Apply the tactic sequence `convert Matrix.det_submatrix_equiv_self (Equiv.subtypeUnivEquiv (fun x => Finset.mem_univ x)) M <;> rfl`.
-/
lemma ge_coeff_top_det {K : Type*} [CommRing K] {i : ℕ} (M : Matrix (Fin i) (Fin i) K) :
    (det (1 + (X : K[X]) • M.map C)).coeff i = M.det := by
  rw [coeff_det_one_add_X_smul_eq_sum_minors]
  have h := Finset.powersetCard_self (Finset.univ : Finset (Fin i))
  rw [Finset.card_fin] at h
  rw [h, Finset.sum_singleton]
  convert Matrix.det_submatrix_equiv_self (Equiv.subtypeUnivEquiv (fun x => Finset.mem_univ x)) M
    <;> rfl

/- English proof (translation)
Rewrite using `[← ge_coeff_top_det (A * B)]`. Establish `h1 : (1 : Matrix (Fin i) (Fin i) K[X]) + (X : K[X]) • (A * B).map C = 1 + ((X : K[X]) • A.map C) * (B.map C)`. Rewrite using `[Matrix.map_mul, Matrix.smul_mul]`. Establish `h2 : (B.map C) * ((X : K[X]) • A.map C) = (X : K[X]) • (B * A).map C`. Rewrite using `[Matrix.mul_smul]`.

Use `congr 1`. Simplify using `[Matrix.map_mul]`. Rewrite using `[h1, det_one_add_mul_comm, h2, coeff_det_one_add_X_smul_eq_sum_minors]`.
-/
lemma ge_det_mul_eq_sum_principal {K : Type*} [CommRing K] {i n : ℕ} (A : Matrix (Fin i) (Fin n) K)
    (B : Matrix (Fin n) (Fin i) K) :
    (A * B).det = ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
      ((B * A).submatrix (Subtype.val : S → Fin n) Subtype.val).det := by
  rw [← ge_coeff_top_det (A * B)]
  have h1 : (1 : Matrix (Fin i) (Fin i) K[X]) + (X : K[X]) • (A * B).map C
      = 1 + ((X : K[X]) • A.map C) * (B.map C) := by
    rw [Matrix.map_mul, Matrix.smul_mul]
  have h2 : (B.map C) * ((X : K[X]) • A.map C) = (X : K[X]) • (B * A).map C := by
    rw [Matrix.mul_smul]; congr 1; simp [Matrix.map_mul]
  rw [h1, det_one_add_mul_comm, h2, coeff_det_one_add_X_smul_eq_sum_minors]

/- English proof (translation)
Rewrite using `[← det_mul, ← Matrix.det_submatrix_equiv_self (S.orderIsoOfFin hS).toEquiv]`. Use `congr 1`.
-/
lemma ge_principal_minor_factor {K : Type*} [CommRing K] {i n : ℕ} (A : Matrix (Fin i) (Fin n) K)
    (B : Matrix (Fin n) (Fin i) K) (S : Finset (Fin n)) (hS : S.card = i) :
    ((B * A).submatrix (Subtype.val : S → Fin n) Subtype.val).det
      = (B.submatrix (S.orderEmbOfFin hS) id).det * (A.submatrix id (S.orderEmbOfFin hS)).det := by
  rw [← det_mul, ← Matrix.det_submatrix_equiv_self (S.orderIsoOfFin hS).toEquiv]
  congr 1

/- English proof (translation)
Rewrite using `[ge_det_mul_eq_sum_principal]`. Rewrite using `[Finset.sum_subtype (p := fun I : Finset (Fin n) => I.card = i) _ (by intro I; simp)]`. Conclude with `Finset.sum_congr rfl fun I _ => ge_principal_minor_factor A B I.1 I.2`.
-/
lemma ge_cauchyBinet {K : Type*} [CommRing K] {i n : ℕ} (A : Matrix (Fin i) (Fin n) K)
    (B : Matrix (Fin n) (Fin i) K) :
    (A * B).det = ∑ I : {I : Finset (Fin n) // I.card = i},
      (B.submatrix (I.1.orderEmbOfFin I.2) id).det * (A.submatrix id (I.1.orderEmbOfFin I.2)).det := by
  rw [ge_det_mul_eq_sum_principal]
  rw [Finset.sum_subtype (p := fun I : Finset (Fin n) => I.card = i) _ (by intro I; simp)]
  exact Finset.sum_congr rfl fun I _ => ge_principal_minor_factor A B I.1 I.2

end GE

end Formalism.HermitianLatticeCounting.P

namespace Formalism.HermitianLatticeCounting.P
section GB
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset
open scoped ComplexConjugate

/- English proof (translation)
Establish `e : ‖θ x‖ ^ 2 = ‖x‖ ^ 2`. Rewrite using `[← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), h.2, h.1]`. Establish `h1` using `norm_nonneg (θ x)`. Establish `h2` using `norm_nonneg x`. Use polynomial arithmetic with `[e]`.
-/
lemma gb_norm_theta {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {θ : V →ₗ[ℂ] V}
    (h : IsSelfAdjointInvolution θ) (x : V) : ‖θ x‖ = ‖x‖ := by
  have e : ‖θ x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), h.2, h.1]
  have h1 := norm_nonneg (θ x)
  have h2 := norm_nonneg x
  nlinarith [e]

/- English proof (translation)
Introduce `V _ _ θ hθ x`. Unfold `majorantHermitianForm`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem gram_majorant_bound : Formalism.HermitianLatticeCounting.ExpansionTerms.MajorantNormBound := by
  intro V _ _ θ hθ x
  unfold majorantHermitianForm
  calc ‖inner ℂ (θ x) x‖ ≤ ‖θ x‖ * ‖x‖ := norm_inner_le_norm _ _
    _ = ‖x‖ ^ 2 := by rw [gb_norm_theta hθ, sq]

/- English proof (translation)
Introduce `V _ _ θ h r y T hG`. Unfold `majorantHermitianForm at hG`. Use `set W : Submodule ℂ V := Submodule.span ℂ (y '' {b | b < Fin.last r}) with hW`. Establish `s1 : ∀ b, ∀ w ∈ W, inner ℂ (θ (y b)) w = 0`. Introduce `b w hw`.

Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨a, ha, rfl⟩` from `hx`. Use `hG a b` as an intermediate fact. Rewrite using `[this, if_neg]`.

Introduce and unpack `⟨h1, -⟩`. Conclude with `(ne_of_lt ha) h1`. Consider the case `zero => simp`. Consider the case `add x z _ _ hx hz => rw [inner_add_right, hx, hz, add_zero]`. Consider the case `smul c x _ hx => rw [inner_smul_right, hx, mul_zero]`.

Establish `s2 : ∀ b, ∀ w ∈ W, inner ℂ (θ w) (y b) = 0`. Introduce `b w hw`. Rewrite using `[h.2, ← inner_conj_symm, s1 b w hw, map_zero]`. Establish `s3 : ∀ w ∈ W, ∀ w' ∈ W, inner ℂ (θ w) w' = 0`. Introduce `w hw w' hw'`.

Proceed by induction on `hw' using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨a, ha, rfl⟩` from `hx`. Conclude with `s2 a w hw`. Consider the case `zero => simp`.

Consider the case `add x z _ _ hx hz => rw [inner_add_right, hx, hz, add_zero]`. Consider the case `smul c x _ hx => rw [inner_smul_right, hx, mul_zero]`. Establish `key : ∀ w ∈ W, T ≤ ‖y (Fin.last r) - w‖ ^ 2`. Introduce `w hw`. Establish `e : inner ℂ (θ (y (Fin.last r) - w)) (y (Fin.last r) - w) = -(T : ℂ)`.

Rewrite using `[map_sub, inner_sub_left, inner_sub_right, inner_sub_right, s1 _ w hw, s2 _ w hw, s3 w hw w hw, hG, if_pos ⟨rfl, rfl⟩]`. Expand and normalize the polynomial expressions, which then agree. Establish `m` using `gram_majorant_bound V θ h (y (Fin.last r) - w)`. Unfold `majorantHermitianForm at m`. Rewrite `m` using `[e, norm_neg, Complex.norm_real, Real.norm_eq_abs]`.

Conclude with `(le_abs_self T).trans m`. Unfold `majorantDistance`. Break down `le_or_gt T 0 with hT | hT` into its components or cases. Conclude with `hT.trans (sq_nonneg _)`. Establish `hne : ((W : Set V)).Nonempty` using `⟨0, W.zero_mem⟩`.

Establish `: √T ≤ Metric.infDist (y (Fin.last r)) (W : Set V)`. Rewrite using `[Metric.le_infDist hne]`. Introduce `w hw`. Rewrite using `[dist_eq_norm]`. Conclude with `Real.sqrt_le_iff.2 ⟨norm_nonneg _, key w hw⟩`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem last_distance_lower_bound : Formalism.HermitianLatticeCounting.ExpansionTerms.LastDistanceLowerBound := by
  intro V _ _ θ h r y T hG
  unfold majorantHermitianForm at hG
  set W : Submodule ℂ V := Submodule.span ℂ (y '' {b | b < Fin.last r}) with hW

  have s1 : ∀ b, ∀ w ∈ W, inner ℂ (θ (y b)) w = 0 := by
    intro b w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      have := hG a b
      rw [this, if_neg]
      rintro ⟨h1, -⟩
      exact (ne_of_lt ha) h1
    | zero => simp
    | add x z _ _ hx hz => rw [inner_add_right, hx, hz, add_zero]
    | smul c x _ hx => rw [inner_smul_right, hx, mul_zero]
  have s2 : ∀ b, ∀ w ∈ W, inner ℂ (θ w) (y b) = 0 := by
    intro b w hw
    rw [h.2, ← inner_conj_symm, s1 b w hw, map_zero]
  have s3 : ∀ w ∈ W, ∀ w' ∈ W, inner ℂ (θ w) w' = 0 := by
    intro w hw w' hw'
    induction hw' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact s2 a w hw
    | zero => simp
    | add x z _ _ hx hz => rw [inner_add_right, hx, hz, add_zero]
    | smul c x _ hx => rw [inner_smul_right, hx, mul_zero]
  have key : ∀ w ∈ W, T ≤ ‖y (Fin.last r) - w‖ ^ 2 := by
    intro w hw
    have e : inner ℂ (θ (y (Fin.last r) - w)) (y (Fin.last r) - w) = -(T : ℂ) := by
      rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right, s1 _ w hw, s2 _ w hw, s3 w hw w hw,
        hG, if_pos ⟨rfl, rfl⟩]
      ring
    have m := gram_majorant_bound V θ h (y (Fin.last r) - w)
    unfold majorantHermitianForm at m
    rw [e, norm_neg, Complex.norm_real, Real.norm_eq_abs] at m
    exact (le_abs_self T).trans m
  unfold majorantDistance
  rcases le_or_gt T 0 with hT | hT
  · exact hT.trans (sq_nonneg _)
  · have hne : ((W : Set V)).Nonempty := ⟨0, W.zero_mem⟩
    have : √T ≤ Metric.infDist (y (Fin.last r)) (W : Set V) := by
      rw [Metric.le_infDist hne]
      intro w hw
      rw [dist_eq_norm]
      exact Real.sqrt_le_iff.2 ⟨norm_nonneg _, key w hw⟩
    calc T = √T ^ 2 := (Real.sq_sqrt hT.le).symm
      _ ≤ _ := by gcongr

/- English proof (translation)
Introduce `V _ _ θ hθ u y1 S hu hS hy1`. Establish `hu0 : ‖u‖ ≠ 0` using `norm_ne_zero_iff.mpr hu`. Establish `hn : (‖u‖ : ℂ) ≠ 0` using `by exact_mod_cast hu0`. Establish `hθv : θ ((Complex.I / (‖u‖ : ℂ)) • θ u) = (Complex.I / (‖u‖ : ℂ)) • u`. Rewrite using `[map_smul, hθ.1]`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[norm_smul, gb_norm_theta hθ, norm_div, Complex.norm_I, Complex.norm_of_nonneg (norm_nonneg u), one_div, inv_mul_cancel₀ hu0]`. Introduce `w hw`. Unfold `majorantHermitianForm`. Rewrite using `[hθv, inner_smul_left, hS w hw, mul_zero]`.

Unfold `majorantHermitianForm`. Rewrite using `[hθv, inner_smul_left, hy1, map_div₀, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_pow]`. Apply the tactic sequence `field_simp <;> ring`.
-/
theorem majorant_phase_estimate_holds : Formalism.HermitianLatticeCounting.ExpansionTerms.MajorantPhaseChoice := by
  intro V _ _ θ hθ u y1 S hu hS hy1
  have hu0 : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hn : (‖u‖ : ℂ) ≠ 0 := by exact_mod_cast hu0
  have hθv : θ ((Complex.I / (‖u‖ : ℂ)) • θ u) = (Complex.I / (‖u‖ : ℂ)) • u := by
    rw [map_smul, hθ.1]
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_smul, gb_norm_theta hθ, norm_div, Complex.norm_I, Complex.norm_of_nonneg (norm_nonneg u),
      one_div, inv_mul_cancel₀ hu0]
  · intro w hw
    unfold majorantHermitianForm
    rw [hθv, inner_smul_left, hS w hw, mul_zero]
  · unfold majorantHermitianForm
    rw [hθv, inner_smul_left, hy1, map_div₀, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_pow]
    field_simp <;> ring

/- English proof (translation)
Introduce `V _ _ θ h n bs e v`. Rewrite using `[Finset.sum_comm]`. Establish `p1 : ∀ b, ∑ a, ‖inner ℂ (bs a) (majorantHermitianForm θ (bs b) v • e - majorantHermitianForm θ (bs b) e • v)‖ ^ 2 ≤ 2 * (‖inner ℂ (θ v) (bs b)‖ ^ 2 * ‖e‖ ^ 2 + ‖inner ℂ (θ e) (bs b)‖ ^ 2 * ‖v‖ ^ 2)`. Introduce `b`. Rewrite using `[bs.sum_sq_norm_inner_right]`.

Unfold `majorantHermitianForm`. Establish `t : ‖inner ℂ (θ v) (bs b) • e - inner ℂ (θ e) (bs b) • v‖ ≤ ‖inner ℂ (θ v) (bs b)‖ * ‖e‖ + ‖inner ℂ (θ e) (bs b)‖ * ‖v‖`. Use `(norm_sub_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[norm_smul, norm_smul]`. Combine the equalities or inequalities in the displayed calculation.

Use polynomial arithmetic with `[sq_nonneg (‖inner ℂ (θ v) (bs b)‖ * ‖e‖ - ‖inner ℂ (θ e) (bs b)‖ * ‖v‖)]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]`. Use `_ = 4 * ‖e‖ ^ 2 * ‖v‖ ^ 2 := by`. Rewrite using `[bs.sum_sq_norm_inner_left, bs.sum_sq_norm_inner_left, gb_norm_theta h, gb_norm_theta h]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem gram_hilbert_schmidt_bound : Formalism.HermitianLatticeCounting.ExpansionTerms.SkewOperatorFrobeniusBound := by
  intro V _ _ θ h n bs e v
  rw [Finset.sum_comm]
  have p1 : ∀ b, ∑ a, ‖inner ℂ (bs a) (majorantHermitianForm θ (bs b) v • e - majorantHermitianForm θ (bs b) e • v)‖ ^ 2 ≤
      2 * (‖inner ℂ (θ v) (bs b)‖ ^ 2 * ‖e‖ ^ 2 + ‖inner ℂ (θ e) (bs b)‖ ^ 2 * ‖v‖ ^ 2) := by
    intro b
    rw [bs.sum_sq_norm_inner_right]
    unfold majorantHermitianForm
    have t : ‖inner ℂ (θ v) (bs b) • e - inner ℂ (θ e) (bs b) • v‖ ≤
        ‖inner ℂ (θ v) (bs b)‖ * ‖e‖ + ‖inner ℂ (θ e) (bs b)‖ * ‖v‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_smul, norm_smul]
    calc ‖inner ℂ (θ v) (bs b) • e - inner ℂ (θ e) (bs b) • v‖ ^ 2
        ≤ (‖inner ℂ (θ v) (bs b)‖ * ‖e‖ + ‖inner ℂ (θ e) (bs b)‖ * ‖v‖) ^ 2 := by gcongr
      _ ≤ _ := by
        nlinarith [sq_nonneg (‖inner ℂ (θ v) (bs b)‖ * ‖e‖ - ‖inner ℂ (θ e) (bs b)‖ * ‖v‖)]
  calc _ ≤ ∑ b, 2 * (‖inner ℂ (θ v) (bs b)‖ ^ 2 * ‖e‖ ^ 2 + ‖inner ℂ (θ e) (bs b)‖ ^ 2 * ‖v‖ ^ 2) :=
        Finset.sum_le_sum fun b _ => p1 b
    _ = 2 * ((∑ b, ‖inner ℂ (θ v) (bs b)‖ ^ 2) * ‖e‖ ^ 2 + (∑ b, ‖inner ℂ (θ e) (bs b)‖ ^ 2) * ‖v‖ ^ 2) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
    _ = 4 * ‖e‖ ^ 2 * ‖v‖ ^ 2 := by
        rw [bs.sum_sq_norm_inner_left, bs.sum_sq_norm_inner_left, gb_norm_theta h, gb_norm_theta h]
        ring

end GB
end Formalism.HermitianLatticeCounting.P

namespace Formalism.HermitianLatticeCounting.P
section GC
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset Matrix InnerProductSpace
open scoped ComplexConjugate

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

noncomputable def gramSchmidtUnitriangularMatrix {l : ℕ} (y : Fin l → V) : Matrix (Fin l) (Fin l) ℂ := fun a b =>
  if b = a then 1 else if b < a then
    inner ℂ (gramSchmidt ℂ y b) (y a) / ((‖gramSchmidt ℂ y b‖ : ℂ)) ^ 2 else 0

/- English proof (translation)
Use `conv_lhs => rw [gramSchmidt_def'' ℂ y a]`. Rewrite using `[← Finset.add_sum_erase univ _ (Finset.mem_univ a)]`. Use `congr 1`. Simplify using `[gramSchmidtUnitriangularMatrix]`. Use `symm`.

Rewrite using `[← Finset.sum_subset (s₁ := Iio a)]`. Use `Finset.sum_congr rfl fun b hb => ?_` and prove the remaining obligations. Establish `hb' : b < a` using `Finset.mem_Iio.1 hb`. Simplify using `[gramSchmidtUnitriangularMatrix, hb', hb'.ne]`. Introduce `b hb`.

Establish `hb' : b < a` using `Finset.mem_Iio.1 hb`. Simplify using `[hb'.ne]`. Introduce `b hb hb2`. Establish `h1 : b ≠ a` using `by simpa using hb`. Establish `h2 : ¬ b < a` using `by simpa using hb2`.

Simplify using `[gramSchmidtUnitriangularMatrix, h1, h2]`.
-/
lemma gc_expand {l : ℕ} (y : Fin l → V) (a : Fin l) :
    y a = ∑ b, gramSchmidtUnitriangularMatrix y a b • gramSchmidt ℂ y b := by
  conv_lhs => rw [gramSchmidt_def'' ℂ y a]
  rw [← Finset.add_sum_erase univ _ (Finset.mem_univ a)]
  congr 1
  · simp [gramSchmidtUnitriangularMatrix]
  · symm
    rw [← Finset.sum_subset (s₁ := Iio a)]
    · refine Finset.sum_congr rfl fun b hb => ?_
      have hb' : b < a := Finset.mem_Iio.1 hb
      simp [gramSchmidtUnitriangularMatrix, hb', hb'.ne]
    · intro b hb
      have hb' : b < a := Finset.mem_Iio.1 hb
      simp [hb'.ne]
    · intro b hb hb2
      have h1 : b ≠ a := by simpa using hb
      have h2 : ¬ b < a := by simpa using hb2
      simp [gramSchmidtUnitriangularMatrix, h1, h2]

/- English proof (translation)
Use `conv_lhs => rw [gc_expand y a, gc_expand y b]`. Rewrite using `[sum_inner]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[inner_sum, Finset.sum_eq_single c]`. Establish `hs : inner ℂ (gramSchmidt ℂ y c) (gramSchmidt ℂ y c) = (‖gramSchmidt ℂ y c‖ : ℂ) ^ 2`.

Rewrite using `[inner_self_eq_norm_sq_to_K]`. Both sides reduce to the same expression. Rewrite using `[inner_smul_left, inner_smul_right, hs]`. Expand and normalize the polynomial expressions, which then agree. Introduce `d _ hd`.

Rewrite using `[inner_smul_left, inner_smul_right, gramSchmidt_orthogonal ℂ y hd.symm]`. Simplify using the standard rewrite rules. Introduce `h`. Conclude with `absurd (Finset.mem_univ c) h`.
-/
lemma gc_inner {l : ℕ} (y : Fin l → V) (a b : Fin l) :
    inner ℂ (y a) (y b) =
      ∑ c, conj (gramSchmidtUnitriangularMatrix y a c) * ((‖gramSchmidt ℂ y c‖ : ℂ) ^ 2) * gramSchmidtUnitriangularMatrix y b c := by
  conv_lhs => rw [gc_expand y a, gc_expand y b]
  rw [sum_inner]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [inner_sum, Finset.sum_eq_single c]
  · have hs : inner ℂ (gramSchmidt ℂ y c) (gramSchmidt ℂ y c) = (‖gramSchmidt ℂ y c‖ : ℂ) ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]; rfl
    rw [inner_smul_left, inner_smul_right, hs]
    ring
  · intro d _ hd
    rw [inner_smul_left, inner_smul_right, gramSchmidt_orthogonal ℂ y hd.symm]
    simp
  · intro h; exact absurd (Finset.mem_univ c) h

/- English proof (translation)
Establish `hM : (Matrix.of fun a b => inner ℂ (y a) (y b)) = (gramSchmidtUnitriangularMatrix y).map conj * Matrix.diagonal (fun c => (‖gramSchmidt ℂ y c‖ : ℂ) ^ 2) * (gramSchmidtUnitriangularMatrix y)ᵀ`. Use extensionality with `a b`. Rewrite using `[Matrix.of_apply, gc_inner, Matrix.mul_apply]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_diagonal, Matrix.map_apply, Matrix.transpose_apply]`.

Establish `h1 : (gramSchmidtUnitriangularMatrix y).det = 1`. Rewrite using `[Matrix.det_of_isLowerTriangular]`. Simplify using `[gramSchmidtUnitriangularMatrix]`. Introduce `i j hij`. Establish `hij' : i < j` using `hij`.

Simplify using `[gramSchmidtUnitriangularMatrix, hij'.ne', hij'.not_gt]`. Establish `h2 : ((gramSchmidtUnitriangularMatrix y).map conj).det = 1`. Rewrite using `[Matrix.det_of_isLowerTriangular]`. Simplify using `[gramSchmidtUnitriangularMatrix]`. Introduce `i j hij`.

Establish `hij' : i < j` using `hij`. Simplify using `[gramSchmidtUnitriangularMatrix, hij'.ne', hij'.not_gt]`. Rewrite using `[hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h1, h2, Matrix.det_diagonal]`. Simplify using the standard rewrite rules.
-/
lemma gc_det {l : ℕ} (y : Fin l → V) :
    (Matrix.of fun a b => inner ℂ (y a) (y b)).det = ∏ c, (‖gramSchmidt ℂ y c‖ : ℂ) ^ 2 := by
  have hM : (Matrix.of fun a b => inner ℂ (y a) (y b)) =
      (gramSchmidtUnitriangularMatrix y).map conj * Matrix.diagonal (fun c => (‖gramSchmidt ℂ y c‖ : ℂ) ^ 2) * (gramSchmidtUnitriangularMatrix y)ᵀ := by
    ext a b
    rw [Matrix.of_apply, gc_inner, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.mul_diagonal, Matrix.map_apply, Matrix.transpose_apply]
  have h1 : (gramSchmidtUnitriangularMatrix y).det = 1 := by
    rw [Matrix.det_of_isLowerTriangular]
    · simp [gramSchmidtUnitriangularMatrix]
    · intro i j hij
      have hij' : i < j := hij
      simp [gramSchmidtUnitriangularMatrix, hij'.ne', hij'.not_gt]
  have h2 : ((gramSchmidtUnitriangularMatrix y).map conj).det = 1 := by
    rw [Matrix.det_of_isLowerTriangular]
    · simp [gramSchmidtUnitriangularMatrix]
    · intro i j hij
      have hij' : i < j := hij
      simp [gramSchmidtUnitriangularMatrix, hij'.ne', hij'.not_gt]
  rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h1, h2, Matrix.det_diagonal]
  simp

/- English proof (translation)
Unfold `majorantDistance`. Use `set K : Submodule ℂ V := Submodule.span ℂ (y '' {b | b < a}) with hK`. Establish `hKeq : K = Submodule.span ℂ (gramSchmidt ℂ y '' Set.Iio a)`. Rewrite using `[span_gramSchmidt_Iio]`. Both sides reduce to the same expression.

Use `set v : V := y a - gramSchmidt ℂ y a with hv`. Establish `hvK : v ∈ K`. Rewrite using `[hKeq, hv]`. Use `conv => enter [2, 1]`. Rewrite using `[gramSchmidt_def'' ℂ y a]`.

Rewrite using `[add_sub_cancel_left]`. Use `Submodule.sum_mem _ fun b hb => Submodule.smul_mem _ _ (Submodule.subset_span ?_)` and prove the remaining obligations. Conclude with `⟨b, Finset.mem_Iio.1 hb, rfl⟩`. Establish `huv : y a - v = gramSchmidt ℂ y a` using `by rw [hv]; abel`. Establish `horth : ∀ w ∈ K, inner ℂ (y a - v) w = 0`.

Introduce `w hw`. Rewrite using `[huv]`. Rewrite `hw` using `[hKeq]`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨b, hb, rfl⟩` from `hx`. Conclude with `gramSchmidt_orthogonal ℂ y (ne_of_gt hb)`. Consider the case `zero => simp`. Consider the case `add x z _ _ hx hz => rw [inner_add_right, hx, hz, add_zero]`. Consider the case `smul c x _ hx => rw [inner_smul_right, hx, mul_zero]`.

Use `(K.norm_eq_iInf_iff_inner_eq_zero hvK).2 horth` as an intermediate fact. Rewrite `this` using `[huv]`. Rewrite using `[this, Metric.infDist_eq_iInf]`. Simplify using `only [dist_eq_norm]`. Both sides reduce to the same expression.
-/
lemma gc_len {l : ℕ} (y : Fin l → V) (a : Fin l) :
    majorantDistance y a = ‖gramSchmidt ℂ y a‖ := by
  unfold majorantDistance
  set K : Submodule ℂ V := Submodule.span ℂ (y '' {b | b < a}) with hK
  have hKeq : K = Submodule.span ℂ (gramSchmidt ℂ y '' Set.Iio a) := by
    rw [span_gramSchmidt_Iio]; rfl
  set v : V := y a - gramSchmidt ℂ y a with hv
  have hvK : v ∈ K := by
    rw [hKeq, hv]
    conv => enter [2, 1]; rw [gramSchmidt_def'' ℂ y a]
    rw [add_sub_cancel_left]
    refine Submodule.sum_mem _ fun b hb => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨b, Finset.mem_Iio.1 hb, rfl⟩
  have huv : y a - v = gramSchmidt ℂ y a := by rw [hv]; abel
  have horth : ∀ w ∈ K, inner ℂ (y a - v) w = 0 := by
    intro w hw
    rw [huv]
    rw [hKeq] at hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, hb, rfl⟩ := hx
      exact gramSchmidt_orthogonal ℂ y (ne_of_gt hb)
    | zero => simp
    | add x z _ _ hx hz => rw [inner_add_right, hx, hz, add_zero]
    | smul c x _ hx => rw [inner_smul_right, hx, mul_zero]
  have := (K.norm_eq_iInf_iff_inner_eq_zero hvK).2 horth
  rw [huv] at this
  rw [this, Metric.infDist_eq_iInf]
  simp only [dist_eq_norm]
  rfl

/- English proof (translation)
Introduce `V _ _ l y`. Rewrite using `[gc_det]`. Use `push_cast`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[gc_len]`.
-/
theorem gram_matrix_product_formula : Formalism.HermitianLatticeCounting.ExpansionTerms.GramDetEqProdDistances := by
  intro V _ _ l y
  rw [gc_det]
  push_cast
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [gc_len]

end GC
end Formalism.HermitianLatticeCounting.P

namespace Formalism.HermitianLatticeCounting.P

/- English proof (translation)
The claim follows from `orbit_integral_entries_of_leading_minor_at_block_end leading_minor_at_block_end`.
-/
theorem orbit_integral_entries : Formalism.HermitianLatticeCounting.ExpansionTerms.OrbitIntegralEntries := orbit_integral_entries_of_leading_minor_at_block_end leading_minor_at_block_end

end Formalism.HermitianLatticeCounting.P
