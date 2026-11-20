import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.Cuspidal
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.HasModerateGrowthZero

open NumberField IsDedekindDomain Matrix Set Filter Topology
open UpperHalfPlane hiding I I_re I_im
open scoped NumberField.AdeleRing MatrixGroups

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm GroundTheory.Global

variable {N : ℕ} [NeZero N] {k : ℤ}

/- English proof (translation)
Establish `hc : c = -b * (a * d - b * c)` using `by linear_combination (-c) * h1 + a * h3`. Establish `hd : d = a * (a * d - b * c)` using `by linear_combination (-d) * h1 + b * h3`. Establish `hsq : c ^ 2 + d ^ 2 = (a * d - b * c) ^ 2 * (a ^ 2 + b ^ 2)`. Take the linear combination `(c - b * (a * d - b * c)) * hc + (d + a * (a * d - b * c)) * hd`. Establish `hD : (a * d - b * c - 1) * (a * d - b * c + 1) = 0`.

Rewrite `hsq` using `[h1, mul_one, h2]`. Take the linear combination `-hsq`. Break down `mul_eq_zero.1 hD with h | h` into its components or cases. Establish `h' : a * d - b * c = 1` using `by linarith`. Conclude with `Or.inl ⟨by rw [hc, h', mul_one], by rw [hd, h', mul_one]⟩`.

Establish `h' : a * d - b * c = -1` using `by linarith`. Conclude with `Or.inr ⟨by rw [hc, h']; ring, by rw [hd, h']; ring⟩`.
-/
theorem orthogonal_cases {a b c d : ℝ} (h1 : a ^ 2 + b ^ 2 = 1) (h2 : c ^ 2 + d ^ 2 = 1)
    (h3 : a * c + b * d = 0) : (c = -b ∧ d = a) ∨ (c = b ∧ d = -a) := by
  have hc : c = -b * (a * d - b * c) := by linear_combination (-c) * h1 + a * h3
  have hd : d = a * (a * d - b * c) := by linear_combination (-d) * h1 + b * h3
  have hsq : c ^ 2 + d ^ 2 = (a * d - b * c) ^ 2 * (a ^ 2 + b ^ 2) := by
    linear_combination (c - b * (a * d - b * c)) * hc + (d + a * (a * d - b * c)) * hd
  have hD : (a * d - b * c - 1) * (a * d - b * c + 1) = 0 := by
    rw [h1, mul_one, h2] at hsq
    linear_combination -hsq
  rcases mul_eq_zero.1 hD with h | h
  · have h' : a * d - b * c = 1 := by linarith
    exact Or.inl ⟨by rw [hc, h', mul_one], by rw [hd, h', mul_one]⟩
  · have h' : a * d - b * c = -1 := by linarith
    exact Or.inr ⟨by rw [hc, h']; ring, by rw [hd, h']; ring⟩

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [epsilon]`.
-/
theorem coe_toReal_epsilon : (toReal epsilon : Matrix (Fin 2) (Fin 2) ℝ) = !![-1, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [epsilon]

/- English proof (translation)
Establish `hnorm : ∀ w : ℂ, w.re ^ 2 + w.im ^ 2 = 1 → ‖w‖ = 1`. Introduce `w hw`. Rewrite using `[Complex.norm_def, Complex.normSq_apply, show w.re * w.re + w.im * w.im = 1 by nlinarith, Real.sqrt_one]`. Establish `hne : ∀ w : ℂ, ‖w‖ = 1 → w ≠ 0` using `fun w hw h => by rw [h, norm_zero] at hw; exact zero_ne_one hw`. Break down `orthogonal_cases h1 h2 h3 with ⟨hc, hd⟩ | ⟨hc, hd⟩` into its components or cases.

Use `set w : ℂ := ⟨K 0 0, -K 0 1⟩`. Establish `hw : ‖w‖ = 1` using `hnorm w (by simp only [w]; nlinarith)`. Use `⟨w, hne w hw, hw, Or.inl ?_⟩` and prove the remaining obligations. Use `Matrix.GeneralLinearGroup.ext fun i j => ?_` and prove the remaining obligations. Rewrite using `[coe_kGL]`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [w, hc, hd]`. Use `set w : ℂ := ⟨-K 0 0, K 0 1⟩`. Establish `hw : ‖w‖ = 1` using `hnorm w (by simp only [w]; nlinarith)`. Use `⟨w, hne w hw, hw, Or.inr ?_⟩` and prove the remaining obligations. Use `Matrix.GeneralLinearGroup.ext fun i j => ?_` and prove the remaining obligations.

Rewrite using `[Units.val_mul, coe_toReal_epsilon, coe_kGL]`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [w, hc, hd, Matrix.mul_apply, Fin.sum_univ_two]`.
-/
theorem exists_eq_kGL_of_orthogonal (K : GL (Fin 2) ℝ)
    (h1 : K 0 0 ^ 2 + K 0 1 ^ 2 = 1) (h2 : K 1 0 ^ 2 + K 1 1 ^ 2 = 1)
    (h3 : K 0 0 * K 1 0 + K 0 1 * K 1 1 = 0) :
    ∃ (w : ℂ) (hw : w ≠ 0), ‖w‖ = 1 ∧ (K = kGL w hw ∨ K = toReal epsilon * kGL w hw) := by
  have hnorm : ∀ w : ℂ, w.re ^ 2 + w.im ^ 2 = 1 → ‖w‖ = 1 := by
    intro w hw
    rw [Complex.norm_def, Complex.normSq_apply, show w.re * w.re + w.im * w.im = 1 by nlinarith,
      Real.sqrt_one]
  have hne : ∀ w : ℂ, ‖w‖ = 1 → w ≠ 0 := fun w hw h => by rw [h, norm_zero] at hw; exact zero_ne_one hw
  rcases orthogonal_cases h1 h2 h3 with ⟨hc, hd⟩ | ⟨hc, hd⟩
  · set w : ℂ := ⟨K 0 0, -K 0 1⟩
    have hw : ‖w‖ = 1 := hnorm w (by simp only [w]; nlinarith)
    refine ⟨w, hne w hw, hw, Or.inl ?_⟩
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [coe_kGL]
    fin_cases i <;> fin_cases j <;> simp [w, hc, hd]
  · set w : ℂ := ⟨-K 0 0, K 0 1⟩
    have hw : ‖w‖ = 1 := hnorm w (by simp only [w]; nlinarith)
    refine ⟨w, hne w hw, hw, Or.inr ?_⟩
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [Units.val_mul, coe_toReal_epsilon, coe_kGL]
    fin_cases i <;> fin_cases j <;> simp [w, hc, hd, Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
Use `set w0 : InfinitePlace ℚ := default`. Establish `hw0` using `RationalIdeles.isReal_infinitePlace w0`. Establish `hn` using `(Reduction.mem_maxCompact.1 hx).1 w0`. Rewrite `hn` using `[Reduction.mem_archCompact]`. Use `set M : Matrix (Fin 2) (Fin 2) w0.Completion := ((Reduction.infAt w0 x : GL (Fin 2) w0.Completion) : Matrix (Fin 2) (Fin 2) w0.Completion)`.

Use `set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw0`. Establish `hE : ∀ a b, realPart x a b = e (M a b)` using `fun a b => rfl`. Establish `hEn : ∀ z, ‖e z‖ = ‖z‖` using `fun z => (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw0).norm_map_of_map_zero (map_zero _) z`. Establish `key : ∀ y0 y1 : ℝ, (y0 * realPart x 0 0 + y1 * realPart x 1 0) ^ 2 + (y0 * realPart x 0 1 + y1 * realPart x 1 1) ^ 2 = y0 ^ 2 + y1 ^ 2`. Introduce `y0 y1`.

Establish `h` using `hn ![e.symm y0, e.symm y1]`. Simplify using `only [Reduction.euclidNorm, Fin.sum_univ_two, Matrix.vecMul, dotProduct, Matrix.cons_val_zero, Matrix.cons_val_one] at h`. Establish `hy : ∀ (y : ℝ) (z : w0.Completion), ‖e.symm y * z‖ = |y| * ‖e z‖`. Introduce `y z`. Rewrite using `[norm_mul, hEn, ← hEn (e.symm y), RingEquiv.apply_symm_apply, Real.norm_eq_abs]`.

Establish `hsum : ∀ j : Fin 2, ‖e.symm y0 * M 0 j + e.symm y1 * M 1 j‖ = |y0 * realPart x 0 j + y1 * realPart x 1 j|`. Introduce `j`. Rewrite using `[← hEn, map_add, map_mul, map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, hE, hE, Real.norm_eq_abs]`. Establish `hy0 : ‖e.symm y0‖ = |y0|` using `by rw [← hEn, RingEquiv.apply_symm_apply, Real.norm_eq_abs]`. Establish `hy1 : ‖e.symm y1‖ = |y1|` using `by rw [← hEn, RingEquiv.apply_symm_apply, Real.norm_eq_abs]`.

Rewrite `h` using `[hsum 0, hsum 1, hy0, hy1, sq_abs, sq_abs, sq_abs, sq_abs]`. Use `congrArg (· ^ 2) h` as an intermediate fact. Rewrite `this` using `[Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]`. Then use the resulting hypothesis. Establish `k10` using `key 1 0`. Establish `k01` using `key 0 1`.

Establish `k11` using `key 1 1`. Use `⟨by linear_combination k10, by linear_combination k01, ?_⟩` and prove the remaining obligations. Take the linear combination `(k11 - k10 - k01) / 2`.
-/
theorem realPart_orthogonal {x : AdelicGL ℚ 2} (hx : x ∈ Reduction.maxCompact) :
    realPart x 0 0 ^ 2 + realPart x 0 1 ^ 2 = 1 ∧ realPart x 1 0 ^ 2 + realPart x 1 1 ^ 2 = 1 ∧
      realPart x 0 0 * realPart x 1 0 + realPart x 0 1 * realPart x 1 1 = 0 := by
  set w0 : InfinitePlace ℚ := default
  have hw0 := RationalIdeles.isReal_infinitePlace w0
  have hn := (Reduction.mem_maxCompact.1 hx).1 w0
  rw [Reduction.mem_archCompact] at hn
  set M : Matrix (Fin 2) (Fin 2) w0.Completion :=
    ((Reduction.infAt w0 x : GL (Fin 2) w0.Completion) : Matrix (Fin 2) (Fin 2) w0.Completion)
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw0
  have hE : ∀ a b, realPart x a b = e (M a b) := fun a b => rfl
  have hEn : ∀ z, ‖e z‖ = ‖z‖ := fun z =>
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw0).norm_map_of_map_zero
      (map_zero _) z
  have key : ∀ y0 y1 : ℝ, (y0 * realPart x 0 0 + y1 * realPart x 1 0) ^ 2 +
      (y0 * realPart x 0 1 + y1 * realPart x 1 1) ^ 2 = y0 ^ 2 + y1 ^ 2 := by
    intro y0 y1
    have h := hn ![e.symm y0, e.symm y1]
    simp only [Reduction.euclidNorm, Fin.sum_univ_two, Matrix.vecMul, dotProduct,
      Matrix.cons_val_zero, Matrix.cons_val_one] at h
    have hy : ∀ (y : ℝ) (z : w0.Completion), ‖e.symm y * z‖ = |y| * ‖e z‖ := by
      intro y z
      rw [norm_mul, hEn, ← hEn (e.symm y), RingEquiv.apply_symm_apply, Real.norm_eq_abs]
    have hsum : ∀ j : Fin 2, ‖e.symm y0 * M 0 j + e.symm y1 * M 1 j‖ =
        |y0 * realPart x 0 j + y1 * realPart x 1 j| := by
      intro j
      rw [← hEn, map_add, map_mul, map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply,
        hE, hE, Real.norm_eq_abs]
    have hy0 : ‖e.symm y0‖ = |y0| := by rw [← hEn, RingEquiv.apply_symm_apply, Real.norm_eq_abs]
    have hy1 : ‖e.symm y1‖ = |y1| := by rw [← hEn, RingEquiv.apply_symm_apply, Real.norm_eq_abs]
    rw [hsum 0, hsum 1, hy0, hy1, sq_abs, sq_abs, sq_abs, sq_abs] at h
    have := congrArg (· ^ 2) h
    rwa [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)] at this
  have k10 := key 1 0
  have k01 := key 0 1
  have k11 := key 1 1
  refine ⟨by linear_combination k10, by linear_combination k01, ?_⟩
  linear_combination (k11 - k10 - k01) / 2

/- English proof (translation)
The claim follows from `(mem_integralFiniteGL_iff_forall ℚ 2).2 fun v => (Reduction.mem_maxCompact.1 hx).2 v`.
-/
theorem finitePart_mem_integralFiniteGL {x : AdelicGL ℚ 2} (hx : x ∈ Reduction.maxCompact) :
    (prodEquiv ℚ 2 x).2 ∈ integralFiniteGL ℚ 2 :=
  (mem_integralFiniteGL_iff_forall ℚ 2).2 fun v => (Reduction.mem_maxCompact.1 hx).2 v

variable (N) in

/- English proof (translation)
Take `⟨t, ht⟩` from `(isCompact_integralFiniteGL ℚ 2).elim_finite_subcover (fun c : FiniteAdelicGL ℚ 2 => (fun x => c⁻¹ * x) ⁻¹' (Gamma0Level N : Set (FiniteAdelicGL ℚ 2))) (fun c => (isOpen_Gamma0Level N).preimage (continuous_const.mul continuous_id)) (fun x _ => Set.mem_iUnion.2 ⟨x, show x⁻¹ * x ∈ …`. Rewrite using `[inv_mul_cancel]`. Conclude with `one_mem _⟩)`. Use `⟨t, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨c, hc, hxc⟩` from `Set.mem_iUnion₂.1 (ht hx)`.

Conclude with `⟨c, hc, hxc⟩`.
-/
theorem exists_finset_cover :
    ∃ C : Finset (FiniteAdelicGL ℚ 2), ∀ x ∈ integralFiniteGL ℚ 2, ∃ c ∈ C, c⁻¹ * x ∈ Gamma0Level N := by
  obtain ⟨t, ht⟩ := (isCompact_integralFiniteGL ℚ 2).elim_finite_subcover
    (fun c : FiniteAdelicGL ℚ 2 => (fun x => c⁻¹ * x) ⁻¹' (Gamma0Level N : Set (FiniteAdelicGL ℚ 2)))
    (fun c => (isOpen_Gamma0Level N).preimage (continuous_const.mul continuous_id))
    (fun x _ => Set.mem_iUnion.2 ⟨x, show x⁻¹ * x ∈ (Gamma0Level N : Set (FiniteAdelicGL ℚ 2)) by
      rw [inv_mul_cancel]
      exact one_mem _⟩)
  refine ⟨t, fun x hx => ?_⟩
  obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.1 (ht hx)
  exact ⟨c, hc, hxc⟩

/- English proof (translation)
Take `⟨C, hC⟩` from `exists_finset_cover N`. Use `set ψ : C × Bool → AdelicGL ℚ 2 → ℂ := fun p => rightTranslate (realEmb (if p.2 then toReal epsilon else 1) * finEmb ℚ 2 p.1) φ`. Establish `hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range ψ))` using `FiniteDimensional.span_of_finite ℂ (Set.finite_range ψ)`. Unfold `IsKFinite`. Use `Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range ψ)) (Submodule.span_le.2 ?_)` and prove the remaining obligations.

Introduce and unpack `_ ⟨⟨x, hx⟩, rfl⟩`. Take `⟨h1, h2, h3⟩` from `realPart_orthogonal hx`. Take `⟨w, hw0, hw, hK⟩` from `exists_eq_kGL_of_orthogonal (realPart x) h1 h2 h3`. Take `⟨c, hc, hcu⟩` from `hC _ (finitePart_mem_integralFiniteGL hx)`. Use `set u := c⁻¹ * (prodEquiv ℚ 2 x).2`.

Establish `hxd : x = realEmb (realPart x) * finEmb ℚ 2 (c * u)`. Rewrite using `[mul_inv_cancel_left, realEmb_realPart_mul_finEmb]`. Establish `hscal : ∀ (e : GL (Fin 2) ℝ) (g : AdelicGL ℚ 2), φ (g * (realEmb (e * kGL w hw0) * finEmb ℚ 2 (c * u))) = (w / (‖w‖ : ℂ)) ^ (-k) * φ (g * (realEmb e * finEmb ℚ 2 c))`. Introduce `e g`. Establish `: g * (realEmb (e * kGL w hw0) * finEmb ℚ 2 (c * u)) = g * (realEmb e * finEmb ℚ 2 c) * realEmb (kGL w hw0) * finEmb ℚ 2 u`.

Apply `(prodEquiv ℚ 2).injective` to reduce the goal to its premises. Simplify using `only [map_mul, prodEquiv_realEmb, prodEquiv_finEmb, Prod.mk_mul_mk, mul_one, one_mul]`. Apply the tactic sequence `refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_mul, Prod.snd_mul, mul_one] <;> group`. Rewrite using `[this, hφ.right_level _ _ hcu, hφ.right_kGL]`. Break down `hK with hK | hK` into its components or cases.

Establish `: rightTranslate x φ = (w / (‖w‖ : ℂ)) ^ (-k) • ψ (⟨c, hc⟩, false)`. Use function extensionality and compare the values at `g`. Simplify using `only [rightTranslate, ψ, Pi.smul_apply, smul_eq_mul, if_neg Bool.false_ne_true]`. Rewrite using `[hxd, hK, ← one_mul (kGL w hw0), hscal]`. Use `show rightTranslate x φ ∈ _`.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)`. Establish `: rightTranslate x φ = (w / (‖w‖ : ℂ)) ^ (-k) • ψ (⟨c, hc⟩, true)`. Use function extensionality and compare the values at `g`. Simplify using `only [rightTranslate, ψ, Pi.smul_apply, smul_eq_mul, if_pos]`.

Rewrite using `[hxd, hK, hscal]`. Use `show rightTranslate x φ ∈ _`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)`.
-/
theorem IsWeightLevel.isKFinite {φ : AdelicGL ℚ 2 → ℂ} (hφ : IsWeightLevel N k φ) : IsKFinite φ := by
  obtain ⟨C, hC⟩ := exists_finset_cover N
  set ψ : C × Bool → AdelicGL ℚ 2 → ℂ := fun p =>
    rightTranslate (realEmb (if p.2 then toReal epsilon else 1) * finEmb ℚ 2 p.1) φ
  have hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range ψ)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range ψ)
  unfold IsKFinite
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range ψ))
    (Submodule.span_le.2 ?_)
  rintro _ ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨h1, h2, h3⟩ := realPart_orthogonal hx
  obtain ⟨w, hw0, hw, hK⟩ := exists_eq_kGL_of_orthogonal (realPart x) h1 h2 h3
  obtain ⟨c, hc, hcu⟩ := hC _ (finitePart_mem_integralFiniteGL hx)
  set u := c⁻¹ * (prodEquiv ℚ 2 x).2
  have hxd : x = realEmb (realPart x) * finEmb ℚ 2 (c * u) := by
    rw [mul_inv_cancel_left, realEmb_realPart_mul_finEmb]

  have hscal : ∀ (e : GL (Fin 2) ℝ) (g : AdelicGL ℚ 2),
      φ (g * (realEmb (e * kGL w hw0) * finEmb ℚ 2 (c * u))) =
        (w / (‖w‖ : ℂ)) ^ (-k) * φ (g * (realEmb e * finEmb ℚ 2 c)) := by
    intro e g
    have : g * (realEmb (e * kGL w hw0) * finEmb ℚ 2 (c * u)) =
        g * (realEmb e * finEmb ℚ 2 c) * realEmb (kGL w hw0) * finEmb ℚ 2 u := by
      apply (prodEquiv ℚ 2).injective
      simp only [map_mul, prodEquiv_realEmb, prodEquiv_finEmb, Prod.mk_mul_mk, mul_one, one_mul]
      refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_mul, Prod.snd_mul, mul_one] <;> group
    rw [this, hφ.right_level _ _ hcu, hφ.right_kGL]
  rcases hK with hK | hK
  · have : rightTranslate x φ = (w / (‖w‖ : ℂ)) ^ (-k) • ψ (⟨c, hc⟩, false) := by
      funext g
      simp only [rightTranslate, ψ, Pi.smul_apply, smul_eq_mul, if_neg Bool.false_ne_true]
      rw [hxd, hK, ← one_mul (kGL w hw0), hscal]
    show rightTranslate x φ ∈ _
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  · have : rightTranslate x φ = (w / (‖w‖ : ℂ)) ^ (-k) • ψ (⟨c, hc⟩, true) := by
      funext g
      simp only [rightTranslate, ψ, Pi.smul_apply, smul_eq_mul, if_pos]
      rw [hxd, hK, hscal]
    show rightTranslate x φ ∈ _
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

end GL2Classical

end

end GroundTheory.Automorphic
