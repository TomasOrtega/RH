import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.ComplexMatrixMajorantIntegrable

noncomputable section

open MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.SecFubini

open Ad3.K Ad3.K.LC Ad3.K.LC.C

/- English proof (translation)
Unfold `psiC`. Establish `h : (-2 * (Real.pi : ℂ) * Complex.I * (2 * (x.re : ℂ))) = ((-2 * Real.pi * (2 * x.re) : ℝ) : ℂ) * Complex.I` using `by push_cast; ring`. Rewrite using `[h, Complex.norm_exp_ofReal_mul_I]`.
-/
theorem psiC_norm (x : ℂ) : ‖psiC x‖ = 1 := by
  unfold psiC
  have h : (-2 * (Real.pi : ℂ) * Complex.I * (2 * (x.re : ℂ))) =
      ((-2 * Real.pi * (2 * x.re) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/- English proof (translation)
Unfold `psiC`. Use `fun_prop`.
-/
theorem psiC_continuous : Continuous psiC := by
  unfold psiC
  fun_prop

/- English proof (translation)
Take `⟨K, -, hK⟩` from `(LinearMap.injective_iff_antilipschitz A).1 hA`. Establish `hanti : AntilipschitzWith K (fun p => A p + c)` using `AntilipschitzWith.of_le_mul_dist fun x y => by`. Simplify `hK.le_mul_dist x y` using `[dist_add_right]`. Set `Ac : E →L[ℝ] F` to `LinearMap.toContinuousLinearMap A`. Establish `hg : Function.HasTemperateGrowth (fun p => A p + c)` using `(Ac.hasTemperateGrowth).add (Function.HasTemperateGrowth.const c)`.

Conclude with `(SchwartzMap.compCLMOfAntilipschitz ℝ hg hanti Ψ).integrable`.
-/
theorem integrable_schwartz_affine {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure E) [μ.HasTemperateGrowth] (A : E →ₗ[ℝ] F) (hA : Function.Injective A)
    (c : F) (Ψ : SchwartzMap F ℂ) : Integrable (fun p => Ψ (A p + c)) μ := by
  obtain ⟨K, -, hK⟩ := (LinearMap.injective_iff_antilipschitz A).1 hA
  have hanti : AntilipschitzWith K (fun p => A p + c) :=
    AntilipschitzWith.of_le_mul_dist fun x y => by
      simpa [dist_add_right] using hK.le_mul_dist x y
  let Ac : E →L[ℝ] F := LinearMap.toContinuousLinearMap A
  have hg : Function.HasTemperateGrowth (fun p => A p + c) :=
    (Ac.hasTemperateGrowth).add (Function.HasTemperateGrowth.const c)
  exact (SchwartzMap.compCLMOfAntilipschitz ℝ hg hanti Ψ).integrable

def nb (x : Fin 2 → ℂ) : Matrix (Fin 2) (Fin 3) ℂ := !![0, 0, x 0; 0, 0, x 1]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [blk, nb]`.
-/
theorem blk_eq (x : Fin 2 → ℂ) : blk x = nb x + blk 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk, nb]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [nb]`.
-/
theorem nb_add (x y : Fin 2 → ℂ) : nb (x + y) = nb x + nb y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nb]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [nb]`.
-/
theorem nb_smul (r : ℝ) (x : Fin 2 → ℂ) : nb (r • x) = r • nb x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nb]

def linP (H : Matrix (Fin 2) (Fin 2) ℂ) (G : Matrix (Fin 3) (Fin 3) ℂ) (t : ℂ) :
    ((Fin 2 → ℂ) × ℂ) →ₗ[ℝ] (M23 × (Fin 2 → ℂ)) where
  toFun p := (Matrix.of.symm (H * nb p.1 * G), Matrix.vecMul ![0, t * p.2] H⁻¹)
  map_add' p q := by
    have h1 : H * nb (p.1 + q.1) * G = H * nb p.1 * G + H * nb q.1 * G := by
      rw [nb_add, Matrix.mul_add, Matrix.add_mul]
    have h2 : (![0, t * (p.2 + q.2)] : Fin 2 → ℂ) = ![0, t * p.2] + ![0, t * q.2] := by
      ext i; fin_cases i <;> simp [mul_add]
    simp only [Prod.fst_add, Prod.snd_add, h1, h2, Matrix.add_vecMul]
    rfl
  map_smul' r p := by
    have h1 : H * nb (r • p.1) * G = r • (H * nb p.1 * G) := by
      rw [nb_smul, Matrix.mul_smul, Matrix.smul_mul]
    have h2 : (![0, t * (r • p.2)] : Fin 2 → ℂ) = r • ![0, t * p.2] := by
      ext i; fin_cases i <;> simp; ring
    simp only [Prod.smul_fst, Prod.smul_snd, h1, h2, Matrix.smul_vecMul, RingHom.id_apply]
    rfl

/- English proof (translation)
Use `(injective_iff_map_eq_zero _).2 fun p hp => ?_` and prove the remaining obligations. Establish `hHu : IsUnit H.det` using `isUnit_iff_ne_zero.2 hH`. Establish `hGu : IsUnit G.det` using `isUnit_iff_ne_zero.2 hG`. Establish `e1 : H * nb p.1 * G = 0` using `congrArg Prod.fst hp`. Establish `e2 : Matrix.vecMul ![0, t * p.2] H⁻¹ = 0` using `congrArg Prod.snd hp`.

Establish `hn : nb p.1 = 0`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc H, ← Matrix.mul_assoc H⁻¹, Matrix.nonsing_inv_mul _ hHu, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hGu, Matrix.mul_one]`. Use `_ = 0 := by rw [e1]; simp`. Establish `hx : p.1 = 0`.

Use extensionality with `i`. Use `congrFun (congrFun hn i) 2` as an intermediate fact. Apply the tactic sequence `fin_cases i <;> simpa [nb] using this`. Establish `hv : (![0, t * p.2] : Fin 2 → ℂ) = 0`. Use `congrArg (fun v => Matrix.vecMul v H) e2` as an intermediate fact.

Simplify `this` using `[Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hHu]`. Establish `hy : p.2 = 0`. Use `congrFun hv 1` as an intermediate fact. Simplify `this` using `[ht]`. Conclude with `Prod.ext hx hy`.
-/
theorem linP_injective {H : Matrix (Fin 2) (Fin 2) ℂ} {G : Matrix (Fin 3) (Fin 3) ℂ} {t : ℂ}
    (hH : H.det ≠ 0) (hG : G.det ≠ 0) (ht : t ≠ 0) : Function.Injective (linP H G t) := by
  refine (injective_iff_map_eq_zero _).2 fun p hp => ?_
  have hHu : IsUnit H.det := isUnit_iff_ne_zero.2 hH
  have hGu : IsUnit G.det := isUnit_iff_ne_zero.2 hG
  have e1 : H * nb p.1 * G = 0 := congrArg Prod.fst hp
  have e2 : Matrix.vecMul ![0, t * p.2] H⁻¹ = 0 := congrArg Prod.snd hp
  have hn : nb p.1 = 0 := by
    calc nb p.1 = H⁻¹ * (H * nb p.1 * G) * G⁻¹ := by
          rw [Matrix.mul_assoc H, ← Matrix.mul_assoc H⁻¹, Matrix.nonsing_inv_mul _ hHu,
            Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hGu, Matrix.mul_one]
      _ = 0 := by rw [e1]; simp
  have hx : p.1 = 0 := by
    ext i
    have := congrFun (congrFun hn i) 2
    fin_cases i <;> simpa [nb] using this
  have hv : (![0, t * p.2] : Fin 2 → ℂ) = 0 := by
    have := congrArg (fun v => Matrix.vecMul v H) e2
    simpa [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hHu] using this
  have hy : p.2 = 0 := by
    have := congrFun hv 1
    simpa [ht] using this
  exact Prod.ext hx hy

/- English proof (translation)
Establish `hG : (g : Matrix (Fin 3) (Fin 3) ℂ).det ≠ 0` using `((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero`. Use `haveI hHaar : (volume : Measure ((Fin 2 → ℂ) × ℂ)).IsAddHaarMeasure := by`. Rewrite using `[Measure.volume_eq_prod]`. Conclude with `Measure.prod.instIsAddHaarMeasure _ _`. Use `haveI : (volume : Measure ((Fin 2 → ℂ) × ℂ)).HasTemperateGrowth := MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth`.

Establish `hI` using `integrable_schwartz_affine (volume : Measure ((Fin 2 → ℂ) × ℂ)) (linP H (g : Matrix (Fin 3) (Fin 3) ℂ) t) (linP_injective hH hG ht) (Matrix.of.symm (H * blk 0 * (g : Matrix (Fin 3) (Fin 3) ℂ)), Matrix.vecMul ![t, 0] H⁻¹) Ψ`. Establish `hL : (fun p : (Fin 2 → ℂ) × ℂ => Ψ (linP H (g : Matrix (Fin 3) (Fin 3) ℂ) t p + (Matrix.of.symm (H * blk 0 * (g : Matrix (Fin 3) (Fin 3) ℂ)), Matrix.vecMul ![t, 0] H⁻¹))) = fun p => Ψ (Matrix.of.symm (H * blk p.1 * (g : Matrix (Fin 3) (Fin 3) ℂ)), rowv t p.2 H)`. Use function extensionality and compare the values at `p`. Use `congr 1`. Use `Prod.ext ?_ ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `Matrix.of.symm (H * nb p.1 * (g : Matrix (Fin 3) (Fin 3) ℂ) + H * blk 0 * (g : Matrix (Fin 3) (Fin 3) ℂ)) = _`. Rewrite using `[blk_eq p.1, Matrix.mul_add, Matrix.add_mul]`. Express the relevant statement in the definitionally equal form `Matrix.vecMul ![0, t * p.2] H⁻¹ + Matrix.vecMul ![t, 0] H⁻¹ = _`. Establish `h2 : (![t, t * p.2] : Fin 2 → ℂ) = ![0, t * p.2] + ![t, 0]`. Apply the tactic sequence `ext i; fin_cases i <;> simp`.

Rewrite using `[rowv, h2, Matrix.add_vecMul]`. Rewrite `hI` using `[hL]`. Use `hI.mono ?_ (ae_of_all _ fun p => ?_)` and prove the remaining obligations. Use `(hI.aestronglyMeasurable.mul ?_).mul ?_` and prove the remaining obligations. Conclude with `(psiC_continuous.comp (by fun_prop)).aestronglyMeasurable`.

Conclude with `(psiC_continuous.comp (by fun_prop)).aestronglyMeasurable`. Simplify using `[psiC_norm]`.
-/
theorem inn_integrable (Ψ : Sw) (g : GL (Fin 3) ℂ) {H : Matrix (Fin 2) (Fin 2) ℂ} {t : ℂ}
    (hH : H.det ≠ 0) (ht : t ≠ 0) :
    Integrable (fun p : (Fin 2 → ℂ) × ℂ =>
      Ψ (Matrix.of.symm (H * blk p.1 * (g : Matrix (Fin 3) (Fin 3) ℂ)), rowv t p.2 H) *
        psiC (-(p.1 1)) * psiC (-p.2)) := by
  have hG : (g : Matrix (Fin 3) (Fin 3) ℂ).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
  haveI hHaar : (volume : Measure ((Fin 2 → ℂ) × ℂ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    exact Measure.prod.instIsAddHaarMeasure _ _
  haveI : (volume : Measure ((Fin 2 → ℂ) × ℂ)).HasTemperateGrowth :=
    MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth
  have hI := integrable_schwartz_affine (volume : Measure ((Fin 2 → ℂ) × ℂ))
    (linP H (g : Matrix (Fin 3) (Fin 3) ℂ) t) (linP_injective hH hG ht)
    (Matrix.of.symm (H * blk 0 * (g : Matrix (Fin 3) (Fin 3) ℂ)), Matrix.vecMul ![t, 0] H⁻¹) Ψ
  have hL : (fun p : (Fin 2 → ℂ) × ℂ => Ψ (linP H (g : Matrix (Fin 3) (Fin 3) ℂ) t p +
      (Matrix.of.symm (H * blk 0 * (g : Matrix (Fin 3) (Fin 3) ℂ)), Matrix.vecMul ![t, 0] H⁻¹))) =
      fun p => Ψ (Matrix.of.symm (H * blk p.1 * (g : Matrix (Fin 3) (Fin 3) ℂ)), rowv t p.2 H) := by
    funext p
    congr 1
    refine Prod.ext ?_ ?_
    · change Matrix.of.symm (H * nb p.1 * (g : Matrix (Fin 3) (Fin 3) ℂ) +
        H * blk 0 * (g : Matrix (Fin 3) (Fin 3) ℂ)) = _
      rw [blk_eq p.1, Matrix.mul_add, Matrix.add_mul]
    · change Matrix.vecMul ![0, t * p.2] H⁻¹ + Matrix.vecMul ![t, 0] H⁻¹ = _
      have h2 : (![t, t * p.2] : Fin 2 → ℂ) = ![0, t * p.2] + ![t, 0] := by
        ext i; fin_cases i <;> simp
      rw [rowv, h2, Matrix.add_vecMul]
  rw [hL] at hI
  refine hI.mono ?_ (ae_of_all _ fun p => ?_)
  · refine (hI.aestronglyMeasurable.mul ?_).mul ?_
    · exact (psiC_continuous.comp (by fun_prop)).aestronglyMeasurable
    · exact (psiC_continuous.comp (by fun_prop)).aestronglyMeasurable
  · simp [psiC_norm]

/- English proof (translation)
Unfold `inn`. Rewrite using `[Measure.volume_eq_prod, integral_prod_symm _ (inn_integrable Ψ g hH ht)]`. Use `congr 1`. Use function extensionality and compare the values at `y`. Rewrite using `[← integral_mul_const]`.

Simplify using `only [one_mul, rowv]`.
-/
theorem inn_eq (Ψ : Sw) (g : GL (Fin 3) ℂ) {H : Matrix (Fin 2) (Fin 2) ℂ} {t : ℂ}
    (hH : H.det ≠ 0) (ht : t ≠ 0) :
    inn Ψ g H t = ∫ y : ℂ, (∫ x : Fin 2 → ℂ,
      Ψ (Matrix.of.symm (H * blk x * (g : Matrix (Fin 3) (Fin 3) ℂ)), Matrix.vecMul ![t, t * y] H⁻¹) *
        psiC (-(1 * x 1))) * psiC (-y) := by
  unfold inn
  rw [Measure.volume_eq_prod, integral_prod_symm _ (inn_integrable Ψ g hH ht)]
  congr 1
  funext y
  rw [← integral_mul_const]
  simp only [one_mul, rowv]

/- English proof (translation)
Simplify using `[ph, _root_.zero_zpow _ hn]`.
-/
theorem ph_zero {n : ℤ} (hn : n ≠ 0) : ph n 0 = 0 := by
  simp [ph, _root_.zero_zpow _ hn]

/- English proof (translation)
Unfold `ph`. Rewrite using `[_root_.zpow_neg, ← _root_.inv_zpow]`. Use `congr 1`. Simplify using `[div_eq_mul_inv, mul_comm]`.
-/
theorem ph_inv (n : ℤ) (d : ℂ) : ph n d⁻¹ = ph (-n) d := by
  unfold ph
  rw [_root_.zpow_neg, ← _root_.inv_zpow]
  congr 1
  simp [div_eq_mul_inv, mul_comm]

/- English proof (translation)
Introduce `k hk Ψ g`. Unfold `sec`. Use `congr 1`. Use `integral_congr_ae (ae_of_all _ fun h => ?_)` and prove the remaining obligations. Distinguish the cases in `hd : (Matrix.of h).det = 0`.

Establish `hn : (-(2 * (k : ℤ) - 2)) ≠ 0` using `by omega`. Simplify using `[hd, ph_zero hn]`. Establish `hJ : ∫ t : ℂ, inn Ψ g (Matrix.of h) t * ph (4 * (k : ℤ) - 4) t = ∫ t : ℂ, ph (4 * (k : ℤ) - 4) t * ∫ y : ℂ, innQ Ψ g h 1 (Matrix.vecMul ![t, t * y] (Matrix.of h)⁻¹) * psiC (-y)`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℂ))] with t ht`.

Establish `ht' : t ≠ 0` using `ht`. Rewrite using `[inn_eq Ψ g hd ht', mul_comm]`. Both sides reduce to the same expression. Establish `hdet : ((Matrix.of h)⁻¹).det = ((Matrix.of h).det)⁻¹`. Rewrite using `[Matrix.det_nonsing_inv, Ring.inverse_eq_inv']`.

Establish `hr : ‖(Matrix.of h).det‖ ^ (-(2 : ℝ)) = ‖(Matrix.of h).det‖⁻¹ * ‖(Matrix.of h).det‖⁻¹`. Rewrite using `[Real.rpow_neg (norm_nonneg _), Real.rpow_two, sq, mul_inv]`. Use `beta_reduce`. Rewrite using `[hJ, W2, hdet, ph_inv, hr, norm_inv]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem secQ : SecQ := by
  intro k hk Ψ g
  unfold sec
  congr 1
  refine integral_congr_ae (ae_of_all _ fun h => ?_)
  by_cases hd : (Matrix.of h).det = 0
  · have hn : (-(2 * (k : ℤ) - 2)) ≠ 0 := by omega
    simp [hd, ph_zero hn]
  · have hJ : ∫ t : ℂ, inn Ψ g (Matrix.of h) t * ph (4 * (k : ℤ) - 4) t =
        ∫ t : ℂ, ph (4 * (k : ℤ) - 4) t *
          ∫ y : ℂ, innQ Ψ g h 1 (Matrix.vecMul ![t, t * y] (Matrix.of h)⁻¹) * psiC (-y) := by
      refine integral_congr_ae ?_
      filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℂ))] with t ht
      have ht' : t ≠ 0 := ht
      rw [inn_eq Ψ g hd ht', mul_comm]
      rfl
    have hdet : ((Matrix.of h)⁻¹).det = ((Matrix.of h).det)⁻¹ := by
      rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    have hr : ‖(Matrix.of h).det‖ ^ (-(2 : ℝ)) = ‖(Matrix.of h).det‖⁻¹ * ‖(Matrix.of h).det‖⁻¹ := by
      rw [Real.rpow_neg (norm_nonneg _), Real.rpow_two, sq, mul_inv]
    beta_reduce
    rw [hJ, W2, hdet, ph_inv, hr, norm_inv]
    push_cast
    ring

end GlobalTheory.CompanionTheory.SecFubini
