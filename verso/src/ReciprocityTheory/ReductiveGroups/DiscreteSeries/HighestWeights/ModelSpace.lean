import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelFun
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.KFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.InhabA

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def rtr (ε : Fin n → Bool) (k : KG ε) : (KG ε → ℂ) →ₗ[ℂ] (KG ε → ℂ) where
  toFun f := fun x => f (x * k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/- English proof (translation)
Use function extensionality and compare the values at `x`. Use `show f (x * (k₁ * k₂)) = f (x * k₁ * k₂)`. Rewrite using `[mul_assoc]`.
-/
theorem rtr_mul (ε : Fin n → Bool) (k₁ k₂ : KG ε) (f : KG ε → ℂ) : rtr ε (k₁ * k₂) f = rtr ε k₁ (rtr ε k₂ f) := by
  funext x
  show f (x * (k₁ * k₂)) = f (x * k₁ * k₂)
  rw [mul_assoc]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Use `show f (x * 1) = f x`. Rewrite using `[mul_one]`.
-/
theorem rtr_one (ε : Fin n → Bool) (f : KG ε → ℂ) : rtr ε 1 f = f := by
  funext x
  show f (x * 1) = f x
  rw [mul_one]

def Vsp (ε : Fin n → Bool) (m : Fin n → ℤ) : Submodule ℂ (KG ε → ℂ) :=
  Submodule.span ℂ (Set.range fun k : KG ε => rtr ε k (f0K ε m))

/- English proof (translation)
Establish `h : rtr ε 1 (f0K ε m) ∈ Vsp ε m` using `Submodule.subset_span ⟨1, rfl⟩`. Rewrite `h` using `[rtr_one]`. Then use the resulting hypothesis.
-/
theorem highest_weight_fn_mem_space (ε : Fin n → Bool) (m : Fin n → ℤ) : f0K ε m ∈ Vsp ε m := by
  have h : rtr ε 1 (f0K ε m) ∈ Vsp ε m := Submodule.subset_span ⟨1, rfl⟩
  rwa [rtr_one] at h

/- English proof (translation)
Establish `h : Vsp ε m ≤ (Vsp ε m).comap (rtr ε k)`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨k', rfl⟩`. Use `show rtr ε k (rtr ε k' (f0K ε m)) ∈ Vsp ε m`. Rewrite using `[← rtr_mul]`.

Conclude with `Submodule.subset_span ⟨k * k', rfl⟩`. Conclude with `h hf`.
-/
theorem rtr_mem (ε : Fin n → Bool) (m : Fin n → ℤ) (k : KG ε) {f : KG ε → ℂ} (hf : f ∈ Vsp ε m) :
    rtr ε k f ∈ Vsp ε m := by
  have h : Vsp ε m ≤ (Vsp ε m).comap (rtr ε k) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k', rfl⟩
    show rtr ε k (rtr ε k' (f0K ε m)) ∈ Vsp ε m
    rw [← rtr_mul]
    exact Submodule.subset_span ⟨k * k', rfl⟩
  exact h hf

def evalK (ε : Fin n → Bool) : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] (KG ε → ℂ) :=
  MvPolynomial.aeval fun p : Fin n × Fin n => fun k : KG ε => toMK k p.1 p.2

def polyK (ε : Fin n → Bool) (D : ℕ) : Submodule ℂ (KG ε → ℂ) :=
  (MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ D).map (evalK ε).toLinearMap

/- English proof (translation)
Proceed by induction on `Q using MvPolynomial.induction_on`. Use `next a => simp [evalK]`. Use `next p q hp hq => rw [map_add, map_add, Pi.add_apply, hp, hq]`. Use `next p i hp =>`. Rewrite using `[map_mul, map_mul, Pi.mul_apply, hp]`.

Simplify using `[evalK]`.
-/
theorem evalK_apply (ε : Fin n → Bool) (Q : MvPolynomial (Fin n × Fin n) ℂ) (x : KG ε) :
    evalK ε Q x = MvPolynomial.aeval (fun p : Fin n × Fin n => toMK x p.1 p.2) Q := by
  induction Q using MvPolynomial.induction_on
  next a => simp [evalK]
  next p q hp hq => rw [map_add, map_add, Pi.add_apply, hp, hq]
  next p i hp =>
    rw [map_mul, map_mul, Pi.mul_apply, hp]
    simp [evalK]

def rsub (ε : Fin n → Bool) (k : KG ε) : Fin n × Fin n → MvPolynomial (Fin n × Fin n) ℂ :=
  fun p => ∑ l, MvPolynomial.X (p.1, l) * MvPolynomial.C (toMK k l p.2)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toMK_mul' (ε : Fin n → Bool) (x k : KG ε) : toMK (x * k) = toMK x * toMK k := rfl

/- English proof (translation)
Use function extensionality and compare the values at `x`. Use `show evalK ε Q (x * k) = evalK ε (MvPolynomial.bind₁ (rsub ε k) Q) x`. Rewrite using `[evalK_apply, evalK_apply, MvPolynomial.aeval_bind₁]`. Use `congrArg (fun g => MvPolynomial.aeval g Q) ?_` and prove the remaining obligations. Use function extensionality and compare the values at `p`.

Simplify using `[rsub, toMK_mul', Matrix.mul_apply]`.
-/
theorem rtr_evalK (ε : Fin n → Bool) (k : KG ε) (Q : MvPolynomial (Fin n × Fin n) ℂ) :
    rtr ε k (evalK ε Q) = evalK ε (MvPolynomial.bind₁ (rsub ε k) Q) := by
  funext x
  show evalK ε Q (x * k) = evalK ε (MvPolynomial.bind₁ (rsub ε k) Q) x
  rw [evalK_apply, evalK_apply, MvPolynomial.aeval_bind₁]
  refine congrArg (fun g => MvPolynomial.aeval g Q) ?_
  funext p
  simp [rsub, toMK_mul', Matrix.mul_apply]

/- English proof (translation)
Simplify using `only [rsub]`. Use `(MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun l _ => ?_)` and prove the remaining obligations. Use `(MvPolynomial.totalDegree_mul _ _).trans ?_` and prove the remaining obligations. Simplify using `[MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]`.
-/
theorem totalDegree_rsub (ε : Fin n → Bool) (k : KG ε) (p : Fin n × Fin n) :
    (rsub ε k p).totalDegree ≤ 1 := by
  simp only [rsub]
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun l _ => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  simp [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]

/- English proof (translation)
Use `conv_lhs => rw [Q.as_sum]`. Rewrite using `[map_sum]`. Use `(MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun d hd => ?_)` and prove the remaining obligations. Rewrite using `[MvPolynomial.bind₁_monomial]`. Use `(MvPolynomial.totalDegree_mul _ _).trans ?_` and prove the remaining obligations.

Rewrite using `[MvPolynomial.totalDegree_C, zero_add]`. Use `(MvPolynomial.totalDegree_finset_prod _ _).trans ?_` and prove the remaining obligations. Use `le_trans ?_ (MvPolynomial.le_totalDegree hd)` and prove the remaining obligations. Rewrite using `[Finsupp.sum]`. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations.

Use `(MvPolynomial.totalDegree_pow _ _).trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem totalDegree_bind₁_le {σ τ : Type*} (g : σ → MvPolynomial τ ℂ) (hg : ∀ i, (g i).totalDegree ≤ 1)
    (Q : MvPolynomial σ ℂ) : (MvPolynomial.bind₁ g Q).totalDegree ≤ Q.totalDegree := by
  classical
  conv_lhs => rw [Q.as_sum]
  rw [map_sum]
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun d hd => ?_)
  rw [MvPolynomial.bind₁_monomial]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finset_prod _ _).trans ?_
  refine le_trans ?_ (MvPolynomial.le_totalDegree hd)
  rw [Finsupp.sum]
  refine Finset.sum_le_sum fun i _ => ?_
  refine (MvPolynomial.totalDegree_pow _ _).trans ?_
  calc d i * (g i).totalDegree ≤ d i * 1 := Nat.mul_le_mul_left _ (hg i)
    _ = d i := mul_one _

/- English proof (translation)
Rewrite using `[rtr_evalK]`. Conclude with `Submodule.mem_map_of_mem ((MvPolynomial.mem_restrictTotalDegree ..).mpr (totalDegree_bind₁_le _ (totalDegree_rsub ε k) Q))`.
-/
theorem rtr_polyK (ε : Fin n → Bool) (k : KG ε) (Q : MvPolynomial (Fin n × Fin n) ℂ) :
    rtr ε k (evalK ε Q) ∈ polyK ε Q.totalDegree := by
  rw [rtr_evalK]
  exact Submodule.mem_map_of_mem ((MvPolynomial.mem_restrictTotalDegree ..).mpr
    (totalDegree_bind₁_le _ (totalDegree_rsub ε k) Q))

def f0P (ε : Fin n → Bool) (m : Fin n → ℤ) : MvPolynomial (Fin n × Fin n) ℂ :=
  ∏ a, ((Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).submatrix
    (fun b : {b : Fin n // ε b = ε a ∧ b ≤ a} => (b : Fin n))
    (fun b : {b : Fin n // ε b = ε a ∧ b ≤ a} => (b : Fin n))).det ^ (mexp ε m a).toNat

/- English proof (translation)
Use function extensionality and compare the values at `k`. Rewrite using `[evalK_apply]`. Use `show _ = f0 ε m (toMK k)`. Simplify using `only [f0P, f0, blkMinor, map_prod, map_pow]`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations.

Use `congr 1`. Rewrite using `[AlgHom.map_det]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `[Matrix.mvPolynomialX]`.
-/
theorem evalK_f0P (ε : Fin n → Bool) (m : Fin n → ℤ) : evalK ε (f0P ε m) = f0K ε m := by
  funext k
  rw [evalK_apply]
  show _ = f0 ε m (toMK k)
  simp only [f0P, f0, blkMinor, map_prod, map_pow]
  refine Finset.prod_congr rfl fun a _ => ?_
  congr 1
  rw [AlgHom.map_det]
  congr 1
  ext i j
  simp [Matrix.mvPolynomialX]

/- English proof (translation)
Use `⟨(f0P ε m).totalDegree, Submodule.span_le.mpr ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Use `show rtr ε k (f0K ε m) ∈ polyK ε _`. Rewrite using `[← evalK_f0P]`. Conclude with `rtr_polyK ε k (f0P ε m)`.
-/
theorem Vsp_le_polyK (ε : Fin n → Bool) (m : Fin n → ℤ) : ∃ D : ℕ, Vsp ε m ≤ polyK ε D := by
  refine ⟨(f0P ε m).totalDegree, Submodule.span_le.mpr ?_⟩
  rintro _ ⟨k, rfl⟩
  show rtr ε k (f0K ε m) ∈ polyK ε _
  rw [← evalK_f0P]
  exact rtr_polyK ε k (f0P ε m)

/- English proof (translation)
Take `⟨D, hD⟩` from `Vsp_le_polyK ε m`. Use `haveI : FiniteDimensional ℂ (polyK ε D) := by`. Unfold `polyK`. Use `infer_instance`. Conclude with `Submodule.finiteDimensional_of_le hD`.
-/
theorem finiteDimensional_Vsp (ε : Fin n → Bool) (m : Fin n → ℤ) : FiniteDimensional ℂ (Vsp ε m) := by
  obtain ⟨D, hD⟩ := Vsp_le_polyK ε m
  haveI : FiniteDimensional ℂ (polyK ε D) := by
    unfold polyK
    infer_instance
  exact Submodule.finiteDimensional_of_le hD

/- English proof (translation)
Proceed by induction on `Q using MvPolynomial.induction_on`. Use `next a => simp`. Use `next p q hp hq =>`. Simplify using `only [map_add]`. Conclude with `hp.add hq`.

Use `next p i hp =>`. Establish `hX : Differentiable ℂ (fun M : Matrix (Fin n) (Fin n) ℂ => M i.1 i.2)` using `by fun_prop`. Simplify using `only [map_mul, MvPolynomial.aeval_X]`. Conclude with `hp.mul hX`.
-/
theorem differentiable_aeval_entries (Q : MvPolynomial (Fin n × Fin n) ℂ) :
    Differentiable ℂ (fun M : Matrix (Fin n) (Fin n) ℂ =>
      MvPolynomial.aeval (fun p : Fin n × Fin n => M p.1 p.2) Q) := by
  induction Q using MvPolynomial.induction_on
  next a => simp
  next p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  next p i hp =>
    have hX : Differentiable ℂ (fun M : Matrix (Fin n) (Fin n) ℂ => M i.1 i.2) := by
      fun_prop
    simp only [map_mul, MvPolynomial.aeval_X]
    exact hp.mul hX

/- English proof (translation)
Take `⟨D, hD⟩` from `Vsp_le_polyK ε m`. Establish `h' : f ∈ (MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ D).map (evalK ε).toLinearMap` using `hD hf`. Take `⟨Q, -, rfl⟩` from `Submodule.mem_map.mp h'`. Conclude with `⟨fun M => MvPolynomial.aeval (fun p : Fin n × Fin n => M p.1 p.2) Q, differentiable_aeval_entries Q, fun k => evalK_apply ε Q k⟩`.
-/
theorem Vsp_holo (ε : Fin n → Bool) (m : Fin n → ℤ) {f : KG ε → ℂ} (hf : f ∈ Vsp ε m) :
    ∃ F : Matrix (Fin n) (Fin n) ℂ → ℂ, Differentiable ℂ F ∧ ∀ k, f k = F (toMK k) := by
  obtain ⟨D, hD⟩ := Vsp_le_polyK ε m
  have h' : f ∈ (MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ D).map (evalK ε).toLinearMap := hD hf
  obtain ⟨Q, -, rfl⟩ := Submodule.mem_map.mp h'
  exact ⟨fun M => MvPolynomial.aeval (fun p : Fin n × Fin n => M p.1 p.2) Q,
    differentiable_aeval_entries Q, fun k => evalK_apply ε Q k⟩

/- English proof (translation)
Take `⟨F, hF, hfF⟩` from `Vsp_holo ε m hf`. Establish `hfe : f = fun k => F (toMK k)` using `funext hfF`. Rewrite using `[hfe]`. Use `hF.continuous.comp ?_` and prove the remaining obligations. Use `fun_prop`.
-/
theorem continuous_of_mem_Vsp (ε : Fin n → Bool) (m : Fin n → ℤ) {f : KG ε → ℂ} (hf : f ∈ Vsp ε m) :
    Continuous f := by
  obtain ⟨F, hF, hfF⟩ := Vsp_holo ε m hf
  have hfe : f = fun k => F (toMK k) := funext hfF
  rw [hfe]
  refine hF.continuous.comp ?_
  fun_prop

/- English proof (translation)
Establish `hc : HasDerivAt (fun t : ℝ => toMK (kcurve ε X t)) X 0`. Establish `hk : ∀ t : ℝ, toMK (kcurve ε X t) = NormedSpace.exp ((t : ℝ) • X)` using `fun t => by`. Unfold `kcurve`. Rewrite using `[dif_pos hX, Classical.choose_spec (exists_curve ε hX) t, Complex.coe_smul]`. Simplify using `only [hk]`.

Use `letI iR : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing`. Use `letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra`. Use `letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℝ ℂ _`. Use `haveI : @CompleteSpace (Matrix (Fin n) (Fin n) ℂ) (@PseudoMetricSpace.toUniformSpace _ (@MetricSpace.toPseudoMetricSpace _ (@NormedRing.toMetricSpace _ iR))) := by`. Conclude with `FiniteDimensional.complete ℂ _`.

Establish `h` using `hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)`. Rewrite `h` using `[zero_smul, NormedSpace.exp_zero, one_mul]`. Conclude with `h`. Set `L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ` to `LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ (toMK x))`. Establish `hin : HasDerivAt (fun t : ℝ => L (toMK (kcurve ε X t))) (L X) 0` using `L.hasFDerivAt.comp_hasDerivAt 0 hc`.

Establish `h0 : toMK (kcurve ε X 0) = 1`. Unfold `kcurve`. Rewrite using `[dif_pos hX, Classical.choose_spec (exists_curve ε hX) 0]`. Simplify using the standard rewrite rules. Establish `hLx : L (toMK (kcurve ε X 0)) = toMK x`.

Rewrite using `[h0]`. Conclude with `mul_one _`. Establish `hF'` using `((hF (toMK x)).hasFDerivAt.restrictScalars ℝ)`. Rewrite `hF'` using `[← hLx]`. Establish `hcomp` using `hF'.comp_hasDerivAt (0 : ℝ) hin`.

Establish `hfun : (fun t : ℝ => f (x * kcurve ε X t)) = fun t => F (L (toMK (kcurve ε X t)))`. Use function extensionality and compare the values at `t`. Rewrite using `[hfF, toMK_mul']`. Both sides reduce to the same expression. Rewrite using `[hfun]`.

Rewrite `hcomp` using `[hLx]`. Conclude with `hcomp`.
-/
theorem hasDerivAt_of_mem_Vsp (ε : Fin n → Bool) (m : Fin n → ℤ) {f : KG ε → ℂ} (hf : f ∈ Vsp ε m)
    {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : Differentiable ℂ F) (hfF : ∀ k, f k = F (toMK k))
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (x : KG ε) :
    HasDerivAt (fun t : ℝ => f (x * kcurve ε X t)) (fderiv ℂ F (toMK x) (toMK x * X)) 0 := by
  have hc : HasDerivAt (fun t : ℝ => toMK (kcurve ε X t)) X 0 := by
    have hk : ∀ t : ℝ, toMK (kcurve ε X t) = NormedSpace.exp ((t : ℝ) • X) := fun t => by
       unfold kcurve
       rw [dif_pos hX, Classical.choose_spec (exists_curve ε hX) t, Complex.coe_smul]
    simp only [hk]
    letI iR : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
    letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℝ ℂ _
    haveI : @CompleteSpace (Matrix (Fin n) (Fin n) ℂ)
        (@PseudoMetricSpace.toUniformSpace _ (@MetricSpace.toPseudoMetricSpace _ (@NormedRing.toMetricSpace _ iR))) := by
      exact FiniteDimensional.complete ℂ _
    have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
    exact h
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ (toMK x))
  have hin : HasDerivAt (fun t : ℝ => L (toMK (kcurve ε X t))) (L X) 0 :=
    L.hasFDerivAt.comp_hasDerivAt 0 hc
  have h0 : toMK (kcurve ε X 0) = 1 := by
    unfold kcurve
    rw [dif_pos hX, Classical.choose_spec (exists_curve ε hX) 0]
    simp
  have hLx : L (toMK (kcurve ε X 0)) = toMK x := by
    rw [h0]
    exact mul_one _
  have hF' := ((hF (toMK x)).hasFDerivAt.restrictScalars ℝ)
  rw [← hLx] at hF'
  have hcomp := hF'.comp_hasDerivAt (0 : ℝ) hin
  have hfun : (fun t : ℝ => f (x * kcurve ε X t)) = fun t => F (L (toMK (kcurve ε X t))) := by
    funext t
    rw [hfF, toMK_mul']
    rfl
  rw [hfun]
  rw [hLx] at hcomp
  exact hcomp

end ReciprocityTheory.ChartRestriction.DS.HW
