import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.FormalDegreeFormula.ModelFunctionsMultiply
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelTwist

noncomputable section

open Matrix
open scoped InnerProductSpace

namespace PositivityTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HW

variable {n : ℕ}

def twChi {ε : Fin n → Bool} (c : ℤ) (k : KG ε) : ℂ := (toMK k).det ^ c

/- English proof (translation)
Use `show (toMK (1 : KG ε)).det ^ c = 1`. Rewrite using `[show toMK (1 : KG ε) = 1 from rfl, Matrix.det_one, _root_.one_zpow]`.
-/
theorem twChi_one {ε : Fin n → Bool} (c : ℤ) : twChi (ε := ε) c 1 = 1 := by
  show (toMK (1 : KG ε)).det ^ c = 1
  rw [show toMK (1 : KG ε) = 1 from rfl, Matrix.det_one, _root_.one_zpow]

/- English proof (translation)
Use `show (toMK (x * y)).det ^ c = (toMK x).det ^ c * (toMK y).det ^ c`. Rewrite using `[show toMK (x * y) = toMK x * toMK y from rfl, Matrix.det_mul, mul_zpow]`.
-/
theorem twChi_mul {ε : Fin n → Bool} (c : ℤ) (x y : KG ε) : twChi c (x * y) = twChi c x * twChi c y := by
  show (toMK (x * y)).det ^ c = (toMK x).det ^ c * (toMK y).det ^ c
  rw [show toMK (x * y) = toMK x * toMK y from rfl, Matrix.det_mul, mul_zpow]

/- English proof (translation)
The claim follows from `zpow_ne_zero _ (twist_det_ne k)`.
-/
theorem twChi_ne {ε : Fin n → Bool} (c : ℤ) (k : KG ε) : twChi c k ≠ 0 := zpow_ne_zero _ (twist_det_ne k)

/- English proof (translation)
Establish `h` using `twist_zpow_star k c`. Establish `h2 : ‖twChi c k‖ ^ 2 = 1`. Use `congrArg norm h` as an intermediate fact. Rewrite `this` using `[norm_mul, norm_star, norm_one]`. Unfold `twChi`.

Use polynomial arithmetic with `[this]`. Establish `h3 : 0 ≤ ‖twChi c k‖` using `norm_nonneg _`. Use polynomial arithmetic with `[h2, h3]`.
-/
theorem norm_twChi {ε : Fin n → Bool} (c : ℤ) (k : KG ε) : ‖twChi c k‖ = 1 := by
  have h := twist_zpow_star k c
  have h2 : ‖twChi c k‖ ^ 2 = 1 := by
    have := congrArg norm h
    rw [norm_mul, norm_star, norm_one] at this
    unfold twChi
    nlinarith [this]
  have h3 : 0 ≤ ‖twChi c k‖ := norm_nonneg _
  nlinarith [h2, h3]

/- English proof (translation)
Use `show ((T.τ 1 : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) = 1`. Rewrite using `[map_one]`. Both sides reduce to the same expression.
-/
theorem kop_one {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) : T.op 1 = 1 := by
  show ((T.τ 1 : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) = 1
  rw [map_one]; rfl

/- English proof (translation)
Use `show ((T.τ (x * y) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) = _`. Rewrite using `[map_mul]`. Both sides reduce to the same expression.
-/
theorem kop_mul {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (x y : KG ε) : T.op (x * y) = T.op x * T.op y := by
  show ((T.τ (x * y) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) = _
  rw [map_mul]; rfl

def twTau {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (c : ℤ) : KG ε →* unitary (T.V →L[ℂ] T.V) where
  toFun k := ⟨twChi c k • T.op k, twist_smul_mem_unitary (twist_zpow_star k c) (T.τ k).2⟩
  map_one' := by
    apply Subtype.ext
    show twChi c 1 • T.op 1 = 1
    rw [twChi_one, one_smul, kop_one]
  map_mul' := by
    intro x y
    apply Subtype.ext
    show twChi c (x * y) • T.op (x * y) = (twChi c x • T.op x) * (twChi c y • T.op y)
    rw [twChi_mul, smul_mul_smul_comm, kop_mul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem twTau_apply {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (c : ℤ) (k : KG ε) :
    ((twTau T c k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) = twChi c k • T.op k := rfl

/- English proof (translation)
Establish `hK : Continuous (fun k : KG ε => toMK k)` using `(continuous_toM _).comp continuous_subtype_val`. Establish `hχc : Continuous (twChi (ε` using `ε) c) := (hK.matrix_det).zpow₀ c (fun k => Or.inl (twist_det_ne k))`. Establish `hop : Continuous (fun k : KG ε => T.op k)` using `continuous_subtype_val.comp T.cont`. Conclude with `Continuous.subtype_mk (hχc.smul hop) _`.
-/
theorem twTau_cont {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (c : ℤ) : Continuous (twTau T c) := by
  have hK : Continuous (fun k : KG ε => toMK k) := (continuous_toM _).comp continuous_subtype_val
  have hχc : Continuous (twChi (ε := ε) c) := (hK.matrix_det).zpow₀ c (fun k => Or.inl (twist_det_ne k))
  have hop : Continuous (fun k : KG ε => T.op k) := continuous_subtype_val.comp T.cont
  exact Continuous.subtype_mk (hχc.smul hop) _

def twD {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (c : ℤ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (T.V →L[ℂ] T.V) :=
  T.dτ + LinearMap.smulRight (Matrix.traceLinearMap (Fin n) ℂ ℂ) ((c : ℂ) • (1 : T.V →L[ℂ] T.V))

/- English proof (translation)
Apply `T.irred W` to reduce the goal to its premises. Introduce `k v hv`. Establish `h` using `W.smul_mem (twChi c k)⁻¹ (hW k v hv)`. Use `h using 1` and compare the differences between its conclusion and the goal. Rewrite using `[twTau_apply, ContinuousLinearMap.smul_apply, smul_smul, inv_mul_cancel₀ (twChi_ne c k), one_smul]`.
-/
theorem twTau_irred {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (c : ℤ) (W : Submodule ℂ T.V)
    (hW : ∀ k : KG ε, ∀ v ∈ W, ((twTau T c k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) v ∈ W) : W = ⊥ ∨ W = ⊤ := by
  apply T.irred W
  intro k v hv
  have h := W.smul_mem (twChi c k)⁻¹ (hW k v hv)
  convert h using 1
  rw [twTau_apply, ContinuousLinearMap.smul_apply, smul_smul, inv_mul_cancel₀ (twChi_ne c k), one_smul]

/- English proof (translation)
Establish `hT` using `T.hasDeriv X hX γ hγ`. Establish `h0 : γ 0 = 1` using `twist_toMK_inj (by`. Rewrite using `[hγ 0, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero]`. Use the proof step `rfl)`. Establish `hD` using `twist_hasDerivAt_det_exp X`.

Establish `hD0 : (NormedSpace.exp (((0 : ℝ) : ℂ) • X)).det = 1`. Rewrite using `[Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.det_one]`. Establish `hZ : HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)).det ^ c) ((c : ℂ) * X.trace) 0`. Establish `h` using `(hasDerivAt_zpow c _ (Or.inl (by rw [hD0]; exact one_ne_zero))).comp (0 : ℝ) hD`. Rewrite `h` using `[hD0, _root_.one_zpow, mul_one]`.

Conclude with `h`. Establish `hP` using `hZ.smul hT`. Establish `e : (fun t => ((twTau T c (γ t) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V)) = (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)).det ^ c • T.op (γ t))`. Use function extensionality and compare the values at `t`. Rewrite using `[twTau_apply]`.

Use `show (toMK (γ t)).det ^ c • T.op (γ t) = _`. Rewrite using `[hγ t]`. Rewrite using `[e]`. Use `HasDerivAt.congr_deriv hP ?_` and prove the remaining obligations. Rewrite using `[hD0, _root_.one_zpow, one_smul, h0, map_one]`.

Use `show T.dτ X + ((c : ℂ) * X.trace) • (1 : T.V →L[ℂ] T.V) = T.dτ X + X.trace • ((c : ℂ) • (1 : T.V →L[ℂ] T.V))`. Rewrite using `[smul_smul, mul_comm]`.
-/
theorem twTau_hasDeriv {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (c : ℤ) (X : Matrix (Fin n) (Fin n) ℂ)
    (hX : inK ε X) (γ : ℝ → KG ε) (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) :
    HasDerivAt (fun t => ((twTau T c (γ t) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V)) (twD T c X) 0 := by
  have hT := T.hasDeriv X hX γ hγ
  have h0 : γ 0 = 1 := twist_toMK_inj (by
    rw [hγ 0, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero]; rfl)
  have hD := twist_hasDerivAt_det_exp X
  have hD0 : (NormedSpace.exp (((0 : ℝ) : ℂ) • X)).det = 1 := by
    rw [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.det_one]
  have hZ : HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)).det ^ c) ((c : ℂ) * X.trace) 0 := by
    have h := (hasDerivAt_zpow c _ (Or.inl (by rw [hD0]; exact one_ne_zero))).comp (0 : ℝ) hD
    rw [hD0, _root_.one_zpow, mul_one] at h
    exact h
  have hP := hZ.smul hT
  have e : (fun t => ((twTau T c (γ t) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V)) =
      (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)).det ^ c • T.op (γ t)) := by
    funext t
    rw [twTau_apply]
    show (toMK (γ t)).det ^ c • T.op (γ t) = _
    rw [hγ t]
  rw [e]
  refine HasDerivAt.congr_deriv hP ?_
  rw [hD0, _root_.one_zpow, one_smul, h0, map_one]
  show T.dτ X + ((c : ℂ) * X.trace) • (1 : T.V →L[ℂ] T.V) = T.dτ X + X.trace • ((c : ℂ) • (1 : T.V →L[ℂ] T.V))
  rw [smul_smul, mul_comm]

/- English proof (translation)
Use `show (T.dτ (Matrix.single a a 1) + Matrix.trace (Matrix.single a a (1 : ℂ)) • ((c : ℂ) • (1 : T.V →L[ℂ] T.V))) T.w = (((Λ a + (c : ℝ) : ℝ)) : ℂ) • T.w`. Rewrite using `[ContinuousLinearMap.add_apply, T.w_wt, Matrix.trace_single_eq_same, one_smul, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]`. Use `push_cast`. Rewrite using `[add_smul]`.
-/
theorem twD_wt {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (c : ℤ) (a : Fin n) :
    twD T c (Matrix.single a a 1) T.w = (((Λ a + (c : ℝ) : ℝ)) : ℂ) • T.w := by
  show (T.dτ (Matrix.single a a 1) + Matrix.trace (Matrix.single a a (1 : ℂ)) •
    ((c : ℂ) • (1 : T.V →L[ℂ] T.V))) T.w = (((Λ a + (c : ℝ) : ℝ)) : ℂ) • T.w
  rw [ContinuousLinearMap.add_apply, T.w_wt, Matrix.trace_single_eq_same, one_smul,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
  push_cast
  rw [add_smul]

/- English proof (translation)
Use `show (T.dτ (Matrix.single a b 1) + Matrix.trace (Matrix.single a b (1 : ℂ)) • ((c : ℂ) • (1 : T.V →L[ℂ] T.V))) T.w = 0`. Rewrite using `[ContinuousLinearMap.add_apply, T.w_hw a b hab he, Matrix.trace_single_eq_of_ne (h := ne_of_lt hab), zero_smul, ContinuousLinearMap.zero_apply, add_zero]`.
-/
theorem twD_hw {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (c : ℤ) (a b : Fin n) (hab : a < b)
    (he : ε a = ε b) : twD T c (Matrix.single a b 1) T.w = 0 := by
  show (T.dτ (Matrix.single a b 1) + Matrix.trace (Matrix.single a b (1 : ℂ)) •
    ((c : ℂ) • (1 : T.V →L[ℂ] T.V))) T.w = 0
  rw [ContinuousLinearMap.add_apply, T.w_hw a b hab he, Matrix.trace_single_eq_of_ne (h := ne_of_lt hab),
    zero_smul, ContinuousLinearMap.zero_apply, add_zero]

def twistKType {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (c : ℤ) : KType ε (fun a => Λ a + (c : ℝ)) where
  V := T.V
  τ := twTau T c
  cont := twTau_cont T c
  irred := twTau_irred T c
  dτ := twD T c
  hasDeriv := twTau_hasDeriv T c
  w := T.w
  w_norm := T.w_norm
  w_wt := twD_wt T c
  w_hw := twD_hw T c

/- English proof (translation)
Use `show ‖⟪T.w, ((twTau T c k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) T.w⟫_ℂ‖ = ‖⟪T.w, T.op k T.w⟫_ℂ‖`. Rewrite using `[twTau_apply, ContinuousLinearMap.smul_apply, inner_smul_right, norm_mul, norm_twChi, one_mul]`.
-/
theorem cK_twistKType {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (c : ℤ) (k : KG ε) :
    cK (twistKType T c) k = cK T k := by
  show ‖⟪T.w, ((twTau T c k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) T.w⟫_ℂ‖ = ‖⟪T.w, T.op k T.w⟫_ℂ‖
  rw [twTau_apply, ContinuousLinearMap.smul_apply, inner_smul_right, norm_mul, norm_twChi, one_mul]

/- English proof (translation)
Introduce `_ _ _ T c` and use `⟨twistKType T c, cK_twistKType T c⟩`.
-/
theorem ckTwist : CkTwist := fun _ _ _ T c => ⟨twistKType T c, cK_twistKType T c⟩

/- English proof (translation)
Unfold `mexp`. Use `split_ifs with h`. Simplify using `only [Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Pi.add_apply]`.
-/
theorem mexp_add (ε : Fin n → Bool) (m₁ m₂ : Fin n → ℤ) (a : Fin n) :
    mexp ε (m₁ + m₂) a = mexp ε m₁ a + mexp ε m₂ a := by
  unfold mexp
  split_ifs with h
  · simp only [Pi.add_apply]; ring
  · simp only [Pi.add_apply]

/- English proof (translation)
Introduce `n ε m₁ m₂ h₁ h₂ k`. Unfold `f0K f0`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[mexp_add, Int.toNat_add (mexp_nonneg ε h₁ a) (mexp_nonneg ε h₂ a), pow_add]`.
-/
theorem model_functions_multiply : ModelFunctionsMultiply := by
  intro n ε m₁ m₂ h₁ h₂ k
  unfold f0K f0
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [mexp_add, Int.toNat_add (mexp_nonneg ε h₁ a) (mexp_nonneg ε h₂ a), pow_add]

end PositivityTheory.RgFd
