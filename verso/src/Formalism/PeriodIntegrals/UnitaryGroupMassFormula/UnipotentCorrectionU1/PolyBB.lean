import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.PolyBA

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section pb2

variable {k r : ℕ}

/- English proof (translation)
Unfold `B.gN`. Establish `h1 : ‖M i j‖ ^ 2 ≤ ∑ a, ∑ b, Complex.normSq (M a b)`. Rewrite using `[← Complex.normSq_eq_norm_sq]`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
lemma pb_entry_le_gN (M : B.Mat k r) (i j : Fin (2 * r + k + 1)) : ‖M i j‖ ≤ B.gN M := by
  unfold B.gN
  have h1 : ‖M i j‖ ^ 2 ≤ ∑ a, ∑ b, Complex.normSq (M a b) := by
    rw [← Complex.normSq_eq_norm_sq]
    calc Complex.normSq (M i j) ≤ ∑ b, Complex.normSq (M i b) :=
          Finset.single_le_sum (f := fun b => Complex.normSq (M i b))
            (fun b _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ a, ∑ b, Complex.normSq (M a b) :=
          Finset.single_le_sum (f := fun a => ∑ b, Complex.normSq (M a b))
            (fun a _ => Finset.sum_nonneg fun b _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  calc ‖M i j‖ = Real.sqrt (‖M i j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt h1

/- English proof (translation)
Establish `h0 : 0 ≤ B.gN g` using `by unfold B.gN; positivity`. Conclude with `(Matrix.norm_le_iff h0).2 (fun i j => pb_entry_le_gN g i j)`.
-/
lemma pb_sup_le_gN (g : B.Mat k r) : ‖g‖ ≤ B.gN g := by
  have h0 : 0 ≤ B.gN g := by unfold B.gN; positivity
  exact (Matrix.norm_le_iff h0).2 (fun i j => pb_entry_le_gN g i j)

/- English proof (translation)
Rewrite using `[Matrix.norm_le_iff (by positivity)]`. Introduce `i j`. Rewrite using `[Matrix.mul_apply]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul]`.

Conclude with `mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm A) (Matrix.norm_entry_le_entrywise_sup_norm A') (norm_nonneg _) (norm_nonneg _)`. Use `_ = _ := by simp`.
-/
lemma pb_mul_norm_le (A A' : B.Mat k r) : ‖A * A'‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (‖A‖ * ‖A'‖) := by
  rw [Matrix.norm_le_iff (by positivity)]
  intro i j
  rw [Matrix.mul_apply]
  calc ‖∑ l, A i l * A' l j‖ ≤ ∑ l, ‖A i l * A' l j‖ := norm_sum_le _ _
    _ ≤ ∑ _l : Fin (2 * r + k + 1), ‖A‖ * ‖A'‖ := Finset.sum_le_sum fun l _ => by
        rw [norm_mul]
        exact mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm A)
          (Matrix.norm_entry_le_entrywise_sup_norm A') (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp

/- English proof (translation)
Establish `hX : ‖x.2‖ ≤ 1` using `(Matrix.norm_le_iff zero_le_one).2 hx.2`. Unfold `dirL`. Use `split_ifs`. Use `show ‖-x.2 * g‖ ≤ _`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[norm_neg]`. Conclude with `mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg _) hX) (by positivity)`. Use `first`. Consider the case `show ‖g * x.2‖ ≤ _`. Combine the equalities or inequalities in the displayed calculation.

Consider the case `(unfold mulRightRealCLM; done)`.
-/
lemma pb_dirL_le {x : Bool × B.Mat k r} (hx : B.unitLie k r x.2) (g : B.Mat k r) :
    ‖dirL x g‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * ‖g‖ := by
  have hX : ‖x.2‖ ≤ 1 := (Matrix.norm_le_iff zero_le_one).2 hx.2
  unfold dirL
  split_ifs
  · show ‖-x.2 * g‖ ≤ _
    calc ‖-x.2 * g‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (‖-x.2‖ * ‖g‖) := pb_mul_norm_le _ _
      _ ≤ _ := by
        rw [norm_neg]
        exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg _) hX) (by positivity)
  · first
    | show ‖g * x.2‖ ≤ _
      calc ‖g * x.2‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (‖g‖ * ‖x.2‖) := pb_mul_norm_le _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (norm_nonneg _) hX) (by positivity)
    | (unfold mulRightRealCLM; done)

/- English proof (translation)
Establish `hD : ∀ (L : B.Mat k r →L[ℝ] ℂ) (x : Bool × B.Mat k r), Dx x (fun g => L g) = fun g => L (dirL x g)`. Introduce `L x`. Use function extensionality and compare the values at `g`. Rewrite using `[Dx_eq, dirL_apply]`. Conclude with `(L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (crv_hasDerivAt x g)).deriv`.

Proceed by induction on `w with`. Consider the case `nil`. Introduce `Λ c hc hΛ`. Use `⟨Λ, rfl, fun g => ?_⟩` and prove the remaining obligations. Simplify using `using hΛ g`.

Consider the case `cons x w ih`. Introduce `Λ c hc hΛ`. Take `⟨Λ₁, h₁, hb₁⟩` from `ih (fun y hy => hw y (by simp [hy])) Λ c hc hΛ`. Use `⟨Λ₁.comp (dirL x), ?_, fun g => ?_⟩` and prove the remaining obligations. Use `show Dx x (Dw w fun g => Λ g) = _`.

Rewrite using `[h₁, hD]`. Both sides reduce to the same expression. Establish `hx` using `hw x (by simp) g`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[List.length_cons, pow_succ]`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma pb_Dw_clm {K : ℝ} (hK : 0 ≤ K) (w : List (Bool × B.Mat k r))
    (hw : ∀ x ∈ w, ∀ g, ‖dirL x g‖ ≤ K * ‖g‖) :
    ∀ (Λ : B.Mat k r →L[ℝ] ℂ) (c : ℝ), 0 ≤ c → (∀ g, ‖Λ g‖ ≤ c * ‖g‖) → ∃ Λ' : B.Mat k r →L[ℝ] ℂ,
      Dw w (fun g => Λ g) = (fun g => Λ' g) ∧ ∀ g, ‖Λ' g‖ ≤ c * K ^ w.length * ‖g‖ := by
  have hD : ∀ (L : B.Mat k r →L[ℝ] ℂ) (x : Bool × B.Mat k r),
      Dx x (fun g => L g) = fun g => L (dirL x g) := by
    intro L x
    funext g
    rw [Dx_eq, dirL_apply]
    exact (L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (crv_hasDerivAt x g)).deriv
  induction w with
  | nil =>
    intro Λ c hc hΛ
    refine ⟨Λ, rfl, fun g => ?_⟩
    simpa using hΛ g
  | cons x w ih =>
    intro Λ c hc hΛ
    obtain ⟨Λ₁, h₁, hb₁⟩ := ih (fun y hy => hw y (by simp [hy])) Λ c hc hΛ
    refine ⟨Λ₁.comp (dirL x), ?_, fun g => ?_⟩
    · show Dx x (Dw w fun g => Λ g) = _
      rw [h₁, hD]
      rfl
    · have hx := hw x (by simp) g
      calc ‖(Λ₁.comp (dirL x)) g‖ = ‖Λ₁ (dirL x g)‖ := rfl
        _ ≤ c * K ^ w.length * ‖dirL x g‖ := hb₁ _
        _ ≤ c * K ^ w.length * (K * ‖g‖) :=
          mul_le_mul_of_nonneg_left hx (mul_nonneg hc (pow_nonneg hK _))
        _ = c * K ^ (x :: w).length * ‖g‖ := by
          rw [List.length_cons, pow_succ]
          ring

/- English proof (translation)
Use `⟨Λ.contDiff, fun n => ?_⟩` and prove the remaining obligations. Establish `hK1 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ)`. Conclude with `(by omega : 1 ≤ 2 * r + k + 1)` after adjusting the coercions. Use `⟨((2 * r + k + 1 : ℕ) : ℝ) ^ n, fun w hw hn g _ => ?_⟩` and prove the remaining obligations. Take `⟨Λ', hΛ', hb⟩` from `pb_Dw_clm (by linarith) w (fun x hx g => pb_dirL_le (hw x hx) g) Λ 1 zero_le_one hΛ`.

Rewrite using `[hΛ', Real.rpow_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[one_mul]`. Conclude with `mul_le_mul (pow_le_pow_right₀ hK1 hn) (pb_sup_le_gN g) (norm_nonneg _) (by positivity)`.
-/
lemma pb_clm (Λ : B.Mat k r →L[ℝ] ℂ) (hΛ : ∀ g, ‖Λ g‖ ≤ 1 * ‖g‖) : PG 1 (fun g => Λ g) := by
  refine ⟨Λ.contDiff, fun n => ?_⟩
  have hK1 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
  refine ⟨((2 * r + k + 1 : ℕ) : ℝ) ^ n, fun w hw hn g _ => ?_⟩
  obtain ⟨Λ', hΛ', hb⟩ := pb_Dw_clm (by linarith) w (fun x hx g => pb_dirL_le (hw x hx) g)
    Λ 1 zero_le_one hΛ
  rw [hΛ', Real.rpow_one]
  calc ‖Λ' g‖ ≤ 1 * ((2 * r + k + 1 : ℕ) : ℝ) ^ w.length * ‖g‖ := hb g
    _ ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ n * B.gN g := by
      rw [one_mul]
      exact mul_le_mul (pow_le_pow_right₀ hK1 hn) (pb_sup_le_gN g) (norm_nonneg _) (by positivity)

def pbCo (a b : Fin (2 * r + k + 1)) : B.Mat k r →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => g a b, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => by simp }

def pbCc (a b : Fin (2 * r + k + 1)) : B.Mat k r →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => star (g a b), map_add' := fun _ _ => by simp, map_smul' := fun _ _ => by simp }

def pbVar (g : B.Mat k r) : (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) → ℂ :=
  Sum.elim (fun x => g x.1 x.2) (fun x => star (g x.1 x.2))

/- English proof (translation)
Break down `i with ⟨a, b⟩ | ⟨a, b⟩` into its components or cases. Establish `e : (fun g : B.Mat k r => pbVar g (Sum.inl (a, b))) = fun g => pbCo a b g`. Use function extensionality and compare the values at `g`. Apply the tactic sequence `simp [pbVar, pbCo] <;> rfl`. Rewrite using `[e]`.

Use `pb_clm (pbCo a b) (fun g => ?_)` and prove the remaining obligations. Apply the tactic sequence `have e2 : pbCo a b g = g a b := by simp [pbCo] <;> rfl`. Rewrite using `[e2, one_mul]`. Conclude with `Matrix.norm_entry_le_entrywise_sup_norm g`. Establish `e : (fun g : B.Mat k r => pbVar g (Sum.inr (a, b))) = fun g => pbCc a b g`.

Use function extensionality and compare the values at `g`. Apply the tactic sequence `simp [pbVar, pbCc] <;> rfl`. Rewrite using `[e]`. Use `pb_clm (pbCc a b) (fun g => ?_)` and prove the remaining obligations. Apply the tactic sequence `have e2 : pbCc a b g = star (g a b) := by simp [pbCc] <;> rfl`.

Rewrite using `[e2, one_mul, norm_star]`. Conclude with `Matrix.norm_entry_le_entrywise_sup_norm g`.
-/
lemma pb_var (i : (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) :
    PG 1 (fun g : B.Mat k r => pbVar g i) := by
  rcases i with ⟨a, b⟩ | ⟨a, b⟩
  · have e : (fun g : B.Mat k r => pbVar g (Sum.inl (a, b))) = fun g => pbCo a b g := by
      funext g
      simp [pbVar, pbCo] <;> rfl
    rw [e]
    refine pb_clm (pbCo a b) (fun g => ?_)
    have e2 : pbCo a b g = g a b := by simp [pbCo] <;> rfl
    rw [e2, one_mul]
    exact Matrix.norm_entry_le_entrywise_sup_norm g
  · have e : (fun g : B.Mat k r => pbVar g (Sum.inr (a, b))) = fun g => pbCc a b g := by
      funext g
      simp [pbVar, pbCc] <;> rfl
    rw [e]
    refine pb_clm (pbCc a b) (fun g => ?_)
    have e2 : pbCc a b g = star (g a b) := by simp [pbCc] <;> rfl
    rw [e2, one_mul, norm_star]
    exact Matrix.norm_entry_le_entrywise_sup_norm g

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Establish `h : PG 0 (fun _ : B.Mat k r => (1 : ℂ))` using `pb_const 1`. Simplify using `using h`. Consider the case `succ m ih`.

Establish `h` using `pb_mul ih hf`. Establish `e1 : ((m + 1 : ℕ) : ℝ) * e = (m : ℝ) * e + e` using `by push_cast; ring`. Rewrite using `[e1]`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma pb_pow {e : ℝ} {f : B.Mat k r → ℂ} (hf : PG e f) (m : ℕ) : PG ((m : ℝ) * e) (fun g => f g ^ m) := by
  induction m with
  | zero =>
    have h : PG 0 (fun _ : B.Mat k r => (1 : ℂ)) := pb_const 1
    simpa using h
  | succ m ih =>
    have h := pb_mul ih hf
    have e1 : ((m + 1 : ℕ) : ℝ) * e = (m : ℝ) * e + e := by push_cast; ring
    rw [e1]
    convert h using 1
    funext g
    ring

/- English proof (translation)
Use `revert hF`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Introduce `_`. Establish `h : PG 0 (fun _ : B.Mat k r => (1 : ℂ))` using `pb_const 1`. Simplify using `using h`.

Introduce `a s ha ih hF`. Establish `h1` using `hF a (Finset.mem_insert_self a s)`. Establish `h2` using `ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))`. Rewrite using `[Finset.sum_insert ha]`. Use `pb_mul h1 h2 using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `g`. Rewrite using `[Finset.prod_insert ha]`.
-/
lemma pb_prod {ι : Type*} (s : Finset ι) (e : ι → ℝ) (F : ι → B.Mat k r → ℂ)
    (hF : ∀ i ∈ s, PG (e i) (F i)) : PG (∑ i ∈ s, e i) (fun g => ∏ i ∈ s, F i g) := by
  classical
  revert hF
  refine Finset.induction_on s ?_ ?_
  · intro _
    have h : PG 0 (fun _ : B.Mat k r => (1 : ℂ)) := pb_const 1
    simpa using h
  · intro a s ha ih hF
    have h1 := hF a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))
    rw [Finset.sum_insert ha]
    convert pb_mul h1 h2 using 1
    funext g
    rw [Finset.prod_insert ha]

/- English proof (translation)
Use `revert hF`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Introduce `_`. Establish `h : PG e (fun _ : B.Mat k r => (0 : ℂ))` using `pb_zero e`. Simplify using `using h`.

Introduce `a s ha ih hF`. Establish `h1` using `hF a (Finset.mem_insert_self a s)`. Establish `h2` using `ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))`. Use `pb_add h1 h2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`.

Rewrite using `[Finset.sum_insert ha]`.
-/
lemma pb_sum {ι : Type*} (s : Finset ι) {e : ℝ} (F : ι → B.Mat k r → ℂ)
    (hF : ∀ i ∈ s, PG e (F i)) : PG e (fun g => ∑ i ∈ s, F i g) := by
  classical
  revert hF
  refine Finset.induction_on s ?_ ?_
  · intro _
    have h : PG e (fun _ : B.Mat k r => (0 : ℂ)) := pb_zero e
    simpa using h
  · intro a s ha ih hF
    have h1 := hF a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))
    convert pb_add h1 h2 using 1
    funext g
    rw [Finset.sum_insert ha]

/- English proof (translation)
Take `⟨q, hq, hPq⟩` from `hP`. Establish `hfun : P = fun g => ∑ d ∈ q.support, q.coeff d * ∏ i ∈ d.support, pbVar g i ^ d i`. Use function extensionality and compare the values at `g`. Rewrite using `[hPq g, MvPolynomial.eval_eq]`. Both sides reduce to the same expression.

Rewrite using `[hfun]`. Use `pb_sum q.support (fun d g => q.coeff d * ∏ i ∈ d.support, pbVar g i ^ d i) (fun d hd => ?_)` and prove the remaining obligations. Establish `h1 : PG (∑ i ∈ d.support, ((d i : ℕ) : ℝ) * 1) (fun g => ∏ i ∈ d.support, pbVar g i ^ d i)` using `pb_prod d.support (fun i => ((d i : ℕ) : ℝ) * 1) (fun i g => pbVar g i ^ d i) (fun i _ => pb_pow (pb_var i) (d i))`. Establish `h0 : PG 0 (fun _ : B.Mat k r => q.coeff d)` using `pb_const _`. Establish `h2` using `pb_mul h0 h1`.

Use `pb_mono h2 ?_` and prove the remaining obligations. Establish `hdeg : (d.sum fun _ e => e) ≤ κ` using `(MvPolynomial.le_totalDegree hd).trans hq`. Establish `hs : (∑ i ∈ d.support, ((d i : ℕ) : ℝ) * 1) = ((d.sum fun _ e => e : ℕ) : ℝ)`. Simplify using `[Finsupp.sum]`. Rewrite using `[zero_add, hs]`.

Conclude with `hdeg` after adjusting the coercions.
-/
theorem pb_poly {κ : ℕ} {P : B.Mat k r → ℂ} (hP : IsPolyDeg κ P) : PG (κ : ℝ) P := by
  obtain ⟨q, hq, hPq⟩ := hP
  have hfun : P = fun g => ∑ d ∈ q.support, q.coeff d * ∏ i ∈ d.support, pbVar g i ^ d i := by
    funext g
    rw [hPq g, MvPolynomial.eval_eq]
    rfl
  rw [hfun]
  refine pb_sum q.support (fun d g => q.coeff d * ∏ i ∈ d.support, pbVar g i ^ d i) (fun d hd => ?_)
  have h1 : PG (∑ i ∈ d.support, ((d i : ℕ) : ℝ) * 1) (fun g => ∏ i ∈ d.support, pbVar g i ^ d i) :=
    pb_prod d.support (fun i => ((d i : ℕ) : ℝ) * 1) (fun i g => pbVar g i ^ d i)
      (fun i _ => pb_pow (pb_var i) (d i))
  have h0 : PG 0 (fun _ : B.Mat k r => q.coeff d) := pb_const _
  have h2 := pb_mul h0 h1
  refine pb_mono h2 ?_
  have hdeg : (d.sum fun _ e => e) ≤ κ := (MvPolynomial.le_totalDegree hd).trans hq
  have hs : (∑ i ∈ d.support, ((d i : ℕ) : ℝ) * 1) = ((d.sum fun _ e => e : ℕ) : ℝ) := by
    simp [Finsupp.sum]
  rw [zero_add, hs]
  exact_mod_cast hdeg

end pb2

end PI.UnitaryCorollaryDerivatives
