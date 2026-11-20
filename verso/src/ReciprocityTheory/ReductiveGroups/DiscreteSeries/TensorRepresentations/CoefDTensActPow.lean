import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HidaSetting
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TensorV
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Closure
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CoefCExpEntrySummable

noncomputable section

open Finset
open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def coefAm (dual : Bool) (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  cond dual (g⁻¹)ᵀ g

def coefBm (dual : Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  cond dual (-Xᵀ) X

/- English proof (translation)
Consider the cases of `dual`. Both sides reduce to the same expression. Simplify using `only [coefAm, coefBm, cond_true]`. Rewrite using `[← Matrix.exp_neg, ← Matrix.exp_transpose]`. Use `congr 1`.

Rewrite using `[Matrix.transpose_neg, Matrix.transpose_smul, smul_neg]`.
-/
theorem coefD_Am_exp (dual : Bool) (X : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) :
    coefAm dual (NormedSpace.exp ((s : ℂ) • X)) = NormedSpace.exp ((s : ℂ) • coefBm dual X) := by
  cases dual
  · rfl
  · simp only [coefAm, coefBm, cond_true]
    rw [← Matrix.exp_neg, ← Matrix.exp_transpose]
    congr 1
    rw [Matrix.transpose_neg, Matrix.transpose_smul, smul_neg]

section Alg

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

def coefPm (B : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ (Fin n → M) :=
  LinearMap.pi fun c => ∑ d, B c d • LinearMap.proj d

/- English proof (translation)
Simplify using `[coefPm, LinearMap.sum_apply]`.
-/
theorem coefPm_apply (B : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → M) (c : Fin n) :
    coefPm B u c = ∑ d, B c d • u d := by
  simp [coefPm, LinearMap.sum_apply]

/- English proof (translation)
Proceed by induction on `j generalizing c with`. Consider the case `zero`. Simplify using `only [pow_zero, Module.End.one_apply, Matrix.one_apply, ite_smul, one_smul, zero_smul]`. Rewrite using `[Finset.sum_ite_eq]`. Simplify using the standard rewrite rules.

Consider the case `succ j ih`. Rewrite using `[pow_succ', Module.End.mul_apply, coefPm_apply, pow_succ']`. Repeatedly rewrite using `[ih, Matrix.mul_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`.
-/
theorem coefPm_pow (B : Matrix (Fin n) (Fin n) ℂ) (j : ℕ) (u : Fin n → M) (c : Fin n) :
    ((coefPm (M := M) B) ^ j) u c = ∑ d, (B ^ j) c d • u d := by
  induction j generalizing c with
  | zero =>
    simp only [pow_zero, Module.End.one_apply, Matrix.one_apply, ite_smul, one_smul, zero_smul]
    rw [Finset.sum_ite_eq]
    simp
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, coefPm_apply, pow_succ']
    simp_rw [ih, Matrix.mul_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]

/- English proof (translation)
Proceed by induction on `k generalizing u with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ, Module.End.mul_apply, ih, diagOp_coord, ← Module.End.mul_apply, ← pow_succ]`.
-/
theorem coefD_diag_pow (A : Module.End ℂ M) (k : ℕ) (u : Fin n → M) (c : Fin n) :
    ((diagOp (n := n) A) ^ k) u c = (A ^ k) (u c) := by
  induction k generalizing u with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, diagOp_coord, ← Module.End.mul_apply, ← pow_succ]

/- English proof (translation)
Use `LinearMap.ext fun u => funext fun c => ?_` and prove the remaining obligations. Simplify using `only [Module.End.mul_apply, coefPm_apply, diagOp_coord, map_sum, map_smul]`.
-/
theorem coefD_comm (A : Module.End ℂ M) (B : Matrix (Fin n) (Fin n) ℂ) :
    Commute (coefPm (M := M) B) (diagOp A) := by
  refine LinearMap.ext fun u => funext fun c => ?_
  simp only [Module.End.mul_apply, coefPm_apply, diagOp_coord, map_sum, map_smul]

/- English proof (translation)
Rewrite using `[Finset.sum_comm]`. Simplify using `[Finset.sum_ite_eq]`.
-/
theorem coefD_sum_ite (c : Fin n) (f : Fin n → Fin n → M) :
    ∑ x, ∑ y, (if c = x then f x y else 0) = ∑ y, f c y := by
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq]

/- English proof (translation)
Simplify using `[Finset.sum_ite_eq]`.
-/
theorem coefD_sum_ite' (c : Fin n) (f : Fin n → Fin n → M) :
    ∑ x, ∑ y, (if c = y then f x y else 0) = ∑ x, f x c := by
  simp [Finset.sum_ite_eq]

/- English proof (translation)
Use `LinearMap.ext fun u => funext fun c => ?_` and prove the remaining obligations. Simplify using `only [actM, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, coefPm_apply, diagOp_coord, Pi.add_apply]`. Consider the cases of `dual`. Simplify using `only [tensF, cond_false, coefBm, tensV_coord, smul_add, Finset.sum_add_distrib, smul_ite, smul_zero, coefD_sum_ite]`. Rewrite using `[add_comm]`.

Simplify using `only [tensF, cond_true, coefBm, tensVd_coord, smul_sub, Finset.sum_sub_distrib, smul_ite, smul_zero, coefD_sum_ite', Matrix.neg_apply, Matrix.transpose_apply, neg_smul, Finset.sum_neg_distrib]`. Normalize the expressions using the abelian group laws.
-/
theorem coefD_tensAct_eq (dual : Bool) (E : Fin n → Fin n → Module.End ℂ M)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    actM (tensF dual E) X = coefPm (coefBm dual X) + diagOp (actM E X) := by
  refine LinearMap.ext fun u => funext fun c => ?_
  simp only [actM, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply,
    Pi.smul_apply, coefPm_apply, diagOp_coord, Pi.add_apply]
  cases dual
  · simp only [tensF, cond_false, coefBm, tensV_coord, smul_add, Finset.sum_add_distrib, smul_ite,
      smul_zero, coefD_sum_ite]
    rw [add_comm]
  · simp only [tensF, cond_true, coefBm, tensVd_coord, smul_sub, Finset.sum_sub_distrib, smul_ite,
      smul_zero, coefD_sum_ite', Matrix.neg_apply, Matrix.transpose_apply, neg_smul,
      Finset.sum_neg_distrib]
    abel

/- English proof (translation)
Rewrite using `[coefD_tensAct_eq, (coefD_comm (actM E X) (coefBm dual X)).add_pow', LinearMap.sum_apply, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun kl _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, Pi.smul_apply, ← Nat.cast_smul_eq_nsmul ℂ, Module.End.mul_apply, coefPm_pow]`. Repeatedly rewrite using `[coefD_diag_pow]`.
-/
theorem coefD_tensAct_pow (dual : Bool) (E : Fin n → Fin n → Module.End ℂ M)
    (X : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) (u : Fin n → M) (c : Fin n) :
    ((actM (tensF dual E) X) ^ m) u c = ∑ kl ∈ antidiagonal m, (m.choose kl.1 : ℂ) •
      ∑ d, ((coefBm dual X) ^ kl.1) c d • ((actM E X) ^ kl.2) (u d) := by
  rw [coefD_tensAct_eq, (coefD_comm (actM E X) (coefBm dual X)).add_pow', LinearMap.sum_apply,
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun kl _ => ?_
  rw [LinearMap.smul_apply, Pi.smul_apply, ← Nat.cast_smul_eq_nsmul ℂ, Module.End.mul_apply,
    coefPm_pow]
  simp_rw [coefD_diag_pow]

end Alg

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

def coefTG (dual : Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (g : Matrix (Fin n) (Fin n) ℂ)
    (f : Fin n → H) : Fin n → H :=
  fun c => ∑ d, coefAm dual g c d • σ g (f d)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coefD_tensGrp_eq (dual : Bool) (g : Matrix (Fin n) (Fin n) ℂ) (f : Fin n → H) (c : Fin n) :
    coefTG dual σ g f c = ∑ d, coefAm dual g c d • σ g (f d) := rfl

/- English proof (translation)
Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun kl hkl => ?_` and prove the remaining obligations. Rewrite `hkl` using `[Finset.HasAntidiagonal.mem_antidiagonal]`.

Rewrite using `[← mul_assoc, ← hkl, coefC_choose_coef, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coefD_comb (s : ℂ) (m : ℕ) (B : Matrix (Fin n) (Fin n) ℂ) (L : Fin n → Fin n → ℕ → ℂ) :
    s ^ m / (m.factorial : ℂ) * ∑ c, ∑ kl ∈ antidiagonal m, (m.choose kl.1 : ℂ) *
        ∑ d, (B ^ kl.1) c d * L c d kl.2 =
      ∑ c, ∑ d, ∑ kl ∈ antidiagonal m,
        s ^ kl.1 / (kl.1.factorial : ℂ) * (B ^ kl.1) c d * (s ^ kl.2 / (kl.2.factorial : ℂ) * L c d kl.2) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
  rw [← mul_assoc, ← hkl, coefC_choose_coef, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

/- English proof (translation)
Use `set lc : Fin n → (H →L[ℂ] ℂ) := fun c => Λ.comp (ContinuousLinearMap.single ℂ (fun _ : Fin n => H) c)`. Establish `hΛ : ∀ u : Fin n → H, Λ u = ∑ c, lc c (u c)`. Introduce `u`. Use `conv_lhs => rw [← Finset.univ_sum_single u]`. Rewrite using `[map_sum]`.

Both sides reduce to the same expression. Use `set B := coefBm dual X`. Use `set Y := actM E X`. Use `set L : Fin n → Fin n → ℕ → ℂ := fun c d k => lc c ((((Y ^ k) (w d) : D) : H))`. Establish `hpair : ∀ c d, HasSum (fun m => ∑ kl ∈ antidiagonal m, (s : ℂ) ^ kl.1 / (kl.1.factorial : ℂ) * (B ^ kl.1) c d * ((s : ℂ) ^ kl.2 / (kl.2.factorial : ℂ) * L c d kl.2)) (coefAm dual (NormedSpace.exp ((s : ℂ) • X)) c d * lc c (σ (NormedSpace.exp ((s : ℂ) • X)) ((w d : D) : H)))`.

Introduce `c d`. Take `⟨a, ha, hs⟩` from `hb d`. Establish `hA` using `coefC_exp_entry_hasSum B s c d`. Rewrite `hA` using `[← coefD_Am_exp]`. Establish `hA'` using `coefC_exp_entry_summable B s c d`.

Establish `horb` using `hasSum_orbit_of_bound hσ hD hX (w d) a ha 0 s (by simpa using hs)`. Rewrite `horb` using `[exp_zero_smul, hσ.1.1]`. Establish `horb'` using `horb.mapL (lc c)`. Establish `hσs : HasSum (fun k : ℕ => (s : ℂ) ^ k / (k.factorial : ℂ) * L c d k) (lc c (σ (NormedSpace.exp ((s : ℂ) • X)) ((w d : D) : H)))`. Use `horb'.congr_fun fun k => ?_` and prove the remaining obligations.

Simplify using `only [L, Y, ContinuousLinearMap.one_apply, map_smul, smul_eq_mul, sub_zero]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hσ' : Summable fun k : ℕ => ‖(s : ℂ) ^ k / (k.factorial : ℂ) * L c d k‖`. Use `Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) (hs.mul_left ‖lc c‖)` and prove the remaining obligations.

Rewrite using `[norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast]`. Establish `h1 : ‖L c d k‖ ≤ ‖lc c‖ * a k` using `((lc c).le_opNorm _).trans (mul_le_mul_of_nonneg_left (ha k) (norm_nonneg _))`. Combine the equalities or inequalities in the displayed calculation. Establish `hmul` using `coefC_hasSum_mul hA hσs hA' hσ'`. Conclude with `hmul`.

Establish `htot` using `hasSum_sum fun c (_ : c ∈ (Finset.univ : Finset (Fin n))) => hasSum_sum fun d (_ : d ∈ (Finset.univ : Finset (Fin n))) => hpair c d`. Establish `hR : Λ (coefTG dual σ (NormedSpace.exp ((s : ℂ) • X)) (fun d => ((w d : D) : H))) = ∑ c, ∑ d, coefAm dual (NormedSpace.exp ((s : ℂ) • X)) c d * lc c (σ (NormedSpace.exp ((s : ℂ) • X)) ((w d : D) : H))`. Rewrite using `[hΛ]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[coefD_tensGrp_eq, map_sum]`.

Simplify using `only [map_smul, smul_eq_mul]`. Rewrite using `[hR]`. Use `htot.congr_fun fun m => ?_` and prove the remaining obligations. Rewrite using `[hΛ]`. Simplify using `only [coefD_tensAct_pow, Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, smul_eq_mul]`.

Rewrite using `[← coefD_comb]`.
-/
theorem coefD_taylor (dual : Bool) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (Λ : (Fin n → H) →L[ℂ] ℂ) (w : Fin n → D) (s : ℝ)
    (hb : ∀ d, ∃ a : ℕ → ℝ, (∀ m, ‖((((actM E X) ^ m) (w d) : D) : H)‖ ≤ a m) ∧
      Summable fun m : ℕ => a m * |s| ^ m / (m.factorial : ℝ)) :
    HasSum (fun m : ℕ => (s : ℂ) ^ m / (m.factorial : ℂ) *
        Λ (fun c => ((((actM (tensF dual E) X) ^ m) w c : D) : H)))
      (Λ (coefTG dual σ (NormedSpace.exp ((s : ℂ) • X)) (fun d => ((w d : D) : H)))) := by
  set lc : Fin n → (H →L[ℂ] ℂ) := fun c => Λ.comp (ContinuousLinearMap.single ℂ (fun _ : Fin n => H) c)
  have hΛ : ∀ u : Fin n → H, Λ u = ∑ c, lc c (u c) := by
    intro u
    conv_lhs => rw [← Finset.univ_sum_single u]
    rw [map_sum]
    rfl
  set B := coefBm dual X
  set Y := actM E X
  set L : Fin n → Fin n → ℕ → ℂ := fun c d k => lc c ((((Y ^ k) (w d) : D) : H))

  have hpair : ∀ c d, HasSum (fun m => ∑ kl ∈ antidiagonal m,
      (s : ℂ) ^ kl.1 / (kl.1.factorial : ℂ) * (B ^ kl.1) c d * ((s : ℂ) ^ kl.2 / (kl.2.factorial : ℂ) * L c d kl.2))
      (coefAm dual (NormedSpace.exp ((s : ℂ) • X)) c d *
        lc c (σ (NormedSpace.exp ((s : ℂ) • X)) ((w d : D) : H))) := by
    intro c d
    obtain ⟨a, ha, hs⟩ := hb d
    have hA := coefC_exp_entry_hasSum B s c d
    rw [← coefD_Am_exp] at hA
    have hA' := coefC_exp_entry_summable B s c d
    have horb := hasSum_orbit_of_bound hσ hD hX (w d) a ha 0 s (by simpa using hs)
    rw [exp_zero_smul, hσ.1.1] at horb
    have horb' := horb.mapL (lc c)
    have hσs : HasSum (fun k : ℕ => (s : ℂ) ^ k / (k.factorial : ℂ) * L c d k)
        (lc c (σ (NormedSpace.exp ((s : ℂ) • X)) ((w d : D) : H))) := by
      refine horb'.congr_fun fun k => ?_
      simp only [L, Y, ContinuousLinearMap.one_apply, map_smul, smul_eq_mul, sub_zero]
      push_cast
      ring
    have hσ' : Summable fun k : ℕ => ‖(s : ℂ) ^ k / (k.factorial : ℂ) * L c d k‖ := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) (hs.mul_left ‖lc c‖)
      rw [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast]
      have h1 : ‖L c d k‖ ≤ ‖lc c‖ * a k := ((lc c).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (ha k) (norm_nonneg _))
      calc |s| ^ k / (k.factorial : ℝ) * ‖L c d k‖ ≤ |s| ^ k / (k.factorial : ℝ) * (‖lc c‖ * a k) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = ‖lc c‖ * (a k * |s| ^ k / (k.factorial : ℝ)) := by ring
    have hmul := coefC_hasSum_mul hA hσs hA' hσ'
    exact hmul
  have htot := hasSum_sum fun c (_ : c ∈ (Finset.univ : Finset (Fin n))) =>
    hasSum_sum fun d (_ : d ∈ (Finset.univ : Finset (Fin n))) => hpair c d
  have hR : Λ (coefTG dual σ (NormedSpace.exp ((s : ℂ) • X)) (fun d => ((w d : D) : H))) =
      ∑ c, ∑ d, coefAm dual (NormedSpace.exp ((s : ℂ) • X)) c d *
        lc c (σ (NormedSpace.exp ((s : ℂ) • X)) ((w d : D) : H)) := by
    rw [hΛ]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [coefD_tensGrp_eq, map_sum]
    simp only [map_smul, smul_eq_mul]
  rw [hR]
  refine htot.congr_fun fun m => ?_
  rw [hΛ]
  simp only [coefD_tensAct_pow, Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, smul_eq_mul]
  rw [← coefD_comb]

end Rep

end ReciprocityTheory.ChartRestriction.DS
