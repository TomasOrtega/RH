import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPolynomialEqZeroOfEvalEqZeroOnOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CauchyLogSqrtTendstoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimitFamilyExistsOfCauchyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilyRegularityCauchyEstimateStatement

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4 GlobalTheory.Mean4O

noncomputable section

namespace GlobalTheory.Mean4O

/- English proof (translation)
Use `⟨∑ r : Fin n → σ, f (fun i => l (Pi.single (r i) 1)) • ∏ i, X (r i), ?_, fun x => ?_⟩` and prove the remaining obligations. Use `totalDegree_finsetSum_le fun r _ => (totalDegree_smul_le _ _).trans ((totalDegree_finsetProd _ _).trans ?_)` and prove the remaining obligations. Simplify using `[totalDegree_X]`. Establish `e : l x = ∑ o, x o • l (Pi.single o 1)` using `by conv_lhs => rw [pi_eq_sum_univ' x]`. Simplify using `only [map_sum, map_smul]`.

Rewrite using `[e, f.map_sum (fun _ o => x o • l (Pi.single o 1))]`. Simplify using `only [map_sum, smul_eval, map_prod, eval_X, f.map_smul_univ, smul_eq_mul, mul_comm]`.
-/
theorem exists_poly_diag {σ V : Type} [Fintype σ] [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (f : MultilinearMap ℝ (fun _ : Fin n => V) ℝ) (l : (σ → ℝ) →ₗ[ℝ] V) :
    ∃ P : MvPolynomial σ ℝ, P.totalDegree ≤ n ∧ ∀ x, eval x P = f fun _ => l x := by
  refine ⟨∑ r : Fin n → σ, f (fun i => l (Pi.single (r i) 1)) • ∏ i, X (r i), ?_, fun x => ?_⟩
  · refine totalDegree_finsetSum_le fun r _ => (totalDegree_smul_le _ _).trans
      ((totalDegree_finsetProd _ _).trans ?_)
    simp [totalDegree_X]
  · have e : l x = ∑ o, x o • l (Pi.single o 1) := by
      conv_lhs => rw [pi_eq_sum_univ' x]
      simp only [map_sum, map_smul]
    rw [e, f.map_sum (fun _ o => x o • l (Pi.single o 1))]
    simp only [map_sum, smul_eval, map_prod, eval_X, f.map_smul_univ, smul_eq_mul, mul_comm]

variable {D : D7} {Y : ShimX D.what₂.Tau}

def wtPart : (Option (D.what₂.Tau × Fin Y.N) → ℝ) →ₗ[ℝ] Wt Y where
  toFun x τ i := x (some (τ, i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/- English proof (translation)
The claim follows from `exists_poly_diag (T.K B c).num ((T.L B c).comp wtPart + (LinearMap.proj none).smulRight (T.a B c) + (T.K B c).ar.comp (((T.F c).phR R).comp wtPart))`.
-/
theorem exists_poly_fR (T : Real0 Y) (B : ℝ) (c : Y.Comp) (R : ℝ) :
    ∃ P : MvPolynomial (Option (D.what₂.Tau × Fin Y.N)) ℝ, P.totalDegree ≤ dimY Y + 1 ∧
      ∀ x, eval x P = T.fR B c (wtPart x) (x none) R :=
  exists_poly_diag (T.K B c).num ((T.L B c).comp wtPart + (LinearMap.proj none).smulRight (T.a B c) +
    (T.K B c).ar.comp (((T.F c).phR R).comp wtPart))

/- English proof (translation)
Use `choose F hd hF' using exists_poly_fR T B c`. Take `⟨C, hC⟩` from `GlobalTheory.T.family_regularity_cauchy_estimate D Y T hF 1`. Set `U : Set (Option (D.what₂.Tau × Fin Y.N) → ℝ)` to `(⋂ τ, ⋂ a : Fin Y.N, ⋂ b : Fin Y.N, {x | (b : ℕ) = a + 1 → x (some (τ, b)) < x (some (τ, a))}) ∩ ⋂ o, {x | 0 < x o} ∩ {x | x o < 1}`. Establish `hU : IsOpen U`. Use `IsOpen.inter (isOpen_iInter_of_finite fun τ => isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => ?_) (isOpen_iInter_of_finite fun o => (isOpen_lt continuous_const (continuous_apply o)).inter (isOpen_lt (continuous_apply o) continuous_const))` and prove the remaining obligations.

Distinguish the cases in `h : (b : ℕ) = a + 1`. Simplify using `only [h, true_imp_iff]`. Conclude with `isOpen_lt (continuous_apply _) (continuous_apply _)`. Simplify using `[h]`. Establish `hne : U.Nonempty`.

Use `⟨fun o => o.elim (1 / 2) fun y => 1 / ((y.2 : ℕ) + 2 : ℝ), ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_iInter, Set.mem_ofPred_eq, Option.elim_some]`. Introduce `τ a b h`. Rewrite using `[h]`. Use `push_cast`.

Conclude with `one_div_lt_one_div_of_lt (by positivity) (by linarith)`. Simplify using `only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_ofPred_eq]`. Introduce and unpack `(_ | y)`. Evaluate the numerical expressions. Establish `: (0 : ℝ) ≤ (y.2 : ℕ)` using `Nat.cast_nonneg _`.

Simplify using `only [Option.elim_some]`. Conclude with `⟨by positivity, (div_lt_one (by positivity)).2 (by linarith)⟩`. Take `⟨P, hP, -, hl⟩` from `GlobalTheory.exists_poly_limit_of_tendsto_on_open _ (dimY Y + 1) F U hU hne hd (by`. Introduce and unpack `x ⟨h₁, h₂⟩`. Simplify using `only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_ofPred_eq] at h₁ h₂`.

Simplify using `only [hF']`. Use `GlobalTheory.T.cauchy_log_sqrt_tendsto _ C (Real.exp 2) (dimY Y + 1) (hC B c _ (fun τ a b h _ => (h₁ τ a b h).le) ?_ _ ⟨(h₂ none).1.le, (h₂ none).2.le⟩)` and prove the remaining obligations. Use `(pi_norm_le_iff_of_nonneg zero_le_one).2 fun τ => (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_` and prove the remaining obligations. Use `h₂ (some (τ, i))` as an intermediate fact. Conclude with `abs_le.2 ⟨by change -1 ≤ x _; linarith [this.1], this.2.le⟩)`.

Use `⟨P, hP, fun u s => ?_⟩` and prove the remaining obligations. Use `hl fun o => o.elim s fun x => u x.1 x.2` as an intermediate fact. Simplify using `only [hF'] at this`. Conclude with `this`.
-/
theorem exists_poly_lim (T : Real0 Y) (hF : ∀ c, (T.F c).FamR Y.j) (B : ℝ) (c : Y.Comp) :
    ∃ P : MvPolynomial (Option (D.what₂.Tau × Fin Y.N)) ℝ, P.totalDegree ≤ dimY Y + 1 ∧
      ∀ (u : Wt Y) (s : ℝ), Tendsto (T.fR B c u s) atTop (𝓝 (evS Y P u s)) := by
  choose F hd hF' using exists_poly_fR T B c
  obtain ⟨C, hC⟩ := GlobalTheory.T.family_regularity_cauchy_estimate D Y T hF 1
  let U : Set (Option (D.what₂.Tau × Fin Y.N) → ℝ) :=
    (⋂ τ, ⋂ a : Fin Y.N, ⋂ b : Fin Y.N, {x | (b : ℕ) = a + 1 → x (some (τ, b)) < x (some (τ, a))}) ∩
      ⋂ o, {x | 0 < x o} ∩ {x | x o < 1}
  have hU : IsOpen U := by
    refine IsOpen.inter (isOpen_iInter_of_finite fun τ => isOpen_iInter_of_finite fun a =>
      isOpen_iInter_of_finite fun b => ?_) (isOpen_iInter_of_finite fun o =>
      (isOpen_lt continuous_const (continuous_apply o)).inter (isOpen_lt (continuous_apply o) continuous_const))
    by_cases h : (b : ℕ) = a + 1
    · simp only [h, true_imp_iff]
      exact isOpen_lt (continuous_apply _) (continuous_apply _)
    · simp [h]
  have hne : U.Nonempty := by
    refine ⟨fun o => o.elim (1 / 2) fun y => 1 / ((y.2 : ℕ) + 2 : ℝ), ?_, ?_⟩
    · simp only [Set.mem_iInter, Set.mem_ofPred_eq, Option.elim_some]
      intro τ a b h
      rw [h]
      push_cast
      exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
    · simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_ofPred_eq]
      rintro (_ | y)
      · norm_num
      · have : (0 : ℝ) ≤ (y.2 : ℕ) := Nat.cast_nonneg _
        simp only [Option.elim_some]
        exact ⟨by positivity, (div_lt_one (by positivity)).2 (by linarith)⟩
  obtain ⟨P, hP, -, hl⟩ := GlobalTheory.exists_poly_limit_of_tendsto_on_open _ (dimY Y + 1) F U hU hne hd (by
    rintro x ⟨h₁, h₂⟩
    simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_ofPred_eq] at h₁ h₂
    simp only [hF']
    refine GlobalTheory.T.cauchy_log_sqrt_tendsto _ C (Real.exp 2) (dimY Y + 1) (hC B c _ (fun τ a b h _ => (h₁ τ a b h).le) ?_ _
      ⟨(h₂ none).1.le, (h₂ none).2.le⟩)
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun τ => (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    have := h₂ (some (τ, i))
    exact abs_le.2 ⟨by change -1 ≤ x _; linarith [this.1], this.2.le⟩)
  refine ⟨P, hP, fun u s => ?_⟩
  have := hl fun o => o.elim s fun x => u x.1 x.2
  simp only [hF'] at this
  exact this

/- English proof (translation)
Introduce `D Y T hF`. Use `⟨fun hT => GlobalTheory.T.limit_family_exists_of_cauchy D Y fun B hB u hu hs => ?_, fun A => ?_⟩` and prove the remaining obligations. Take `⟨C, hC⟩` from `GlobalTheory.T.family_regularity_cauchy_estimate D Y T hF 1`. Use `⟨Fintype.card Y.Comp * C, Real.exp 2, fun R R' hR hR' => ?_⟩` and prove the remaining obligations. Establish `hn : ‖u‖ ≤ 1` using `(pi_norm_le_iff_of_nonneg zero_le_one).2 fun τ => (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => (le_ciSup (f := fun x : Rt D.what₂.Tau Y.N => |u x.1 x.2|) (Set.finite_range _).bddAbove (τ, i)).trans hs`.

Rewrite using `[hT B hB R hR u, hT B hB R' (hR.trans hR') u, ← Finset.sum_sub_distrib]`. Use `(Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun c _ => hC B c u (fun τ a b h h' => sub_nonneg.1 (hu τ a b h h')) hn 0 ⟨le_rfl, zero_le_one⟩ R R' hR hR').trans_eq ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `choose Ps h using exists_poly_lim T hF`.

Conclude with `⟨Ps, fun B _ c => h B c⟩`.
-/
theorem exists_limFam_and_tiePs : ∀ (D : D7) (Y : ShimX D.what₂.Tau) (T : Real0 Y), (∀ c, (T.F c).FamR Y.j) →
    (TieDeg T → ∃ Φ, LimFam (Y := Y) Φ) ∧ ∀ A : SlopeTestRemainingChoices Y, ∃ Ps, TiePs T { A with Ps := Ps } := by
  intro D Y T hF
  refine ⟨fun hT => GlobalTheory.T.limit_family_exists_of_cauchy D Y fun B hB u hu hs => ?_, fun A => ?_⟩
  · obtain ⟨C, hC⟩ := GlobalTheory.T.family_regularity_cauchy_estimate D Y T hF 1
    refine ⟨Fintype.card Y.Comp * C, Real.exp 2, fun R R' hR hR' => ?_⟩
    have hn : ‖u‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 fun τ =>
      (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i =>
        (le_ciSup (f := fun x : Rt D.what₂.Tau Y.N => |u x.1 x.2|) (Set.finite_range _).bddAbove (τ, i)).trans hs
    rw [hT B hB R hR u, hT B hB R' (hR.trans hR') u, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun c _ =>
      hC B c u (fun τ a b h h' => sub_nonneg.1 (hu τ a b h h')) hn 0 ⟨le_rfl, zero_le_one⟩ R R' hR hR').trans_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  · choose Ps h using exists_poly_lim T hF
    exact ⟨Ps, fun B _ c => h B c⟩

end GlobalTheory.Mean4O
