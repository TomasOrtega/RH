import Mathlib

open Filter Topology Polynomial

namespace GlobalTheory.SimpleRoots

variable {d : ℕ}

/- English proof (translation)
Rewrite using `[eval_map, eval₂_eq_sum_range]`.
-/
theorem eval_map_eq_sum (p : Polynomial (MvPolynomial (Fin d) ℂ)) (x : Fin d → ℂ) (y : ℂ) :
    (p.map (MvPolynomial.eval x)).eval y
      = ∑ i ∈ Finset.range (p.natDegree + 1), MvPolynomial.eval x (p.coeff i) * y ^ i := by
  rw [eval_map, eval₂_eq_sum_range]

/- English proof (translation)
The claim follows from `AnalyticOnNhd.eval_mvPolynomial a x (Set.mem_univ x)`.
-/
theorem analyticAt_mvPolynomial_eval (a : MvPolynomial (Fin d) ℂ) (x : Fin d → ℂ) :
    AnalyticAt ℂ (fun x : Fin d → ℂ => MvPolynomial.eval x a) x :=
  AnalyticOnNhd.eval_mvPolynomial a x (Set.mem_univ x)

/- English proof (translation)
Simplify using `only [eval_map_eq_sum]`. Use `Finset.analyticAt_fun_sum _ fun i _ => ?_` and prove the remaining obligations. Conclude with `((analyticAt_mvPolynomial_eval _ _).comp analyticAt_fst).mul (analyticAt_snd.pow i)`.
-/
theorem analyticAt_eval_map (p : Polynomial (MvPolynomial (Fin d) ℂ)) (z : (Fin d → ℂ) × ℂ) :
    AnalyticAt ℂ (fun w : (Fin d → ℂ) × ℂ => (p.map (MvPolynomial.eval w.1)).eval w.2) z := by
  simp only [eval_map_eq_sum]
  refine Finset.analyticAt_fun_sum _ fun i _ => ?_
  exact ((analyticAt_mvPolynomial_eval _ _).comp analyticAt_fst).mul (analyticAt_snd.pow i)

/- English proof (translation)
Use `set f : (Fin d → ℂ) × ℂ → ℂ := fun w => (p.map (MvPolynomial.eval w.1)).eval w.2 with hf`. Establish `ha : AnalyticAt ℂ f (x₀, y₀)` using `analyticAt_eval_map p _`. Establish `hc : ContDiffAt ℂ ⊤ f (x₀, y₀)` using `ha.contDiffAt`. Establish `hd : HasFDerivAt (fun y : ℂ => f (x₀, y)) (fderiv ℂ f (x₀, y₀) ∘L .inr ℂ (Fin d → ℂ) ℂ) y₀` using `ha.differentiableAt.hasFDerivAt.comp y₀ (hasFDerivAt_prodMk_right x₀ y₀)`. Establish `hd'` using `((p.map (MvPolynomial.eval x₀)).hasDerivAt y₀).hasFDerivAt`.

Establish `he` using `hd.unique hd'`. Establish `hi : (fderiv ℂ f (x₀, y₀) ∘L .inr ℂ (Fin d → ℂ) ℂ).IsInvertible`. Rewrite using `[he]`. Use `⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ h1), ?_⟩` and prove the remaining obligations. Use `ext`.

Simplify using the standard rewrite rules. Use `⟨hc.implicitFunction (by simp) hi, ?_, hc.implicitFunction_apply_self (by simp) hi, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(hc.contDiffAt_implicitFunction (by simp) hi).analyticAt`. Use `filter_upwards [hc.eventually_apply_implicitFunction (by simp) hi] with x hx`. Conclude with `hx.trans h0`.

Use `filter_upwards [hc.eventually_apply_eq_iff_implicitFunction (by simp) hi] with w hw`. Rewrite using `[← hw]`. Conclude with `Iff.of_eq (congrArg _ h0.symm)`.
-/
theorem exists_analytic_root (p : Polynomial (MvPolynomial (Fin d) ℂ)) {x₀ : Fin d → ℂ} {y₀ : ℂ}
    (h0 : (p.map (MvPolynomial.eval x₀)).eval y₀ = 0)
    (h1 : (p.map (MvPolynomial.eval x₀)).derivative.eval y₀ ≠ 0) :
    ∃ ψ : (Fin d → ℂ) → ℂ, AnalyticAt ℂ ψ x₀ ∧ ψ x₀ = y₀ ∧
      (∀ᶠ x in 𝓝 x₀, (p.map (MvPolynomial.eval x)).eval (ψ x) = 0) ∧
      ∀ᶠ w in 𝓝 (x₀, y₀), (p.map (MvPolynomial.eval w.1)).eval w.2 = 0 ↔ ψ w.1 = w.2 := by
  set f : (Fin d → ℂ) × ℂ → ℂ := fun w => (p.map (MvPolynomial.eval w.1)).eval w.2 with hf
  have ha : AnalyticAt ℂ f (x₀, y₀) := analyticAt_eval_map p _
  have hc : ContDiffAt ℂ ⊤ f (x₀, y₀) := ha.contDiffAt
  have hd : HasFDerivAt (fun y : ℂ => f (x₀, y))
      (fderiv ℂ f (x₀, y₀) ∘L .inr ℂ (Fin d → ℂ) ℂ) y₀ :=
    ha.differentiableAt.hasFDerivAt.comp y₀ (hasFDerivAt_prodMk_right x₀ y₀)
  have hd' := ((p.map (MvPolynomial.eval x₀)).hasDerivAt y₀).hasFDerivAt
  have he := hd.unique hd'
  have hi : (fderiv ℂ f (x₀, y₀) ∘L .inr ℂ (Fin d → ℂ) ℂ).IsInvertible := by
    rw [he]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ h1), ?_⟩
    ext
    simp
  refine ⟨hc.implicitFunction (by simp) hi, ?_, hc.implicitFunction_apply_self (by simp) hi, ?_, ?_⟩
  · exact (hc.contDiffAt_implicitFunction (by simp) hi).analyticAt
  · filter_upwards [hc.eventually_apply_implicitFunction (by simp) hi] with x hx
    exact hx.trans h0
  · filter_upwards [hc.eventually_apply_eq_iff_implicitFunction (by simp) hi] with w hw
    rw [← hw]
    exact Iff.of_eq (congrArg _ h0.symm)

/- English proof (translation)
Rewrite using `[Multiset.nodup_iff_count_le_one]`. Introduce `y`. Rewrite using `[count_roots]`. Assume the negation of the conclusion as `hy`. Take `⟨h1, h2⟩` from `(one_lt_rootMultiplicity_iff_isRoot hP).mp (not_le.mp hy)`.

Conclude with `h y h1 h2`.
-/
theorem nodup_roots_of_derivative_ne_zero {P : ℂ[X]} (hP : P ≠ 0)
    (h : ∀ y, P.eval y = 0 → P.derivative.eval y ≠ 0) : P.roots.Nodup := by
  classical
  rw [Multiset.nodup_iff_count_le_one]
  intro y
  rw [count_roots]
  by_contra hy
  obtain ⟨h1, h2⟩ := (one_lt_rootMultiplicity_iff_isRoot hP).mp (not_le.mp hy)
  exact h y h1 h2

/- English proof (translation)
Establish `hne : ∀ x, p.map (MvPolynomial.eval x) ≠ 0` using `fun x => (hp.map _).ne_zero`. Establish `hex : ∀ y, ∃ ψ : (Fin d → ℂ) → ℂ, y ∈ (p.map (MvPolynomial.eval x₀)).roots → AnalyticAt ℂ ψ x₀ ∧ ψ x₀ = y ∧ ∀ᶠ x in 𝓝 x₀, (p.map (MvPolynomial.eval x)).eval (ψ x) = 0`. Introduce `y`. Distinguish the cases in `hy : y ∈ (p.map (MvPolynomial.eval x₀)).roots`. Establish `hy'` using `(mem_roots (hne x₀)).mp hy`.

Take `⟨ψ, h1, h2, h3, -⟩` from `exists_analytic_root p hy' (h y hy')`. Conclude with `⟨ψ, fun _ => ⟨h1, h2, h3⟩⟩`. Conclude with `⟨0, fun hy' => absurd hy' hy⟩`. Use `choose ψ hψ using hex`. Use `⟨ψ, fun y hy => ⟨(hψ y hy).1, (hψ y hy).2.1⟩, ?_⟩` and prove the remaining obligations.

Use `set S := (p.map (MvPolynomial.eval x₀)).roots with hS`. Establish `hnd : S.Nodup` using `nodup_roots_of_derivative_ne_zero (hne x₀) h`. Establish `hcard : ∀ x, (p.map (MvPolynomial.eval x)).roots.card = p.natDegree` using `fun x => by`. Rewrite using `[← hp.natDegree_map (MvPolynomial.eval x)]`. Conclude with `(IsAlgClosed.splits _).natDegree_eq_card_roots.symm`.

Establish `e1 : ∀ᶠ x in 𝓝 x₀, ∀ y ∈ S.toFinset, (p.map (MvPolynomial.eval x)).eval (ψ y x) = 0` using `(Finset.eventually_all _).mpr fun y hy => (hψ y (Multiset.mem_toFinset.mp hy)).2.2`. Establish `e2 : ∀ᶠ x in 𝓝 x₀, ∀ y ∈ S.toFinset, ∀ y' ∈ S.toFinset, y ≠ y' → ψ y x ≠ ψ y' x`. Use `(Finset.eventually_all _).mpr fun y hy => (Finset.eventually_all _).mpr fun y' hy' => ?_` and prove the remaining obligations. Distinguish the cases in `hyy : y = y'`. Conclude with `Eventually.of_forall fun _ hn => absurd hyy hn`.

Take `⟨a1, a2, -⟩` from `hψ y (Multiset.mem_toFinset.mp hy)`. Take `⟨b1, b2, -⟩` from `hψ y' (Multiset.mem_toFinset.mp hy')`. Use `(a1.continuousAt.ne_iff_eventually_ne b1.continuousAt).mp (by rwa [a2, b2])` as an intermediate fact. Conclude with `this.mono fun x hx _ => hx`. Use `filter_upwards [e1, e2] with x h1 h2`.

Use `symm`. Use `Multiset.eq_of_le_of_card_le ?_ ?_` and prove the remaining obligations. Use `(Multiset.le_iff_subset (hnd.map_on fun y hy y' hy' hyy => ?_)).mpr fun t ht => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Conclude with `h2 y (Multiset.mem_toFinset.mpr hy) y' (Multiset.mem_toFinset.mpr hy') hn hyy`.

Take `⟨y, hy, rfl⟩` from `Multiset.mem_map.mp ht`. Conclude with `(mem_roots (hne x)).mpr (h1 y (Multiset.mem_toFinset.mpr hy))`. Rewrite using `[Multiset.card_map, hcard, hS, hcard]`.
-/
theorem exists_analytic_roots {p : Polynomial (MvPolynomial (Fin d) ℂ)} (hp : p.Monic)
    {x₀ : Fin d → ℂ}
    (h : ∀ y, (p.map (MvPolynomial.eval x₀)).eval y = 0 →
      (p.map (MvPolynomial.eval x₀)).derivative.eval y ≠ 0) :
    ∃ ψ : ℂ → (Fin d → ℂ) → ℂ,
      (∀ y ∈ (p.map (MvPolynomial.eval x₀)).roots, AnalyticAt ℂ (ψ y) x₀ ∧ ψ y x₀ = y) ∧
      ∀ᶠ x in 𝓝 x₀, (p.map (MvPolynomial.eval x)).roots
        = (p.map (MvPolynomial.eval x₀)).roots.map fun y => ψ y x := by
  classical
  have hne : ∀ x, p.map (MvPolynomial.eval x) ≠ 0 := fun x => (hp.map _).ne_zero
  have hex : ∀ y, ∃ ψ : (Fin d → ℂ) → ℂ, y ∈ (p.map (MvPolynomial.eval x₀)).roots →
      AnalyticAt ℂ ψ x₀ ∧ ψ x₀ = y ∧
        ∀ᶠ x in 𝓝 x₀, (p.map (MvPolynomial.eval x)).eval (ψ x) = 0 := by
    intro y
    by_cases hy : y ∈ (p.map (MvPolynomial.eval x₀)).roots
    · have hy' := (mem_roots (hne x₀)).mp hy
      obtain ⟨ψ, h1, h2, h3, -⟩ := exists_analytic_root p hy' (h y hy')
      exact ⟨ψ, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, fun hy' => absurd hy' hy⟩
  choose ψ hψ using hex
  refine ⟨ψ, fun y hy => ⟨(hψ y hy).1, (hψ y hy).2.1⟩, ?_⟩
  set S := (p.map (MvPolynomial.eval x₀)).roots with hS
  have hnd : S.Nodup := nodup_roots_of_derivative_ne_zero (hne x₀) h
  have hcard : ∀ x, (p.map (MvPolynomial.eval x)).roots.card = p.natDegree := fun x => by
    rw [← hp.natDegree_map (MvPolynomial.eval x)]
    exact (IsAlgClosed.splits _).natDegree_eq_card_roots.symm
  have e1 : ∀ᶠ x in 𝓝 x₀, ∀ y ∈ S.toFinset, (p.map (MvPolynomial.eval x)).eval (ψ y x) = 0 :=
    (Finset.eventually_all _).mpr fun y hy => (hψ y (Multiset.mem_toFinset.mp hy)).2.2
  have e2 : ∀ᶠ x in 𝓝 x₀, ∀ y ∈ S.toFinset, ∀ y' ∈ S.toFinset, y ≠ y' → ψ y x ≠ ψ y' x := by
    refine (Finset.eventually_all _).mpr fun y hy => (Finset.eventually_all _).mpr fun y' hy' => ?_
    by_cases hyy : y = y'
    · exact Eventually.of_forall fun _ hn => absurd hyy hn
    · obtain ⟨a1, a2, -⟩ := hψ y (Multiset.mem_toFinset.mp hy)
      obtain ⟨b1, b2, -⟩ := hψ y' (Multiset.mem_toFinset.mp hy')
      have := (a1.continuousAt.ne_iff_eventually_ne b1.continuousAt).mp (by rwa [a2, b2])
      exact this.mono fun x hx _ => hx
  filter_upwards [e1, e2] with x h1 h2
  symm
  refine Multiset.eq_of_le_of_card_le ?_ ?_
  · refine (Multiset.le_iff_subset (hnd.map_on fun y hy y' hy' hyy => ?_)).mpr fun t ht => ?_
    · by_contra hn
      exact h2 y (Multiset.mem_toFinset.mpr hy) y' (Multiset.mem_toFinset.mpr hy') hn hyy
    · obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp ht
      exact (mem_roots (hne x)).mpr (h1 y (Multiset.mem_toFinset.mpr hy))
  · rw [Multiset.card_map, hcard, hS, hcard]

/- English proof (translation)
Proceed by induction on `T using Multiset.induction_on generalizing k with`. Consider the case `empty => simp`. Consider the case `cons a T ih`. Establish `ha` using `h a (Multiset.mem_cons_self a T)`. Establish `ih'` using `ih fun y hy => h y (Multiset.mem_cons_of_mem hy)`.

Simplify using `only [Multiset.map_cons, Multiset.prod_cons, sub_mul, coeff_sub, coeff_C_mul]`. Use `DifferentiableAt.sub ?_ (ha.mul (ih' k))` and prove the remaining obligations. Consider the cases of `k with`. Consider the case `zero => simp`. Consider the case `succ k => simpa only [coeff_X_mul] using ih' k`.
-/
theorem differentiableAt_coeff_prod {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : Multiset ι) (ψ : ι → E → ℂ) {x₀ : E} (h : ∀ y ∈ T, DifferentiableAt ℂ (ψ y) x₀) (k : ℕ) :
    DifferentiableAt ℂ (fun x => (T.map fun y => X - C (ψ y x)).prod.coeff k) x₀ := by
  induction T using Multiset.induction_on generalizing k with
  | empty => simp
  | cons a T ih =>
    have ha := h a (Multiset.mem_cons_self a T)
    have ih' := ih fun y hy => h y (Multiset.mem_cons_of_mem hy)
    simp only [Multiset.map_cons, Multiset.prod_cons, sub_mul, coeff_sub, coeff_C_mul]
    refine DifferentiableAt.sub ?_ (ha.mul (ih' k))
    cases k with
    | zero => simp
    | succ k => simpa only [coeff_X_mul] using ih' k

/- English proof (translation)
Proceed by induction on `T using Multiset.induction_on generalizing k with`. Consider the case `empty`. Simplify using `only [Multiset.map_zero, Multiset.prod_zero, coeff_one, Multiset.card_zero, pow_zero]`. Apply the tactic sequence `split_ifs <;> simp`. Consider the case `cons a T ih`.

Establish `ha` using `h a (Multiset.mem_cons_self a T)`. Establish `ih'` using `ih fun y hy => h y (Multiset.mem_cons_of_mem hy)`. Simplify using `only [Multiset.map_cons, Multiset.prod_cons, sub_mul, coeff_sub, coeff_C_mul, Multiset.card_cons]`. Establish `h1 : ‖(X * (T.map fun y => X - C y).prod).coeff k‖ ≤ (1 + R) ^ T.card`. Consider the cases of `k with`.

Consider the case `zero => simp`. Check the signs of the components of the expression. Consider the case `succ k => simpa only [coeff_X_mul] using ih' k`. Establish `h2 : ‖a * (T.map fun y => X - C y).prod.coeff k‖ ≤ R * (1 + R) ^ T.card`. Rewrite using `[norm_mul]`.

Conclude with `mul_le_mul ha (ih' k) (norm_nonneg _) hR`. Use `(norm_sub_le _ _).trans ((add_le_add h1 h2).trans_eq ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_coeff_prod_le (T : Multiset ℂ) {R : ℝ} (hR : 0 ≤ R) (h : ∀ y ∈ T, ‖y‖ ≤ R) (k : ℕ) :
    ‖(T.map fun y => X - C y).prod.coeff k‖ ≤ (1 + R) ^ T.card := by
  induction T using Multiset.induction_on generalizing k with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, coeff_one, Multiset.card_zero, pow_zero]
    split_ifs <;> simp
  | cons a T ih =>
    have ha := h a (Multiset.mem_cons_self a T)
    have ih' := ih fun y hy => h y (Multiset.mem_cons_of_mem hy)
    simp only [Multiset.map_cons, Multiset.prod_cons, sub_mul, coeff_sub, coeff_C_mul,
      Multiset.card_cons]
    have h1 : ‖(X * (T.map fun y => X - C y).prod).coeff k‖ ≤ (1 + R) ^ T.card := by
      cases k with
      | zero => simp; positivity
      | succ k => simpa only [coeff_X_mul] using ih' k
    have h2 : ‖a * (T.map fun y => X - C y).prod.coeff k‖ ≤ R * (1 + R) ^ T.card := by
      rw [norm_mul]
      exact mul_le_mul ha (ih' k) (norm_nonneg _) hR
    refine (norm_sub_le _ _).trans ((add_le_add h1 h2).trans_eq ?_)
    ring

/- English proof (translation)
Proceed by induction on `a using MvPolynomial.induction_on with`. Consider the case `C c => exact ⟨‖c‖, 0, norm_nonneg _, fun x => by simp⟩`. Consider the case `add a b ha hb`. Take `⟨C₁, m₁, h₁, ha⟩` from `ha`. Take `⟨C₂, m₂, h₂, hb⟩` from `hb`.

Use `⟨C₁ + C₂, m₁ + m₂, by positivity, fun x => ?_⟩` and prove the remaining obligations. Establish `h1 : 1 ≤ 1 + ‖x‖` using `by linarith [norm_nonneg x]`. Rewrite using `[map_add, add_mul]`. Use `(norm_add_le _ _).trans (add_le_add ((ha x).trans ?_) ((hb x).trans ?_))` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (by omega)) h₁`.

Conclude with `mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (by omega)) h₂`. Consider the case `mul_X a i ha`. Take `⟨C₁, m₁, h₁, ha⟩` from `ha`. Use `⟨C₁, m₁ + 1, h₁, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, MvPolynomial.eval_X, norm_mul, pow_succ, ← mul_assoc]`.

Use `mul_le_mul (ha x) ?_ (norm_nonneg _) (by positivity)` and prove the remaining obligations. Combine the linear relations using `[norm_le_pi_norm x i]`.
-/
theorem exists_norm_eval_le (a : MvPolynomial (Fin d) ℂ) :
    ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧ ∀ x : Fin d → ℂ, ‖MvPolynomial.eval x a‖ ≤ C * (1 + ‖x‖) ^ m := by
  induction a using MvPolynomial.induction_on with
  | C c => exact ⟨‖c‖, 0, norm_nonneg _, fun x => by simp⟩
  | add a b ha hb =>
    obtain ⟨C₁, m₁, h₁, ha⟩ := ha
    obtain ⟨C₂, m₂, h₂, hb⟩ := hb
    refine ⟨C₁ + C₂, m₁ + m₂, by positivity, fun x => ?_⟩
    have h1 : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
    rw [map_add, add_mul]
    refine (norm_add_le _ _).trans (add_le_add ((ha x).trans ?_) ((hb x).trans ?_))
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (by omega)) h₁
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (by omega)) h₂
  | mul_X a i ha =>
    obtain ⟨C₁, m₁, h₁, ha⟩ := ha
    refine ⟨C₁, m₁ + 1, h₁, fun x => ?_⟩
    rw [map_mul, MvPolynomial.eval_X, norm_mul, pow_succ, ← mul_assoc]
    refine mul_le_mul (ha x) ?_ (norm_nonneg _) (by positivity)
    linarith [norm_le_pi_norm x i]

/- English proof (translation)
Establish `h1` using `IsRoot.norm_lt_cauchyBound hP.ne_zero hy`. Use `lift M to NNReal using hM0`. Establish `h2 : P.cauchyBound ≤ M + 1`. Unfold `cauchyBound`. Rewrite using `[hP.leadingCoeff, nnnorm_one, div_one]`.

Use `gcongr`. Conclude with `Finset.sup_le fun i hi => by exact_mod_cast hM i (Finset.mem_range.mp hi)`. Conclude with `(h1.trans_le h2).le` after adjusting the coercions.
-/
theorem norm_root_le {P : ℂ[X]} (hP : P.Monic) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ i < P.natDegree, ‖P.coeff i‖ ≤ M) {y : ℂ} (hy : P.eval y = 0) : ‖y‖ ≤ M + 1 := by
  have h1 := IsRoot.norm_lt_cauchyBound hP.ne_zero hy
  lift M to NNReal using hM0
  have h2 : P.cauchyBound ≤ M + 1 := by
    unfold cauchyBound
    rw [hP.leadingCoeff, nnnorm_one, div_one]
    gcongr
    exact Finset.sup_le fun i hi => by exact_mod_cast hM i (Finset.mem_range.mp hi)
  exact_mod_cast (h1.trans_le h2).le

/- English proof (translation)
Use `choose C m hC h using fun i => exists_norm_eval_le (p.coeff i)`. Use `set s := Finset.range p.natDegree`. Establish `hs : 0 ≤ ∑ i ∈ s, C i` using `Finset.sum_nonneg fun i _ => hC i`. Use `⟨∑ i ∈ s, C i + 1, ∑ i ∈ s, m i, by positivity, fun x y hy => ?_⟩` and prove the remaining obligations. Establish `h1 : 1 ≤ 1 + ‖x‖` using `by linarith [norm_nonneg x]`.

Establish `h2` using `norm_root_le (hp.map _) (M := (∑ i ∈ s, C i) * (1 + ‖x‖) ^ (∑ i ∈ s, m i)) (by positivity) (fun i hi => ?_) hy`. Rewrite using `[add_mul, one_mul]`. Combine the linear relations using `[one_le_pow₀ h1 (n := ∑ i ∈ s, m i)]`. Rewrite `hi` using `[hp.natDegree_map]`. Establish `hi' : i ∈ s` using `Finset.mem_range.mpr hi`.

Rewrite using `[coeff_map]`. Use `(h i x).trans (mul_le_mul (Finset.single_le_sum (fun j _ => hC j) hi') (pow_le_pow_right₀ h1 (Finset.single_le_sum (fun j _ => Nat.zero_le _) hi')) (by positivity) hs)` and prove the remaining obligations.
-/
theorem exists_norm_root_le {p : Polynomial (MvPolynomial (Fin d) ℂ)} (hp : p.Monic) :
    ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧ ∀ (x : Fin d → ℂ) (y : ℂ),
      (p.map (MvPolynomial.eval x)).eval y = 0 → ‖y‖ ≤ C * (1 + ‖x‖) ^ m := by
  choose C m hC h using fun i => exists_norm_eval_le (p.coeff i)
  set s := Finset.range p.natDegree
  have hs : 0 ≤ ∑ i ∈ s, C i := Finset.sum_nonneg fun i _ => hC i
  refine ⟨∑ i ∈ s, C i + 1, ∑ i ∈ s, m i, by positivity, fun x y hy => ?_⟩
  have h1 : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  have h2 := norm_root_le (hp.map _) (M := (∑ i ∈ s, C i) * (1 + ‖x‖) ^ (∑ i ∈ s, m i))
    (by positivity) (fun i hi => ?_) hy
  · rw [add_mul, one_mul]
    linarith [one_le_pow₀ h1 (n := ∑ i ∈ s, m i)]
  · rw [hp.natDegree_map] at hi
    have hi' : i ∈ s := Finset.mem_range.mpr hi
    rw [coeff_map]
    refine (h i x).trans (mul_le_mul (Finset.single_le_sum (fun j _ => hC j) hi')
      (pow_le_pow_right₀ h1 (Finset.single_le_sum (fun j _ => Nat.zero_le _) hi'))
      (by positivity) hs)

end GlobalTheory.SimpleRoots
