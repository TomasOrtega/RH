import Mathlib
import Formalism.PeriodIntegrals.UpqRep

noncomputable section

open PI.UpqRep MeasureTheory Matrix Finset
open scoped InnerProductSpace

namespace GlobalTheory.DiscreteSeriesTest

/- English proof (translation)
Establish `h1` using `Finset.card_filter_add_card_filter_not (s := univ.filter fun b : Fin n => a < b) (fun b => ε b = ε a)`. Establish `h2` using `Finset.card_filter_add_card_filter_not (s := univ.filter fun b : Fin n => b < a) (fun b => ε b = ε a)`. Rewrite `h1`, `h2` using `[Finset.filter_filter, Finset.filter_filter]`. Establish `e1 : (univ.filter fun b : Fin n => a < b) = Finset.Ioi a` using `by ext; simp`. Establish `e2 : (univ.filter fun b : Fin n => b < a) = Finset.Iio a` using `by ext; simp`.

Rewrite `h1` using `[e1, Fin.card_Ioi]`. Rewrite `h2` using `[e2, Fin.card_Iio]`. Establish `ha` using `a.isLt`. Establish `h3 : ((n - 1 - (a : ℕ) : ℕ) : ℝ) = (n : ℝ) - 1 - a`. Rewrite using `[Nat.sub_sub, Nat.cast_sub (by omega)]; push_cast; ring`.

Establish `h1'` using `congrArg (Nat.cast : ℕ → ℝ) h1`. Establish `h2'` using `congrArg (Nat.cast : ℕ → ℝ) h2`. Rewrite `h1'` using `[h3]`. Move the coercions through the operations in `at h1' h2'`. Simplify using `only [rhoN, rhoC, ne_eq]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem rhoN_add_rhoC {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    rhoN ε a + rhoC ε a = ((n : ℝ) - 1) / 2 - a := by
  have h1 := Finset.card_filter_add_card_filter_not (s := univ.filter fun b : Fin n => a < b) (fun b => ε b = ε a)
  have h2 := Finset.card_filter_add_card_filter_not (s := univ.filter fun b : Fin n => b < a) (fun b => ε b = ε a)
  rw [Finset.filter_filter, Finset.filter_filter] at h1 h2
  have e1 : (univ.filter fun b : Fin n => a < b) = Finset.Ioi a := by ext; simp
  have e2 : (univ.filter fun b : Fin n => b < a) = Finset.Iio a := by ext; simp
  rw [e1, Fin.card_Ioi] at h1
  rw [e2, Fin.card_Iio] at h2
  have ha := a.isLt
  have h3 : ((n - 1 - (a : ℕ) : ℕ) : ℝ) = (n : ℝ) - 1 - a := by
    rw [Nat.sub_sub, Nat.cast_sub (by omega)]; push_cast; ring
  have h1' := congrArg (Nat.cast : ℕ → ℝ) h1
  have h2' := congrArg (Nat.cast : ℕ → ℝ) h2
  rw [h3] at h1'
  push_cast at h1' h2'
  simp only [rhoN, rhoC, ne_eq]
  linarith

/- English proof (translation)
Rewrite using `[← rhoN_add_rhoC ε a]`. Simplify using `only [lowK, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lowK_add {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) (a : Fin n) :
    (lowK ε lam + (2 : ℝ) • rhoC ε) a = lam a + (((n : ℝ) - 1) / 2 - a) := by
  rw [← rhoN_add_rhoC ε a]
  simp only [lowK, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Introduce `a b hab`. Rewrite using `[lowK_add, lowK_add]`. Establish `h1` using `h hab`. Establish `h2 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ)` using `by exact_mod_cast hab`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lowK_add_strictAnti {n : ℕ} (ε : Fin n → Bool) {lam : Fin n → ℝ} (h : StrictAnti lam) :
    StrictAnti (lowK ε lam + (2 : ℝ) • rhoC ε) := by
  intro a b hab
  rw [lowK_add, lowK_add]
  have h1 := h hab
  have h2 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  linarith

/- English proof (translation)
Use `⟨?_, by simp [Jm, Matrix.diagonal_mul_diagonal, mul_comm]⟩` and prove the remaining obligations. Rewrite using `[Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Rewrite using `[Pi.star_apply, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]`.

Simplify using the standard rewrite rules.
-/
theorem torus_mem {n : ℕ} (ε : Fin n → Bool) (θ : Fin n → ℝ) :
    Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Kset ε := by
  refine ⟨?_, by simp [Jm, Matrix.diagonal_mul_diagonal, mul_comm]⟩
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  rw [Pi.star_apply, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    Complex.norm_exp_ofReal_mul_I]
  simp

/- English proof (translation)
Establish `h2` using `h (Pi.single a (2 * Real.pi)) (torus_mem ε _)`. Establish `e : (Matrix.diagonal fun b => Complex.exp (((Pi.single a (2 * Real.pi) : Fin n → ℝ) b : ℂ) * Complex.I)) = (1 : Matrix (Fin n) (Fin n) ℂ)`. Rewrite using `[← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `b`.

Distinguish the cases in `hb : b = a`. Substitute `hb` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hb]`. Rewrite `h2` using `[e, h1]`.

Simplify using `only [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2`. Establish `h3 : Complex.exp (((μ a * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) = 1`. Apply `smul_left_injective ℂ hv` to reduce the goal to its premises. Simplify using `using h2.symm`. Take `⟨m, hm⟩` from `Complex.exp_eq_one_iff.1 h3`.

Use `⟨m, ?_⟩` and prove the remaining obligations. Establish `h4` using `congrArg Complex.im hm`. Simplify using `at h4`. Conclude with `h4`.
-/
theorem wt_int {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (h1 : σ 1 = 1) {μ : Fin n → ℝ} {v : H} (hv : v ≠ 0)
    (h : IsWtOn (Kset ε) σ μ v) (a : Fin n) : ∃ m : ℤ, μ a = m := by
  have h2 := h (Pi.single a (2 * Real.pi)) (torus_mem ε _)
  have e : (Matrix.diagonal fun b => Complex.exp (((Pi.single a (2 * Real.pi) : Fin n → ℝ) b : ℂ) * Complex.I)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← Matrix.diagonal_one]
    congr 1
    funext b
    by_cases hb : b = a
    · subst hb; simp
    · simp [hb]
  rw [e, h1] at h2
  simp only [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
  have h3 : Complex.exp (((μ a * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) = 1 := by
    apply smul_left_injective ℂ hv
    simpa using h2.symm
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 h3
  refine ⟨m, ?_⟩
  have h4 := congrArg Complex.im hm
  simp at h4
  exact h4

/- English proof (translation)
Use `⟨hl, fun a => ?_⟩` and prove the remaining obligations. Take `⟨-, -, ⟨⟨h1, -⟩, -, -⟩, -, -, ⟨S, -, -, -, ⟨v, -, hv0, hv⟩, -⟩, -⟩` from `h`. Take `⟨m, hm⟩` from `wt_int h1 hv0 hv a`. Establish `h2` using `lowK_add ε lam a`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hm, rhoC] at h2`.

Use `⟨m + (univ.filter fun b => a < b ∧ ε b = ε a).card - (univ.filter fun b => b < a ∧ ε b = ε a).card - (n - 1) + a, ?_⟩` and prove the remaining obligations. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem isHCParam_of_isDS {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
    {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hl : StrictAnti lam) (h : IsDS ε lam σ) :
    IsHCParam lam := by
  refine ⟨hl, fun a => ?_⟩
  obtain ⟨-, -, ⟨⟨h1, -⟩, -, -⟩, -, -, ⟨S, -, -, -, ⟨v, -, hv0, hv⟩, -⟩, -⟩ := h
  obtain ⟨m, hm⟩ := wt_int h1 hv0 hv a
  have h2 := lowK_add ε lam a
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hm, rhoC] at h2
  refine ⟨m + (univ.filter fun b => a < b ∧ ε b = ε a).card - (univ.filter fun b => b < a ∧ ε b = ε a).card
    - (n - 1) + a, ?_⟩
  push_cast
  linarith

/- English proof (translation)
Establish `h` using `congrFun (congrFun hg 0) 0`. Simplify using `only [Jm, Matrix.mul_apply, Fin.sum_univ_one, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq] at h`. Establish `h2` using `congrArg norm h`. Apply the tactic sequence `have h3 : ‖(if ε 0 = true then (1 : ℂ) else -1)‖ = 1 := by split_ifs <;> simp`. Simplify using `only [norm_mul, norm_star, h3] at h2`.

Use polynomial arithmetic with `[norm_nonneg (g 0 0)]`.
-/
theorem norm_entry {ε : Fin 1 → Bool} {g : Matrix (Fin 1) (Fin 1) ℂ} (hg : inUJ ε g) : ‖g 0 0‖ = 1 := by
  have h := congrFun (congrFun hg 0) 0
  simp only [Jm, Matrix.mul_apply, Fin.sum_univ_one, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq] at h
  have h2 := congrArg norm h
  have h3 : ‖(if ε 0 = true then (1 : ℂ) else -1)‖ = 1 := by split_ifs <;> simp
  simp only [norm_mul, norm_star, h3] at h2
  nlinarith [norm_nonneg (g 0 0)]

def chi (m : ℤ) (g : Matrix (Fin 1) (Fin 1) ℂ) : ℂ →L[ℂ] ℂ := (g 0 0) ^ m • ContinuousLinearMap.id ℂ ℂ

/- English proof (translation)
Establish `key : ∀ t : ℝ, Complex.exp ((((μ 0 - m) * t : ℝ) : ℂ) * Complex.I) = 1`. Introduce `t`. Establish `h1` using `h (fun _ => t) (torus_mem ε _)`. Simplify using `only [chi, Matrix.diagonal_apply_eq, Fin.sum_univ_one, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul] at h1`. Establish `h2` using `mul_right_cancel₀ hv h1`.

Rewrite `h2` using `[← Complex.exp_int_mul]`. Establish `: (((μ 0 - m) * t : ℝ) : ℂ) * Complex.I = ((μ 0 * t : ℝ) : ℂ) * Complex.I - m * (t * Complex.I)` using `by push_cast; ring`. Rewrite using `[this, Complex.exp_sub, ← h2, div_self (Complex.exp_ne_zero _)]`. Use function extensionality and compare the values at `a`. Take `rfl : a = 0` from `Subsingleton.elim _ _`.

Assume the negation of the conclusion as `hne`. Establish `hne' : μ 0 - m ≠ 0` using `sub_ne_zero.2 hne`. Use `key (Real.pi / (μ 0 - m))` as an intermediate fact. Rewrite `this` using `[mul_div_cancel₀ _ hne', Complex.exp_pi_mul_I]`. Evaluate the numerical expressions using `at this`.
-/
theorem wt_eq {ε : Fin 1 → Bool} (m : ℤ) (μ : Fin 1 → ℝ) (v : ℂ) (hv : v ≠ 0)
    (h : IsWtOn (Kset ε) (chi m) μ v) : μ = fun _ => (m : ℝ) := by
  have key : ∀ t : ℝ, Complex.exp ((((μ 0 - m) * t : ℝ) : ℂ) * Complex.I) = 1 := by
    intro t
    have h1 := h (fun _ => t) (torus_mem ε _)
    simp only [chi, Matrix.diagonal_apply_eq, Fin.sum_univ_one, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul] at h1
    have h2 := mul_right_cancel₀ hv h1
    rw [← Complex.exp_int_mul] at h2
    have : (((μ 0 - m) * t : ℝ) : ℂ) * Complex.I = ((μ 0 * t : ℝ) : ℂ) * Complex.I - m * (t * Complex.I) := by
      push_cast; ring
    rw [this, Complex.exp_sub, ← h2, div_self (Complex.exp_ne_zero _)]
  funext a
  obtain rfl : a = 0 := Subsingleton.elim _ _
  by_contra hne
  have hne' : μ 0 - m ≠ 0 := sub_ne_zero.2 hne
  have := key (Real.pi / (μ 0 - m))
  rw [mul_div_cancel₀ _ hne', Complex.exp_pi_mul_I] at this
  norm_num at this

/- English proof (translation)
Use function extensionality and compare the values at `a`. Take `rfl : a = 0` from `Subsingleton.elim _ _`. Simplify using `[lowK, rhoN, rhoC, Finset.filter_singleton]`.
-/
theorem lowK_one (ε : Fin 1 → Bool) (lam : Fin 1 → ℝ) : lowK ε lam = lam := by
  funext a
  obtain rfl : a = 0 := Subsingleton.elim _ _
  simp [lowK, rhoN, rhoC, Finset.filter_singleton]

/- English proof (translation)
Establish `hE` using `(isClosedEmbeddingMatrix 1 ε).1`. Establish `hc : IsCompact (Set.pi Set.univ fun _ : Fin 1 => Set.pi Set.univ fun _ : Fin 1 => Metric.closedBall (0 : ℂ) 1)` using `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1`. Use `⟨?_⟩` and prove the remaining obligations. Use `hE.isCompact_preimage hc` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use `symm`. Use `Set.eq_univ_of_forall fun g i _ j _ => ?_` and prove the remaining obligations. Take `rfl : i = 0` from `Subsingleton.elim _ _`. Take `rfl : j = 0` from `Subsingleton.elim _ _`. Apply the tactic sequence `simpa using (norm_entry g.2).le`.
-/
theorem compact_one (ε : Fin 1 → Bool) : CompactSpace (UJ ε) := by
  have hE := (isClosedEmbeddingMatrix 1 ε).1
  have hc : IsCompact (Set.pi Set.univ fun _ : Fin 1 => Set.pi Set.univ fun _ : Fin 1 =>
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine ⟨?_⟩
  have := hE.isCompact_preimage hc
  convert this using 1
  symm
  refine Set.eq_univ_of_forall fun g i _ j _ => ?_
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : j = 0 := Subsingleton.elim _ _
  simpa using (norm_entry g.2).le

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, -, -, -, -, ⟨S, -, -, -, ⟨v, -, hv0, hv⟩, -⟩, -⟩`. Rewrite using `[← wt_eq m _ v hv0 hv, lowK_one]`. Introduce and unpack `rfl`. Establish `hsub : ∀ S : Submodule ℂ ℂ, S = ⊥ ∨ S = ⊤` using `fun S => eq_bot_or_eq_top S`.

Establish `hiso : ∀ g ∈ UJset ε, ∀ v : ℂ, ‖chi m g v‖ = ‖v‖`. Introduce `g hg v`. Apply the tactic sequence `simp [chi, norm_zpow, norm_entry hg]`. Use `⟨inferInstance, inferInstance, ⟨⟨?_, ?_⟩, hiso, ?_⟩, fun S _ _ => hsub S, ?_, ⟨⊤, ?_⟩, ?_⟩` and prove the remaining obligations. Use `ext`.

Simplify using `[chi]`. Introduce `a _ b _`. Use `ext`. Simplify using `[chi, Matrix.mul_apply, mul_zpow, mul_comm]`. Introduce `v`.

Simplify using `only [chi, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]`. Use `ContinuousOn.mul (ContinuousOn.zpow₀ (by fun_prop) m ?_) continuousOn_const` and prove the remaining obligations. Introduce `g hg`. Use `left`. Introduce `h0`.

Apply the tactic sequence `have := norm_entry hg`. Simplify using `[h0] at this`. Introduce `v w`. Use `compact_one ε` as an intermediate fact. Establish `hfin : IsFiniteMeasure (muG ε)` using `CompactSpace.isFiniteMeasure`.

Establish `hc : Continuous (coefOn (ε` using `ε) (chi m) v w) := by`. Unfold `coefOn`. Simplify using `only [chi, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]`. Use `Continuous.inner continuous_const (Continuous.mul (Continuous.zpow₀ ?_ m ?_) continuous_const)` and prove the remaining obligations. Conclude with `(Units.continuous_val.comp continuous_subtype_val).matrix_elem 0 0`.

Introduce `g left`. Introduce `h0`. Apply the tactic sequence `have := norm_entry g.2`. Simplify using `[umat] at h0`. Simplify using `[h0] at this`.

Use `MemLp.of_bound hc.aestronglyMeasurable (‖w‖ * ‖v‖) (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Use `norm_inner_le_norm (𝕜 := ℂ) w (chi m (umat g) v)` as an intermediate fact. Rewrite `this` using `[hiso _ g.2]`. Conclude with `this`. Rewrite using `[lowK_one]`.

Use `⟨inferInstance, fun _ _ _ _ => trivial, fun S _ _ => hsub S, ⟨1, trivial, one_ne_zero, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `θ _`. Simplify using `only [chi, Matrix.diagonal_apply_eq, Fin.sum_univ_one, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, ← Complex.exp_int_mul]`. Use `congr 2`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Introduce `μ v _ hv h`. Rewrite using `[wt_eq m μ v hv h]`. Conclude with `⟨fun _ _ => 0, by simp, by simp⟩`. Introduce `μ S hS`.

Take `⟨v, _, hv, h⟩` from `hS.2.2.2.1`. Rewrite using `[wt_eq m μ v hv h, lowK_one]`.
-/
theorem isDS_chi_iff (ε : Fin 1 → Bool) (m : ℤ) (lam : Fin 1 → ℝ) :
    IsDS ε lam (chi m) ↔ lam = fun _ => (m : ℝ) := by
  constructor
  · rintro ⟨-, -, -, -, -, ⟨S, -, -, -, ⟨v, -, hv0, hv⟩, -⟩, -⟩
    rw [← wt_eq m _ v hv0 hv, lowK_one]
  rintro rfl
  have hsub : ∀ S : Submodule ℂ ℂ, S = ⊥ ∨ S = ⊤ := fun S => eq_bot_or_eq_top S
  have hiso : ∀ g ∈ UJset ε, ∀ v : ℂ, ‖chi m g v‖ = ‖v‖ := by
    intro g hg v
    simp [chi, norm_zpow, norm_entry hg]
  refine ⟨inferInstance, inferInstance, ⟨⟨?_, ?_⟩, hiso, ?_⟩, fun S _ _ => hsub S, ?_, ⟨⊤, ?_⟩, ?_⟩
  · ext; simp [chi]
  · intro a _ b _
    ext
    simp [chi, Matrix.mul_apply, mul_zpow, mul_comm]
  · intro v
    simp only [chi, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    refine ContinuousOn.mul (ContinuousOn.zpow₀ (by fun_prop) m ?_) continuousOn_const
    intro g hg
    left
    intro h0
    have := norm_entry hg
    simp [h0] at this
  · intro v w
    have := compact_one ε
    have hfin : IsFiniteMeasure (muG ε) := CompactSpace.isFiniteMeasure
    have hc : Continuous (coefOn (ε := ε) (chi m) v w) := by
      unfold coefOn
      simp only [chi, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
      refine Continuous.inner continuous_const (Continuous.mul (Continuous.zpow₀ ?_ m ?_) continuous_const)
      · exact (Units.continuous_val.comp continuous_subtype_val).matrix_elem 0 0
      · intro g
        left
        intro h0
        have := norm_entry g.2
        simp [umat] at h0
        simp [h0] at this
    refine MemLp.of_bound hc.aestronglyMeasurable (‖w‖ * ‖v‖) (Filter.Eventually.of_forall fun g => ?_)
    have := norm_inner_le_norm (𝕜 := ℂ) w (chi m (umat g) v)
    rw [hiso _ g.2] at this
    exact this
  · rw [lowK_one]
    refine ⟨inferInstance, fun _ _ _ _ => trivial, fun S _ _ => hsub S, ⟨1, trivial, one_ne_zero, ?_⟩, ?_⟩
    · intro θ _
      simp only [chi, Matrix.diagonal_apply_eq, Fin.sum_univ_one, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply, smul_eq_mul, ← Complex.exp_int_mul]
      congr 2
      push_cast; ring
    · intro μ v _ hv h
      rw [wt_eq m μ v hv h]
      exact ⟨fun _ _ => 0, by simp, by simp⟩
  · intro μ S hS
    obtain ⟨v, _, hv, h⟩ := hS.2.2.2.1
    rw [wt_eq m μ v hv h, lowK_one]

/- English proof (translation)
Establish `c : ∀ (ε : Fin 2 → Bool) (a : Fin 2), ε 0 ≠ ε 1 → rhoN ε a - rhoC ε a = 1 / 2 - a`. Introduce `ε a h`. Establish `h0 : rhoC ε a = 0`. Establish `e1 : (univ.filter fun b => a < b ∧ ε b = ε a) = ∅`. Use `Finset.filter_eq_empty_iff.2 fun b _ hb => ?_` and prove the remaining obligations.

Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simp_all`. Establish `e2 : (univ.filter fun b => b < a ∧ ε b = ε a) = ∅`. Use `Finset.filter_eq_empty_iff.2 fun b _ hb => ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simp_all`. Simplify using `[rhoC, e1, e2]`.

Establish `h1` using `rhoN_add_rhoC ε a`. Move the coercions through the operations in `at h1`. Combine the linear equalities and inequalities to obtain the conclusion. Use function extensionality and compare the values at `a`. Establish `h1` using `c ![true, false] a (by simp)`.

Establish `h2` using `c ![false, true] (Equiv.swap 0 1 a) (by simp)`. Simplify using `only [lowK, Function.comp_apply, Pi.sub_apply, Pi.add_apply, add_sub_assoc, h1, h2]`. Apply the tactic sequence `fin_cases a <;> simp <;> norm_num`.
-/
theorem order_needed :
    lowK ![true, false] ![1 / 2, 7 / 2] = lowK ![false, true] ![5 / 2, 3 / 2] ∘ Equiv.swap 0 1 := by
  have c : ∀ (ε : Fin 2 → Bool) (a : Fin 2), ε 0 ≠ ε 1 →
      rhoN ε a - rhoC ε a = 1 / 2 - a := by
    intro ε a h
    have h0 : rhoC ε a = 0 := by
      have e1 : (univ.filter fun b => a < b ∧ ε b = ε a) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun b _ hb => ?_
        fin_cases a <;> fin_cases b <;> simp_all
      have e2 : (univ.filter fun b => b < a ∧ ε b = ε a) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun b _ hb => ?_
        fin_cases a <;> fin_cases b <;> simp_all
      simp [rhoC, e1, e2]
    have h1 := rhoN_add_rhoC ε a
    push_cast at h1
    linarith
  funext a
  have h1 := c ![true, false] a (by simp)
  have h2 := c ![false, true] (Equiv.swap 0 1 a) (by simp)
  simp only [lowK, Function.comp_apply, Pi.sub_apply, Pi.add_apply, add_sub_assoc, h1, h2]
  fin_cases a <;> simp <;> norm_num

end GlobalTheory.DiscreteSeriesTest
