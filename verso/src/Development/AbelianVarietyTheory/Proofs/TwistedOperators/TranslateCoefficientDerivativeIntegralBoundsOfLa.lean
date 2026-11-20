import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteBranchingUpq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DKerHasCompactSupport

noncomputable section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal

namespace GlobalTheory.SepReal.DerInt

/- English proof (translation)
Establish `hM0 : 0 ≤ M` using `(norm_nonneg _).trans (hM 0 ⟨le_refl _, zero_le_one⟩)`. Establish `hd1 : ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖f1 x - f1 0‖ ≤ M * (x - 0)` using `norm_image_sub_le_of_norm_deriv_le_segment' (fun x _ => (hf1 x).hasDerivWithinAt) (fun x hx => hM x (Set.Ico_subset_Icc_self hx))`. Establish `hg : ∀ x : ℝ, HasDerivAt (fun s : ℝ => f s - (s : ℂ) * f1 0) (f1 x - f1 0) x`. Introduce `x`. Establish `h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 x`.

Use `(hasDerivAt_id x).ofReal_comp` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Both sides reduce to the same expression. Conclude with `Complex.ofReal_one.symm`. Establish `h2` using `(hf x).sub (h1.mul_const (f1 0))`.

Rewrite `h2` using `[one_mul]`. Conclude with `h2`. Establish `hd2` using `norm_image_sub_le_of_norm_deriv_le_segment' (a := 0) (b := τ) (C := M * τ) (fun x _ => (hg x).hasDerivWithinAt) (fun x hx => by`. Use `hd1 x ⟨hx.1, (hx.2.le.trans hτ1)⟩` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation.

Establish `hfτ` using `hS τ ⟨hτ0.le, hτ1⟩`. Establish `hf0` using `hS 0 ⟨le_rfl, zero_le_one⟩`. Establish `e : (τ : ℂ) * f1 0 = (f τ - f 0) - ((f τ - (τ : ℂ) * f1 0) - (f 0 - ((0 : ℝ) : ℂ) * f1 0))` using `by push_cast; ring`. Establish `hn : ‖(τ : ℂ) * f1 0‖ = τ * ‖f1 0‖`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_of_nonneg hτ0.le]`.

Establish `hb : τ * ‖f1 0‖ ≤ τ ^ 2 + τ ^ 2 + M * τ * (τ - 0)`. Rewrite using `[← hn, e]`. Combine the equalities or inequalities in the displayed calculation. Establish `: τ * ‖f1 0‖ ≤ τ * ((2 + M) * τ)` using `by nlinarith`. Conclude with `le_of_mul_le_mul_left this hτ0`.
-/
theorem taylor_der (f f1 f2 : ℝ → ℂ) (τ M : ℝ) (hf : ∀ t, HasDerivAt f (f1 t) t) (hf1 : ∀ t, HasDerivAt f1 (f2 t) t)
    (hS : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖f t‖ ≤ τ ^ 2) (hM : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖f2 t‖ ≤ M) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) :
    ‖f1 0‖ ≤ (2 + M) * τ := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_refl _, zero_le_one⟩)
  have hd1 : ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖f1 x - f1 0‖ ≤ M * (x - 0) :=
    norm_image_sub_le_of_norm_deriv_le_segment' (fun x _ => (hf1 x).hasDerivWithinAt)
      (fun x hx => hM x (Set.Ico_subset_Icc_self hx))
  have hg : ∀ x : ℝ, HasDerivAt (fun s : ℝ => f s - (s : ℂ) * f1 0) (f1 x - f1 0) x := by
    intro x
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 x := by
      have := (hasDerivAt_id x).ofReal_comp
      convert this using 1
      · rfl
      · exact Complex.ofReal_one.symm
    have h2 := (hf x).sub (h1.mul_const (f1 0))
    rw [one_mul] at h2
    exact h2
  have hd2 := norm_image_sub_le_of_norm_deriv_le_segment' (a := 0) (b := τ) (C := M * τ)
    (fun x _ => (hg x).hasDerivWithinAt) (fun x hx => by
      have := hd1 x ⟨hx.1, (hx.2.le.trans hτ1)⟩
      calc _ ≤ M * (x - 0) := this
        _ ≤ M * τ := by gcongr; linarith [hx.2]) τ ⟨hτ0.le, le_rfl⟩
  have hfτ := hS τ ⟨hτ0.le, hτ1⟩
  have hf0 := hS 0 ⟨le_rfl, zero_le_one⟩
  have e : (τ : ℂ) * f1 0 = (f τ - f 0) - ((f τ - (τ : ℂ) * f1 0) - (f 0 - ((0 : ℝ) : ℂ) * f1 0)) := by
    push_cast; ring
  have hn : ‖(τ : ℂ) * f1 0‖ = τ * ‖f1 0‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hτ0.le]
  have hb : τ * ‖f1 0‖ ≤ τ ^ 2 + τ ^ 2 + M * τ * (τ - 0) := by
    rw [← hn, e]
    calc _ ≤ ‖f τ - f 0‖ + ‖(f τ - (τ : ℂ) * f1 0) - (f 0 - ((0 : ℝ) : ℂ) * f1 0)‖ := norm_sub_le _ _
      _ ≤ (‖f τ‖ + ‖f 0‖) + M * τ * (τ - 0) := by gcongr; exact norm_sub_le _ _
      _ ≤ _ := by linarith
  have : τ * ‖f1 0‖ ≤ τ * ((2 + M) * τ) := by nlinarith
  exact le_of_mul_le_mul_left this hτ0

/- English proof (translation)
Establish `hU' : IsURepOn (Formalism.QuantumDeterminants.UH (Jm ε)) π` using `hπ`. Establish `h0` using `GlobalTheory.SmLinSub.hasDerivAt_dR hu hY`. Establish `h1 : HasDerivAt (fun s : ℝ => π (NormedSpace.exp (t • Y)) (π (NormedSpace.exp (s • Y)) u)) (π (NormedSpace.exp (t • Y)) (dR π Y u)) 0` using `((π (NormedSpace.exp (t • Y))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h0`. Establish `e : ∀ s : ℝ, π (NormedSpace.exp (t • Y)) (π (NormedSpace.exp (s • Y)) u) = π (NormedSpace.exp ((s + t) • Y)) u`. Introduce `s`.

Rewrite using `[← GlobalTheory.SmLinSub.rep_mul hU' (GlobalTheory.SmLinSub.exp_mem hY t) (GlobalTheory.SmLinSub.exp_mem hY s), ← Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left t).smul_right s), add_smul, add_comm (s • Y)]`. Establish `h2 : HasDerivAt (fun s : ℝ => π (NormedSpace.exp ((s + t) • Y)) u) (π (NormedSpace.exp (t • Y)) (dR π Y u)) 0`. Simplify `h1` using `only [e]`. Establish `h3 : HasDerivAt (fun s : ℝ => π (NormedSpace.exp (s • Y)) u) (π (NormedSpace.exp (t • Y)) (dR π Y u)) t`. Use `HasDerivAt.comp_sub_const (x := t) (a := t) (by rwa [sub_self])` as an intermediate fact.

Simplify using `using this`. Establish `h4` using `((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h3`. Establish `h5 : HasDerivAt (fun s : ℝ => star ⟪w, π (NormedSpace.exp (s • Y)) u⟫_ℂ) (star ⟪w, π (NormedSpace.exp (t • Y)) (dR π Y u)⟫_ℂ) t` using `h4.star`. Establish `e2 : ∀ a : H, star ⟪w, a⟫_ℂ = ⟪a, w⟫_ℂ` using `fun a => by rw [← starRingEnd_apply, inner_conj_symm]`. Simplify `h5` using `only [e2]`.
-/
theorem coef_hasDerivAt {m : ℕ} {ε : Fin m → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {π : Mat m → (H →L[ℂ] H)} (hπ : IsURepOn (UJset ε) π) {Y : Mat m} (hY : Y ∈ lieOf (Jm ε)) {u : H}
    (hu : SmV (lieOf (Jm ε)) π u) (w : H) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ⟪π (NormedSpace.exp (s • Y)) u, w⟫_ℂ) ⟪π (NormedSpace.exp (t • Y)) (dR π Y u), w⟫_ℂ t := by
  have hU' : IsURepOn (Formalism.QuantumDeterminants.UH (Jm ε)) π := hπ
  have h0 := GlobalTheory.SmLinSub.hasDerivAt_dR hu hY
  have h1 : HasDerivAt (fun s : ℝ => π (NormedSpace.exp (t • Y)) (π (NormedSpace.exp (s • Y)) u))
      (π (NormedSpace.exp (t • Y)) (dR π Y u)) 0 :=
    ((π (NormedSpace.exp (t • Y))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h0
  have e : ∀ s : ℝ, π (NormedSpace.exp (t • Y)) (π (NormedSpace.exp (s • Y)) u) = π (NormedSpace.exp ((s + t) • Y)) u := by
    intro s
    rw [← GlobalTheory.SmLinSub.rep_mul hU' (GlobalTheory.SmLinSub.exp_mem hY t) (GlobalTheory.SmLinSub.exp_mem hY s),
      ← Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left t).smul_right s), add_smul, add_comm (s • Y)]
  have h2 : HasDerivAt (fun s : ℝ => π (NormedSpace.exp ((s + t) • Y)) u) (π (NormedSpace.exp (t • Y)) (dR π Y u)) 0 := by
    simpa only [e] using h1
  have h3 : HasDerivAt (fun s : ℝ => π (NormedSpace.exp (s • Y)) u) (π (NormedSpace.exp (t • Y)) (dR π Y u)) t := by
    have := HasDerivAt.comp_sub_const (x := t) (a := t) (by rwa [sub_self])
    simpa using this
  have h4 := ((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h3
  have h5 : HasDerivAt (fun s : ℝ => star ⟪w, π (NormedSpace.exp (s • Y)) u⟫_ℂ)
      (star ⟪w, π (NormedSpace.exp (t • Y)) (dR π Y u)⟫_ℂ) t := h4.star
  have e2 : ∀ a : H, star ⟪w, a⟫_ℂ = ⟪a, w⟫_ℂ := fun a => by rw [← starRingEnd_apply, inner_conj_symm]
  simpa only [e2] using h5

/- English proof (translation)
Establish `h1` using `(hasSum_nat_add_iff' 1).2 (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x)`. Establish `h2` using `(hasSum_nat_add_iff' 1).2 (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖)`. Rewrite `h2` using `[← Real.exp_eq_exp_ℝ]`. Simplify using `only [Finset.range_one, Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul] at h1 h2`. Use `HasSum.norm_le_of_bounded h1 h2 (fun k => ?_)` and prove the remaining obligations.

Rewrite using `[norm_smul, smul_eq_mul, Real.norm_of_nonneg (by positivity)]`. Conclude with `mul_le_mul_of_nonneg_left (norm_pow_le' x (Nat.succ_pos k)) (by positivity)`.
-/
theorem norm_exp_sub_one_le' {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] (x : A) :
    ‖NormedSpace.exp x - 1‖ ≤ Real.exp ‖x‖ - 1 := by
  have h1 := (hasSum_nat_add_iff' 1).2 (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x)
  have h2 := (hasSum_nat_add_iff' 1).2 (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖)
  rw [← Real.exp_eq_exp_ℝ] at h2
  simp only [Finset.range_one, Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one, inv_one,
    pow_zero, one_smul] at h1 h2
  refine HasSum.norm_le_of_bounded h1 h2 (fun k => ?_)
  rw [norm_smul, smul_eq_mul, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_pow_le' x (Nat.succ_pos k)) (by positivity)

/- English proof (translation)
Use `letI : NormedRing (Mat m) := Matrix.frobeniusNormedRing`. Use `letI : NormedAlgebra ℝ (Mat m) := Matrix.frobeniusNormedAlgebra`. Establish `hn : ∀ g : Mat m, hsn g = ‖g‖` using `fun g => by`. Rewrite using `[Matrix.frobenius_norm_def, hsn, Real.sqrt_eq_rpow]`. Simplify using `only [Real.rpow_two]`.

Establish `h1` using `norm_exp_sub_one_le' (t • Y)`. Establish `h2 : ‖t • Y‖ ≤ 1`. Rewrite using `[norm_smul, ← hn, Real.norm_eq_abs]`. Combine the equalities or inequalities in the displayed calculation. Establish `h3 : ‖(1 : Mat m)‖ = Real.sqrt m`.

Rewrite using `[← hn, hsn]`. Use `congr 1`. Establish `: ∀ a : Fin m, ∑ b, ‖(1 : Mat m) a b‖ ^ 2 = 1` using `fun a => by`. Rewrite using `[Finset.sum_eq_single a]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Simplify using `[Matrix.one_apply_ne' hb]`. Simplify using the standard rewrite rules. Simplify using `[this]`. Establish `h4 : Real.exp ‖t • Y‖ ≤ Real.exp 1` using `Real.exp_le_exp.2 h2`.

Establish `h5` using `Real.exp_one_lt_d9`. Establish `key : ‖NormedSpace.exp (t • Y)‖ ≤ Real.sqrt m + 3`. Establish `h6` using `norm_le_norm_sub_add (NormedSpace.exp (t • Y)) 1`. Rewrite `h6` using `[h3]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hn]`. Conclude with `key`.
-/
theorem hsn_exp_le {m : ℕ} (Y : Mat m) (t : ℝ) (ht : |t| ≤ 1) (hY : hsn Y ≤ 1) :
    hsn (NormedSpace.exp (t • Y)) ≤ Real.sqrt m + 3 := by
  letI : NormedRing (Mat m) := Matrix.frobeniusNormedRing
  letI : NormedAlgebra ℝ (Mat m) := Matrix.frobeniusNormedAlgebra
  have hn : ∀ g : Mat m, hsn g = ‖g‖ := fun g => by
    rw [Matrix.frobenius_norm_def, hsn, Real.sqrt_eq_rpow]
    simp only [Real.rpow_two]
  have h1 := norm_exp_sub_one_le' (t • Y)
  have h2 : ‖t • Y‖ ≤ 1 := by
    rw [norm_smul, ← hn, Real.norm_eq_abs]
    calc |t| * hsn Y ≤ 1 * 1 := mul_le_mul ht hY (Real.sqrt_nonneg _) zero_le_one
      _ = 1 := by norm_num
  have h3 : ‖(1 : Mat m)‖ = Real.sqrt m := by
    rw [← hn, hsn]
    congr 1
    have : ∀ a : Fin m, ∑ b, ‖(1 : Mat m) a b‖ ^ 2 = 1 := fun a => by
      rw [Finset.sum_eq_single a]
      · simp
      · intro b _ hb; simp [Matrix.one_apply_ne' hb]
      · simp
    simp [this]
  have h4 : Real.exp ‖t • Y‖ ≤ Real.exp 1 := Real.exp_le_exp.2 h2
  have h5 := Real.exp_one_lt_d9
  have key : ‖NormedSpace.exp (t • Y)‖ ≤ Real.sqrt m + 3 := by
    have h6 := norm_le_norm_sub_add (NormedSpace.exp (t • Y)) 1
    rw [h3] at h6
    calc _ ≤ _ := h6
      _ ≤ (Real.exp ‖t • Y‖ - 1) + Real.sqrt m := add_le_add h1 le_rfl
      _ ≤ Real.sqrt m + 3 := by linarith
  rw [hn]
  exact key

/- English proof (translation)
Use `haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩`. Break down `(Real.sqrt_nonneg _).lt_or_eq with h | h` into its components or cases. Conclude with `h`. It suffices to derive a contradiction. Establish `hs : ∑ a, ∑ b, ‖g a b‖ ^ 2 = 0`.

Establish `h0 : 0 ≤ ∑ a, ∑ b, ‖g a b‖ ^ 2` using `by positivity`. Use `h.symm` as an intermediate fact. Unfold `hsn at this`. Rewrite `this` using `[Real.sqrt_eq_zero h0]`. Then use the resulting hypothesis. Establish `hz : g = 0`.

Use extensionality with `a b`. Establish `h1` using `(Finset.sum_eq_zero_iff_of_nonneg (fun a _ => by positivity)).1 hs a (Finset.mem_univ a)`. Establish `h2` using `(Finset.sum_eq_zero_iff_of_nonneg (fun b _ => by positivity)).1 h1 b (Finset.mem_univ b)`. Simplify using `using h2`. Rewrite `hg` using `[hz]`.

Conclude with `not_isUnit_zero hg`.
-/
theorem hsn_pos {m : ℕ} (hm : 1 ≤ m) (g : Mat m) (hg : IsUnit g) : 0 < hsn g := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  rcases (Real.sqrt_nonneg _).lt_or_eq with h | h
  · exact h
  · exfalso
    have hs : ∑ a, ∑ b, ‖g a b‖ ^ 2 = 0 := by
      have h0 : 0 ≤ ∑ a, ∑ b, ‖g a b‖ ^ 2 := by positivity
      have := h.symm
      unfold hsn at this
      rwa [Real.sqrt_eq_zero h0] at this
    have hz : g = 0 := by
      ext a b
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => by positivity)).1 hs a (Finset.mem_univ a)
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => by positivity)).1 h1 b (Finset.mem_univ b)
      simpa using h2
    rw [hz] at hg
    exact not_isUnit_zero hg

/- English proof (translation)
Establish `hL7 : 7 ≤ L` using `by linarith`. Establish `hL0 : 0 < L` using `by linarith`. Establish `hR0 : 0 < R` using `by linarith`. Use `set l := Real.log L with hl`. Use `set r := Real.log R with hr`.

Establish `hl1 : 1 ≤ l`. Rewrite using `[hl, Real.le_log_iff_exp_le hL0]`. Use `Real.exp_one_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hr0 : 0 ≤ r` using `Real.log_nonneg hR1`.

Establish `hrl : r ≤ C₀ * m * l`. Use `Real.log_le_log hR0 hR` as an intermediate fact. Rewrite `this` using `[Real.log_rpow hL0]`. Then use the resulting hypothesis. Establish `hF1 : 2 + (L ^ 2 * R ^ 2) ^ 2 ≤ Real.exp (5 * l + 4 * r)`. Establish `e : Real.exp (5 * l + 4 * r) = L ^ 5 * R ^ 4`.

Rewrite using `[Real.exp_add, hl, hr, show (5 : ℝ) * Real.log L = ((5 : ℕ) : ℝ) * Real.log L by norm_num, show (4 : ℝ) * Real.log R = ((4 : ℕ) : ℝ) * Real.log R by norm_num, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log hL0, Real.exp_log hR0]`. Rewrite using `[e]`. Establish `h1 : 1 ≤ R ^ 4` using `one_le_pow₀ hR1`. Establish `h2 : 7 ^ 4 ≤ L ^ 4` using `pow_le_pow_left₀ (by norm_num) hL7 4`. Establish `h3 : 1 ≤ L ^ 4 * R ^ 4` using `by nlinarith`.

Establish `h4 : L ^ 5 * R ^ 4 = L * (L ^ 4 * R ^ 4)` using `by ring`. Establish `h5 : (L ^ 2 * R ^ 2) ^ 2 = L ^ 4 * R ^ 4` using `by ring`. Rewrite using `[h4, h5]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hb0 : 0 < (Real.sqrt m + 3) * R ^ 2` using `by positivity`.

Establish `hF2 : ((Real.sqrt m + 3) * R ^ 2) ^ (20 * m ^ 2) ≤ Real.exp ((l + 2 * r) * (20 * m ^ 2))`. Rewrite using `[Real.rpow_def_of_pos hb0]`. Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Apply `mul_le_mul_of_nonneg_right _ (by positivity)` to reduce the goal to its premises. Rewrite using `[Real.log_mul (by positivity) (by positivity), Real.log_pow, hr]`.

Establish `hs : Real.sqrt m + 3 ≤ L`. Establish `: Real.sqrt m ≤ m`. Rewrite using `[Real.sqrt_le_left (by linarith)]`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.

Use `Real.log_le_log (by positivity) hs` as an intermediate fact. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hm2 : 10 * (m - 1) ^ 2 ≤ 10 * m ^ 2 * l` using `by nlinarith`. Establish `hm3 : 50 * m ^ 3 ≤ 50 * m ^ 3 * l`.

Establish `: 0 ≤ m ^ 3` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `hp1 : 5 + 30 * m ^ 2 + 50 * m ^ 3 ≤ 100 * m ^ 4` using `by nlinarith`. Establish `hp2 : 4 * m + 40 * m ^ 3 ≤ 50 * m ^ 4` using `by nlinarith`. Establish `hq1` using `mul_le_mul_of_nonneg_right hp1 (by linarith : (0 : ℝ) ≤ l)`.

Establish `hq2` using `mul_le_mul_of_nonneg_left hp2 (by positivity : (0 : ℝ) ≤ C₀ * l)`. Establish `hr4 : 4 * r ≤ 4 * (C₀ * m * l)` using `by linarith`. Establish `hr40 : 40 * m ^ 2 * r ≤ 40 * m ^ 2 * (C₀ * m * l)` using `mul_le_mul_of_nonneg_left hrl (by positivity)`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Real.exp_add]`.

Use `_ ≤ _ := by`. Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem const_le (C₀ : ℝ) (hC₀ : 0 < C₀) (m L R : ℝ) (hm : 4 ≤ m) (hL : m + 3 ≤ L) (hR1 : 1 ≤ R) (hR : R ≤ L ^ (C₀ * m)) :
    (2 + (L ^ 2 * R ^ 2) ^ 2) * (Real.exp (50 * m ^ 3) * ((Real.sqrt m + 3) * R ^ 2) ^ (20 * m ^ 2)) * Real.exp (10 * (m - 1) ^ 2)
      ≤ Real.exp ((100 + 50 * C₀) * m ^ 4 * Real.log L) := by
  have hL7 : 7 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hR0 : 0 < R := by linarith
  set l := Real.log L with hl
  set r := Real.log R with hr
  have hl1 : 1 ≤ l := by
    rw [hl, Real.le_log_iff_exp_le hL0]
    have := Real.exp_one_lt_d9
    linarith
  have hr0 : 0 ≤ r := Real.log_nonneg hR1
  have hrl : r ≤ C₀ * m * l := by
    have := Real.log_le_log hR0 hR
    rwa [Real.log_rpow hL0] at this

  have hF1 : 2 + (L ^ 2 * R ^ 2) ^ 2 ≤ Real.exp (5 * l + 4 * r) := by
    have e : Real.exp (5 * l + 4 * r) = L ^ 5 * R ^ 4 := by
      rw [Real.exp_add, hl, hr, show (5 : ℝ) * Real.log L = ((5 : ℕ) : ℝ) * Real.log L by norm_num,
        show (4 : ℝ) * Real.log R = ((4 : ℕ) : ℝ) * Real.log R by norm_num, Real.exp_nat_mul, Real.exp_nat_mul,
        Real.exp_log hL0, Real.exp_log hR0]
    rw [e]
    have h1 : 1 ≤ R ^ 4 := one_le_pow₀ hR1
    have h2 : 7 ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ (by norm_num) hL7 4
    have h3 : 1 ≤ L ^ 4 * R ^ 4 := by nlinarith
    have h4 : L ^ 5 * R ^ 4 = L * (L ^ 4 * R ^ 4) := by ring
    have h5 : (L ^ 2 * R ^ 2) ^ 2 = L ^ 4 * R ^ 4 := by ring
    rw [h4, h5]
    nlinarith

  have hb0 : 0 < (Real.sqrt m + 3) * R ^ 2 := by positivity
  have hF2 : ((Real.sqrt m + 3) * R ^ 2) ^ (20 * m ^ 2) ≤ Real.exp ((l + 2 * r) * (20 * m ^ 2)) := by
    rw [Real.rpow_def_of_pos hb0]
    apply Real.exp_le_exp.2
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, hr]
    have hs : Real.sqrt m + 3 ≤ L := by
      have : Real.sqrt m ≤ m := by
        rw [Real.sqrt_le_left (by linarith)]
        nlinarith
      linarith
    have := Real.log_le_log (by positivity) hs
    push_cast
    linarith
  have hm2 : 10 * (m - 1) ^ 2 ≤ 10 * m ^ 2 * l := by nlinarith
  have hm3 : 50 * m ^ 3 ≤ 50 * m ^ 3 * l := by
    have : 0 ≤ m ^ 3 := by positivity
    nlinarith
  have hp1 : 5 + 30 * m ^ 2 + 50 * m ^ 3 ≤ 100 * m ^ 4 := by nlinarith
  have hp2 : 4 * m + 40 * m ^ 3 ≤ 50 * m ^ 4 := by nlinarith
  have hq1 := mul_le_mul_of_nonneg_right hp1 (by linarith : (0 : ℝ) ≤ l)
  have hq2 := mul_le_mul_of_nonneg_left hp2 (by positivity : (0 : ℝ) ≤ C₀ * l)
  have hr4 : 4 * r ≤ 4 * (C₀ * m * l) := by linarith
  have hr40 : 40 * m ^ 2 * r ≤ 40 * m ^ 2 * (C₀ * m * l) := mul_le_mul_of_nonneg_left hrl (by positivity)
  calc _ ≤ Real.exp (5 * l + 4 * r) * (Real.exp (50 * m ^ 3) * Real.exp ((l + 2 * r) * (20 * m ^ 2))) *
        Real.exp (10 * (m - 1) ^ 2) := by gcongr
    _ = Real.exp ((5 * l + 4 * r) + (50 * m ^ 3 + (l + 2 * r) * (20 * m ^ 2)) + 10 * (m - 1) ^ 2) := by
        simp only [Real.exp_add]
    _ ≤ _ := by
        apply Real.exp_le_exp.2
        linarith

/- English proof (translation)
Establish `h1 : gᴴ * Jm ε * g = Jm ε` using `hg`. Establish `h2 : g'ᴴ * Jm ε * g' = Jm ε` using `hg'`. Use `show (g * g')ᴴ * Jm ε * (g * g') = Jm ε`. Establish `: g'ᴴ * (gᴴ * Jm ε * g) * g' = Jm ε` using `by rw [h1, h2]`. Simplify `this` using `[Matrix.mul_assoc, conjTranspose_mul]`.
-/
theorem mem_mul {m : ℕ} {ε : Fin m → Bool} {g g' : Mat m} (hg : g ∈ UJset ε) (hg' : g' ∈ UJset ε) : g * g' ∈ UJset ε := by
  have h1 : gᴴ * Jm ε * g = Jm ε := hg
  have h2 : g'ᴴ * Jm ε * g' = Jm ε := hg'
  show (g * g')ᴴ * Jm ε * (g * g') = Jm ε
  have : g'ᴴ * (gᴴ * Jm ε * g) * g' = Jm ε := by rw [h1, h2]
  simpa [Matrix.mul_assoc, conjTranspose_mul] using this

/- English proof (translation)
Establish `hJ : IsUnit (Jm ε)` using `⟨⟨Jm ε, Jm ε, Jm_mul_self ε, Jm_mul_self ε⟩, rfl⟩`. Establish `hd` using `(Matrix.isUnit_iff_isUnit_det g).1 (GlobalTheory.SmLinSub.isUnit_of_mem hJ hg)`. Establish `h1 : gᴴ * Jm ε * g = Jm ε` using `hg`. Use `show (g⁻¹)ᴴ * Jm ε * g⁻¹ = Jm ε`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem mem_inv {m : ℕ} {ε : Fin m → Bool} {g : Mat m} (hg : g ∈ UJset ε) : g⁻¹ ∈ UJset ε := by
  have hJ : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, Jm_mul_self ε, Jm_mul_self ε⟩, rfl⟩
  have hd := (Matrix.isUnit_iff_isUnit_det g).1 (GlobalTheory.SmLinSub.isUnit_of_mem hJ hg)
  have h1 : gᴴ * Jm ε * g = Jm ε := hg
  show (g⁻¹)ᴴ * Jm ε * g⁻¹ = Jm ε
  calc (g⁻¹)ᴴ * Jm ε * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Jm ε * g) * g⁻¹ := by rw [h1]
    _ = ((g⁻¹)ᴴ * gᴴ) * Jm ε * (g * g⁻¹) := by simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [← conjTranspose_mul, mul_nonsing_inv _ hd]; simp

/- English proof (translation)
Set `Li : H →ₗᵢ[ℂ] H` to `{ toLinearMap := (π a).toLinearMap, norm_map' := hπ.2.1 _ ha }`. Conclude with `Li.inner_map_map x y`.
-/
theorem inner_rep {m : ℕ} {ε : Fin m → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {π : Mat m → (H →L[ℂ] H)} (hπ : IsURepOn (UJset ε) π) {a : Mat m} (ha : a ∈ UJset ε) (x y : H) :
    ⟪π a x, π a y⟫_ℂ = ⟪x, y⟫_ℂ := by
  let Li : H →ₗᵢ[ℂ] H := { toLinearMap := (π a).toLinearMap, norm_map' := hπ.2.1 _ ha }
  exact Li.inner_map_map x y

/- English proof (translation)
Rewrite using `[hπ.1.2 a ha b hb]`. Both sides reduce to the same expression.
-/
theorem rep_mul_apply {m : ℕ} {ε : Fin m → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {π : Mat m → (H →L[ℂ] H)} (hπ : IsURepOn (UJset ε) π) {a b : Mat m} (ha : a ∈ UJset ε) (hb : b ∈ UJset ε) (x : H) :
    π (a * b) x = π a (π b x) := by
  rw [hπ.1.2 a ha b hb]; rfl

/- English proof (translation)
Introduce `hE hP hD hL C₀ hC₀`. Use `⟨100 + 50 * C₀, by positivity, ?_⟩` and prove the remaining obligations. Introduce `n e ε lam ε' mu B hpar H H' _ _ _ _ π σ hπ hσ v₀ hv₀ g₀ hg₀ hgn X hX hX1`. Take `⟨hmapH, hmul, hcont, hinv, hcol, hstab, hlie, hexp, hsnH, hsnL, hcolle, hUJ, hsub⟩` from `hE n e ε ε' hpar.signs`. Use `haveI : CompleteSpace H := hπ.1`.

Establish `hU : IsURepOn (UJset ε) π` using `hπ.2.2.1`. Establish `hU' : IsURepOn (Formalism.QuantumDeterminants.UH (Jm ε)) π` using `hU`. Establish `hJ : IsUnit (Jm ε)` using `⟨⟨Jm ε, Jm ε, Jm_mul_self ε, Jm_mul_self ε⟩, rfl⟩`. Establish `hn3` using `hpar.three_le`. Establish `hgap : GapAtLeast ε lam (1000 * (((n + 1 : ℕ)) : ℝ) ^ 3)` using `by push_cast; exact hpar.gap`.

Establish `hDe` using `hD (n + 1) ε lam B (by omega) hpar.hlam hgap hpar.bound.1 H π hπ v₀ hv₀`. Take `⟨hsm0, hLw⟩` from `hL (n + 1) ε lam B (by omega) hpar.hlam hgap hpar.bound.1 H π hπ v₀ hv₀`. Move the coercions through the operations in `at hDe hLw`. Use `set m : ℝ := (n : ℝ) + 1 with hm`. Establish `hm4 : 4 ≤ m`.

Establish `: (3 : ℝ) ≤ n` using `by exact_mod_cast hn3`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set R := hsn g₀ with hR`. Use `set X' := embL e X with hX'def`. Establish `hX' : X' ∈ lieOf (Jm ε)` using `hlie X hX`.

Establish `hX'n : hsn X' ≤ 1` using `by rw [hX'def, hsnL]; exact hX1`. Use `set v := π g₀ v₀ with hv`. Establish `hsmv : SmV (lieOf (Jm ε)) π v` using `GlobalTheory.SmLinSub.rep_mem hJ hU' hsm0 hg₀`. Use `set d1 := dR π X' v with hd1`. Establish `hsm1 : SmV (lieOf (Jm ε)) π d1` using `GlobalTheory.SmLinSub.dR_mem hJ hU' hsmv hX'`.

Use `set d2 := dR π X' d1 with hd2`. Establish `hv1 : ‖v‖ = 1` using `by rw [hv, hU.2.1 g₀ hg₀]; exact hv₀.1`. Establish `hR1 : 1 ≤ R` using `(hUJ g₀ hg₀).1.trans (hcolle g₀)`. Establish `hRi : hsn g₀⁻¹ = R` using `(hUJ g₀ hg₀).2`. Establish `hB : 500 * m ^ 3 ≤ B`.

Take `⟨i, hi⟩` from `hpar.neg`. Establish `h1` using `hpar.gap (e none) (e (some i)) (by rw [hpar.signs.1, hpar.signs.2 i, hi]; decide)`. Establish `ha` using `hpar.bound.1 (e none)`. Establish `hb` using `hpar.bound.1 (e (some i))`. Use `abs_sub (lam (e none)) (lam (e (some i)))` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hB1 : 1 ≤ B`. Establish `: (4 : ℝ) ^ 3 ≤ m ^ 3` using `pow_le_pow_left₀ (by norm_num) hm4 3`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hLm : m + 3 ≤ 8 * m * B` using `by nlinarith`.

Establish `hM2 : ‖d2‖ ≤ ((8 * m * B) ^ 2 * R ^ 2) ^ 2` using `by set X'' := g₀⁻¹ * X' * g₀ with hX''def`. Establish `hX'' : X'' ∈ lieOf (Jm ε)` using `GlobalTheory.SmLinSub.conj_mem_lie hJ hg₀ hX'`. Establish `e1 : d1 = π g₀ (dR π X'' v₀)` using `GlobalTheory.SmLinSub.dR_rep hJ hU' hsm0 hg₀ hX'`. Establish `hsm0'` using `GlobalTheory.SmLinSub.dR_mem hJ hU' hsm0 hX''`. Establish `e2 : d2 = π g₀ (dR π X'' (dR π X'' v₀))`.

Rewrite using `[hd2, e1]`. Conclude with `GlobalTheory.SmLinSub.dR_rep hJ hU' hsm0' hg₀ hX'`. Establish `hb` using `hLw [X'', X''] (by simp [hX'']) (by simp)`. Establish `hX''n : hsn X'' ≤ R ^ 2`. Establish `h1` using `hsub (g₀⁻¹ * X') g₀`.

Establish `h2` using `hsub g₀⁻¹ X'`. Rewrite `h2` using `[hRi]`. Establish `h0 : 0 ≤ hsn X'` using `Real.sqrt_nonneg _`. Establish `h0' : 0 ≤ R` using `Real.sqrt_nonneg _`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[e2, hU.2.1 g₀ hg₀]`. Simplify using `only [List.foldr, List.map, List.prod_cons, List.prod_nil, mul_one] at hb`. Establish `h0 : 0 ≤ hsn X''` using `Real.sqrt_nonneg _`. Combine the equalities or inequalities in the displayed calculation. Use `set M2 := ((8 * m * B) ^ 2 * R ^ 2) ^ 2 with hM2def`.

Use `set K0 := (Real.sqrt m + 3) * R ^ 2 with hK0`. Establish `hK0p : 0 < K0` using `by positivity`. Use `set A := 20 * m ^ 2 with hAdef`. Establish `hA0 : 0 ≤ A` using `by positivity`. Use `set K1 := (2 + M2) * (Real.exp (50 * m ^ 3) * K0 ^ A) with hK1`.

Establish `hK1p : 0 ≤ K1` using `by positivity`. Establish `hpt : ∀ h : UJ ε', ‖⟪d1, π (embH e (umat h)) v⟫_ℂ‖ ≤ K1 * hsn (umat h) ^ (-A)`. Introduce `h`. Use `set b := embH e (umat h) with hbdef`. Establish `hh : umat h ∈ UJset ε'` using `h.2`.

Establish `hb : b ∈ UJset ε` using `hmapH _ hh`. Establish `hhpos : 0 < hsn (umat h)` using `hsn_pos (by omega) _ (Units.isUnit _)`. Establish `hbn : hsn (umat h) ≤ hsn b`. Use `hsnH (umat h)` as an intermediate fact. Establish `h0 : 0 ≤ hsn b` using `Real.sqrt_nonneg _`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hbpos : 0 < hsn b` using `hhpos.trans_le hbn`. Use `set E := Real.exp (50 * m ^ 3) * (hsn b / K0) ^ (-A) with hEdef`. Establish `hE0 : 0 < E` using `by positivity`. Establish `hcoef : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖⟪π (NormedSpace.exp (t • X')) v, π b v⟫_ℂ‖ ≤ E ^ 2`.

Introduce `t ht`. Establish `ha : NormedSpace.exp (t • X') ∈ UJset ε` using `GlobalTheory.SmLinSub.exp_mem hX' t`. Establish `ha' : NormedSpace.exp ((-t) • X') ∈ UJset ε` using `GlobalTheory.SmLinSub.exp_mem hX' (-t)`. Establish `hst : (-t) • X' = t • -X'` using `by rw [neg_smul, smul_neg]`. Establish `haa : NormedSpace.exp ((-t) • X') * NormedSpace.exp (t • X') = 1`.

Rewrite using `[hst]`. Conclude with `GlobalTheory.SmLinSub.expS_neg_mul X' t`. Establish `haa' : NormedSpace.exp (t • X') * NormedSpace.exp ((-t) • X') = 1`. Rewrite using `[hst]`. Conclude with `GlobalTheory.SmLinSub.expS_mul_neg X' t`.

Establish `hd` using `(Matrix.isUnit_iff_isUnit_det g₀).1 (GlobalTheory.SmLinSub.isUnit_of_mem hJ hg₀)`. Establish `hgi` using `mem_inv hg₀`. Establish `hc : NormedSpace.exp ((-t) • X') * b ∈ UJset ε` using `mem_mul ha' hb`. Establish `hc'' : g₀⁻¹ * (NormedSpace.exp ((-t) • X') * b) * g₀ ∈ UJset ε` using `mem_mul (mem_mul hgi hc) hg₀`. Establish `e1 : ⟪π (NormedSpace.exp (t • X')) v, π b v⟫_ℂ = ⟪v, π (NormedSpace.exp ((-t) • X') * b) v⟫_ℂ`.

Rewrite using `[← inner_rep hU ha' (π _ v) (π b v), ← rep_mul_apply hU ha' ha, haa, hU.1.1, ← rep_mul_apply hU ha' hb]`. Both sides reduce to the same expression. Establish `e2 : ⟪v, π (NormedSpace.exp ((-t) • X') * b) v⟫_ℂ = ⟪v₀, π (g₀⁻¹ * (NormedSpace.exp ((-t) • X') * b) * g₀) v₀⟫_ℂ`. Rewrite using `[hv, ← inner_rep hU hgi (π g₀ v₀), ← rep_mul_apply hU hgi hg₀, nonsing_inv_mul _ hd, hU.1.1, ← rep_mul_apply hU hc hg₀, ← rep_mul_apply hU hgi (mem_mul hc hg₀), ← Matrix.mul_assoc]`. Both sides reduce to the same expression.

Establish `hsa : hsn (NormedSpace.exp (t • X')) ≤ Real.sqrt m + 3`. Use `hsn_exp_le X' t (abs_le.2 ⟨by linarith [ht.1], ht.2⟩) hX'n` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`. Establish `hbc : hsn b ≤ K0 * hsn (g₀⁻¹ * (NormedSpace.exp ((-t) • X') * b) * g₀)` using `by set c := NormedSpace.exp ((-t) • X') * b set c'' := g₀⁻¹ * c * g₀`.

Establish `eb : b = NormedSpace.exp (t • X') * (g₀ * c'' * g₀⁻¹)`. Establish `: g₀ * c'' * g₀⁻¹ = c`. Simplify using `only [c'', ← Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.one_mul]`. Rewrite using `[Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.mul_one]`. Rewrite using `[this, ← Matrix.mul_assoc, haa', Matrix.one_mul]`.

Establish `h0 : 0 ≤ hsn c''` using `Real.sqrt_nonneg _`. Establish `h0a : 0 ≤ hsn (NormedSpace.exp (t • X'))` using `Real.sqrt_nonneg _`. Establish `h0R : 0 ≤ R` using `Real.sqrt_nonneg _`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.

Use `_ ≤ (Real.sqrt m + 3) * (R * hsn c'' * R) := by gcongr`. Use `_ = K0 * hsn c'' := by rw [hK0]; ring`. Establish `hlow : hsn b / K0 ≤ hsn (g₀⁻¹ * (NormedSpace.exp ((-t) • X') * b) * g₀)`. Rewrite using `[div_le_iff₀ hK0p]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hE2 : E ^ 2 = Real.exp (100 * m ^ 3) * (hsn b / K0) ^ (-(40 * m ^ 2))`. Rewrite using `[hEdef, mul_pow, sq (Real.exp _), ← Real.exp_add, sq ((hsn b / K0) ^ (-A)), ← Real.rpow_add (div_pos hbpos hK0p), hAdef]`. Apply the tactic sequence `congr 2 <;> ring`. Rewrite using `[e1, e2, hE2]`. Use `(hDe _ hc'').trans ?_` and prove the remaining obligations.

Conclude with `mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (div_pos hbpos hK0p) hlow (neg_nonpos.2 (by positivity))) (Real.exp_pos _).le`. Establish `hone : ∀ t : ℝ, ‖⟪π (NormedSpace.exp (t • X')) v, π b v⟫_ℂ‖ ≤ 1`. Introduce `t`. Establish `ha` using `GlobalTheory.SmLinSub.exp_mem hX' t`. Combine the equalities or inequalities in the displayed calculation.

Establish `hτ0 : 0 < min 1 E` using `lt_min one_pos hE0`. Establish `key` using `taylor_der (fun s : ℝ => ⟪π (NormedSpace.exp (s • X')) v, π b v⟫_ℂ) (fun s : ℝ => ⟪π (NormedSpace.exp (s • X')) d1, π b v⟫_ℂ) (fun s : ℝ => ⟪π (NormedSpace.exp (s • X')) d2, π b v⟫_ℂ) (min 1 E) M2 (fun t => coef_hasDerivAt hU hX' hsmv _ t) (fun t => coef_hasDerivAt hU hX' hsm1 _ …`. Break down `le_total 1 E with h1 | h1` into its components or cases. Rewrite using `[min_eq_left h1]`. Simplify using `using hone t`.

Rewrite using `[min_eq_right h1]`. Conclude with `hcoef t ht)`. Use the proof step `(fun t ht => by`. Establish `ha` using `GlobalTheory.SmLinSub.exp_mem hX' t`. Combine the equalities or inequalities in the displayed calculation.

Use `hτ0 (min_le_left _ _)`. Simplify using `only [zero_smul, NormedSpace.exp_zero, hU.1.1, ContinuousLinearMap.one_apply] at key`. Establish `hsplit : (hsn b / K0) ^ (-A) = K0 ^ A * hsn b ^ (-A)`. Rewrite using `[Real.rpow_neg (div_nonneg hbpos.le hK0p.le), Real.div_rpow hbpos.le hK0p.le, inv_div, div_eq_mul_inv, ← Real.rpow_neg hbpos.le]`. Establish `hmono : hsn b ^ (-A) ≤ hsn (umat h) ^ (-A)` using `Real.rpow_le_rpow_of_nonpos hhpos hbn (by linarith)`.

Establish `hM20 : 0 ≤ M2` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Establish `hcontF : Continuous (fun h : UJ ε' => ⟪d1, π (embH e (umat h)) v⟫_ℂ)`. Establish `hum : Continuous (fun h : UJ ε' => umat h)` using `Units.continuous_val.comp continuous_subtype_val`. Establish `h1 : Continuous (fun h : UJ ε' => π (embH e (umat h)) v)` using `(hU.2.2 v).comp_continuous (hcont.comp hum) (fun h => hmapH _ h.2)`.

Conclude with `continuous_const.inner h1`. Establish `hAn : 4 * (n : ℝ) ^ 2 + 1 ≤ A` using `by rw [hAdef, hm]; nlinarith`. Take `⟨hInt, hIle⟩` from `hP n ε' A (by omega) hAn`. Establish `hIntK : Integrable (fun h : UJ ε' => K1 * hsn (umat h) ^ (-A)) (muG ε')` using `hInt.const_mul K1`. Use `⟨hIntK.mono' hcontF.aestronglyMeasurable (ae_of_all _ hpt), ?_⟩` and prove the remaining obligations.

Establish `hvol : 0 ≤ (muG ε' (nbh ε' (1 / 4))).toReal` using `ENNReal.toReal_nonneg`. Establish `hcst` using `const_le C₀ hC₀ m (8 * m * B) R hm4 hLm hR1 hgn`. Establish `hmn : m - 1 = n` using `by rw [hm]; ring`. Rewrite `hcst` using `[hmn]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hK1, hM2def, hK0, hAdef]`. Unfold `big`. Rewrite using `[← hm]`. Conclude with `hcst`. Use `_ = _ := by ring`.
-/
theorem derBounds_of : EmbLaws → PowInt → DecPow → LieBound → DerBounds := by
  intro hE hP hD hL C₀ hC₀
  refine ⟨100 + 50 * C₀, by positivity, ?_⟩
  intro n e ε lam ε' mu B hpar H H' _ _ _ _ π σ hπ hσ v₀ hv₀ g₀ hg₀ hgn X hX hX1
  obtain ⟨hmapH, hmul, hcont, hinv, hcol, hstab, hlie, hexp, hsnH, hsnL, hcolle, hUJ, hsub⟩ := hE n e ε ε' hpar.signs
  haveI : CompleteSpace H := hπ.1
  have hU : IsURepOn (UJset ε) π := hπ.2.2.1
  have hU' : IsURepOn (Formalism.QuantumDeterminants.UH (Jm ε)) π := hU
  have hJ : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, Jm_mul_self ε, Jm_mul_self ε⟩, rfl⟩
  have hn3 := hpar.three_le
  have hgap : GapAtLeast ε lam (1000 * (((n + 1 : ℕ)) : ℝ) ^ 3) := by push_cast; exact hpar.gap
  have hDe := hD (n + 1) ε lam B (by omega) hpar.hlam hgap hpar.bound.1 H π hπ v₀ hv₀
  obtain ⟨hsm0, hLw⟩ := hL (n + 1) ε lam B (by omega) hpar.hlam hgap hpar.bound.1 H π hπ v₀ hv₀
  push_cast at hDe hLw

  set m : ℝ := (n : ℝ) + 1 with hm
  have hm4 : 4 ≤ m := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    linarith
  set R := hsn g₀ with hR
  set X' := embL e X with hX'def
  have hX' : X' ∈ lieOf (Jm ε) := hlie X hX
  have hX'n : hsn X' ≤ 1 := by rw [hX'def, hsnL]; exact hX1
  set v := π g₀ v₀ with hv
  have hsmv : SmV (lieOf (Jm ε)) π v := GlobalTheory.SmLinSub.rep_mem hJ hU' hsm0 hg₀
  set d1 := dR π X' v with hd1
  have hsm1 : SmV (lieOf (Jm ε)) π d1 := GlobalTheory.SmLinSub.dR_mem hJ hU' hsmv hX'
  set d2 := dR π X' d1 with hd2
  have hv1 : ‖v‖ = 1 := by rw [hv, hU.2.1 g₀ hg₀]; exact hv₀.1
  have hR1 : 1 ≤ R := (hUJ g₀ hg₀).1.trans (hcolle g₀)
  have hRi : hsn g₀⁻¹ = R := (hUJ g₀ hg₀).2
  have hB : 500 * m ^ 3 ≤ B := by
    obtain ⟨i, hi⟩ := hpar.neg
    have h1 := hpar.gap (e none) (e (some i)) (by rw [hpar.signs.1, hpar.signs.2 i, hi]; decide)
    have ha := hpar.bound.1 (e none)
    have hb := hpar.bound.1 (e (some i))
    have := abs_sub (lam (e none)) (lam (e (some i)))
    linarith
  have hB1 : 1 ≤ B := by
    have : (4 : ℝ) ^ 3 ≤ m ^ 3 := pow_le_pow_left₀ (by norm_num) hm4 3
    linarith
  have hLm : m + 3 ≤ 8 * m * B := by nlinarith
  have hM2 : ‖d2‖ ≤ ((8 * m * B) ^ 2 * R ^ 2) ^ 2 := by
    set X'' := g₀⁻¹ * X' * g₀ with hX''def
    have hX'' : X'' ∈ lieOf (Jm ε) := GlobalTheory.SmLinSub.conj_mem_lie hJ hg₀ hX'
    have e1 : d1 = π g₀ (dR π X'' v₀) := GlobalTheory.SmLinSub.dR_rep hJ hU' hsm0 hg₀ hX'
    have hsm0' := GlobalTheory.SmLinSub.dR_mem hJ hU' hsm0 hX''
    have e2 : d2 = π g₀ (dR π X'' (dR π X'' v₀)) := by
      rw [hd2, e1]; exact GlobalTheory.SmLinSub.dR_rep hJ hU' hsm0' hg₀ hX'
    have hb := hLw [X'', X''] (by simp [hX'']) (by simp)
    have hX''n : hsn X'' ≤ R ^ 2 := by
      have h1 := hsub (g₀⁻¹ * X') g₀
      have h2 := hsub g₀⁻¹ X'
      rw [hRi] at h2
      have h0 : 0 ≤ hsn X' := Real.sqrt_nonneg _
      have h0' : 0 ≤ R := Real.sqrt_nonneg _
      calc hsn X'' ≤ hsn (g₀⁻¹ * X') * R := h1
        _ ≤ R * hsn X' * R := by gcongr
        _ ≤ R * 1 * R := by gcongr
        _ = R ^ 2 := by ring
    rw [e2, hU.2.1 g₀ hg₀]
    simp only [List.foldr, List.map, List.prod_cons, List.prod_nil, mul_one] at hb
    have h0 : 0 ≤ hsn X'' := Real.sqrt_nonneg _
    calc _ ≤ _ := hb
      _ ≤ ((8 * m * B) ^ 2 * R ^ 2) * ((8 * m * B) ^ 2 * R ^ 2) := by gcongr
      _ = _ := by ring

  set M2 := ((8 * m * B) ^ 2 * R ^ 2) ^ 2 with hM2def
  set K0 := (Real.sqrt m + 3) * R ^ 2 with hK0
  have hK0p : 0 < K0 := by positivity
  set A := 20 * m ^ 2 with hAdef
  have hA0 : 0 ≤ A := by positivity
  set K1 := (2 + M2) * (Real.exp (50 * m ^ 3) * K0 ^ A) with hK1
  have hK1p : 0 ≤ K1 := by positivity
  have hpt : ∀ h : UJ ε', ‖⟪d1, π (embH e (umat h)) v⟫_ℂ‖ ≤ K1 * hsn (umat h) ^ (-A) := by
    intro h
    set b := embH e (umat h) with hbdef
    have hh : umat h ∈ UJset ε' := h.2
    have hb : b ∈ UJset ε := hmapH _ hh
    have hhpos : 0 < hsn (umat h) := hsn_pos (by omega) _ (Units.isUnit _)
    have hbn : hsn (umat h) ≤ hsn b := by
      have := hsnH (umat h)
      have h0 : 0 ≤ hsn b := Real.sqrt_nonneg _
      nlinarith
    have hbpos : 0 < hsn b := hhpos.trans_le hbn
    set E := Real.exp (50 * m ^ 3) * (hsn b / K0) ^ (-A) with hEdef
    have hE0 : 0 < E := by positivity
    have hcoef : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖⟪π (NormedSpace.exp (t • X')) v, π b v⟫_ℂ‖ ≤ E ^ 2 := by
      intro t ht
      have ha : NormedSpace.exp (t • X') ∈ UJset ε := GlobalTheory.SmLinSub.exp_mem hX' t
      have ha' : NormedSpace.exp ((-t) • X') ∈ UJset ε := GlobalTheory.SmLinSub.exp_mem hX' (-t)
      have hst : (-t) • X' = t • -X' := by rw [neg_smul, smul_neg]
      have haa : NormedSpace.exp ((-t) • X') * NormedSpace.exp (t • X') = 1 := by
        rw [hst]; exact GlobalTheory.SmLinSub.expS_neg_mul X' t
      have haa' : NormedSpace.exp (t • X') * NormedSpace.exp ((-t) • X') = 1 := by
        rw [hst]; exact GlobalTheory.SmLinSub.expS_mul_neg X' t
      have hd := (Matrix.isUnit_iff_isUnit_det g₀).1 (GlobalTheory.SmLinSub.isUnit_of_mem hJ hg₀)
      have hgi := mem_inv hg₀
      have hc : NormedSpace.exp ((-t) • X') * b ∈ UJset ε := mem_mul ha' hb
      have hc'' : g₀⁻¹ * (NormedSpace.exp ((-t) • X') * b) * g₀ ∈ UJset ε := mem_mul (mem_mul hgi hc) hg₀
      have e1 : ⟪π (NormedSpace.exp (t • X')) v, π b v⟫_ℂ = ⟪v, π (NormedSpace.exp ((-t) • X') * b) v⟫_ℂ := by
        rw [← inner_rep hU ha' (π _ v) (π b v), ← rep_mul_apply hU ha' ha, haa, hU.1.1, ← rep_mul_apply hU ha' hb]
        rfl
      have e2 : ⟪v, π (NormedSpace.exp ((-t) • X') * b) v⟫_ℂ =
          ⟪v₀, π (g₀⁻¹ * (NormedSpace.exp ((-t) • X') * b) * g₀) v₀⟫_ℂ := by
        rw [hv, ← inner_rep hU hgi (π g₀ v₀), ← rep_mul_apply hU hgi hg₀, nonsing_inv_mul _ hd, hU.1.1,
          ← rep_mul_apply hU hc hg₀, ← rep_mul_apply hU hgi (mem_mul hc hg₀), ← Matrix.mul_assoc]
        rfl
      have hsa : hsn (NormedSpace.exp (t • X')) ≤ Real.sqrt m + 3 := by
        have := hsn_exp_le X' t (abs_le.2 ⟨by linarith [ht.1], ht.2⟩) hX'n
        push_cast at this
        exact this
      have hbc : hsn b ≤ K0 * hsn (g₀⁻¹ * (NormedSpace.exp ((-t) • X') * b) * g₀) := by
        set c := NormedSpace.exp ((-t) • X') * b
        set c'' := g₀⁻¹ * c * g₀
        have eb : b = NormedSpace.exp (t • X') * (g₀ * c'' * g₀⁻¹) := by
          have : g₀ * c'' * g₀⁻¹ = c := by
            simp only [c'', ← Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.one_mul]
            rw [Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.mul_one]
          rw [this, ← Matrix.mul_assoc, haa', Matrix.one_mul]
        have h0 : 0 ≤ hsn c'' := Real.sqrt_nonneg _
        have h0a : 0 ≤ hsn (NormedSpace.exp (t • X')) := Real.sqrt_nonneg _
        have h0R : 0 ≤ R := Real.sqrt_nonneg _
        calc hsn b ≤ hsn (NormedSpace.exp (t • X')) * hsn (g₀ * c'' * g₀⁻¹) := by rw [eb]; exact hsub _ _
          _ ≤ hsn (NormedSpace.exp (t • X')) * (R * hsn c'' * R) := by
              gcongr
              calc hsn (g₀ * c'' * g₀⁻¹) ≤ hsn (g₀ * c'') * hsn g₀⁻¹ := hsub _ _
                _ ≤ R * hsn c'' * R := by rw [hRi]; gcongr; exact hsub _ _
          _ ≤ (Real.sqrt m + 3) * (R * hsn c'' * R) := by gcongr
          _ = K0 * hsn c'' := by rw [hK0]; ring
      have hlow : hsn b / K0 ≤ hsn (g₀⁻¹ * (NormedSpace.exp ((-t) • X') * b) * g₀) := by
        rw [div_le_iff₀ hK0p]; linarith
      have hE2 : E ^ 2 = Real.exp (100 * m ^ 3) * (hsn b / K0) ^ (-(40 * m ^ 2)) := by
        rw [hEdef, mul_pow, sq (Real.exp _), ← Real.exp_add, sq ((hsn b / K0) ^ (-A)),
          ← Real.rpow_add (div_pos hbpos hK0p), hAdef]
        congr 2 <;> ring
      rw [e1, e2, hE2]
      refine (hDe _ hc'').trans ?_
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (div_pos hbpos hK0p) hlow (neg_nonpos.2 (by positivity)))
        (Real.exp_pos _).le
    have hone : ∀ t : ℝ, ‖⟪π (NormedSpace.exp (t • X')) v, π b v⟫_ℂ‖ ≤ 1 := by
      intro t
      have ha := GlobalTheory.SmLinSub.exp_mem hX' t
      calc _ ≤ ‖π (NormedSpace.exp (t • X')) v‖ * ‖π b v‖ := norm_inner_le_norm _ _
        _ = 1 := by rw [hU.2.1 _ ha, hU.2.1 _ hb, hv1]; norm_num
    have hτ0 : 0 < min 1 E := lt_min one_pos hE0
    have key := taylor_der (fun s : ℝ => ⟪π (NormedSpace.exp (s • X')) v, π b v⟫_ℂ)
      (fun s : ℝ => ⟪π (NormedSpace.exp (s • X')) d1, π b v⟫_ℂ) (fun s : ℝ => ⟪π (NormedSpace.exp (s • X')) d2, π b v⟫_ℂ)
      (min 1 E) M2 (fun t => coef_hasDerivAt hU hX' hsmv _ t) (fun t => coef_hasDerivAt hU hX' hsm1 _ t)
      (fun t ht => by
        rcases le_total 1 E with h1 | h1
        · rw [min_eq_left h1]; simpa using hone t
        · rw [min_eq_right h1]; exact hcoef t ht)
      (fun t ht => by
        have ha := GlobalTheory.SmLinSub.exp_mem hX' t
        calc _ ≤ ‖π (NormedSpace.exp (t • X')) d2‖ * ‖π b v‖ := norm_inner_le_norm _ _
          _ = ‖d2‖ := by rw [hU.2.1 _ ha, hU.2.1 _ hb, hv1, mul_one]
          _ ≤ M2 := hM2)
      hτ0 (min_le_left _ _)
    simp only [zero_smul, NormedSpace.exp_zero, hU.1.1, ContinuousLinearMap.one_apply] at key
    have hsplit : (hsn b / K0) ^ (-A) = K0 ^ A * hsn b ^ (-A) := by
      rw [Real.rpow_neg (div_nonneg hbpos.le hK0p.le), Real.div_rpow hbpos.le hK0p.le, inv_div, div_eq_mul_inv,
        ← Real.rpow_neg hbpos.le]
    have hmono : hsn b ^ (-A) ≤ hsn (umat h) ^ (-A) := Real.rpow_le_rpow_of_nonpos hhpos hbn (by linarith)
    have hM20 : 0 ≤ M2 := by positivity
    calc _ ≤ (2 + M2) * min 1 E := key
      _ ≤ (2 + M2) * E := by gcongr; exact min_le_right _ _
      _ = K1 * hsn b ^ (-A) := by rw [hEdef, hsplit, hK1]; ring
      _ ≤ K1 * hsn (umat h) ^ (-A) := by gcongr

  have hcontF : Continuous (fun h : UJ ε' => ⟪d1, π (embH e (umat h)) v⟫_ℂ) := by
    have hum : Continuous (fun h : UJ ε' => umat h) := Units.continuous_val.comp continuous_subtype_val
    have h1 : Continuous (fun h : UJ ε' => π (embH e (umat h)) v) :=
      (hU.2.2 v).comp_continuous (hcont.comp hum) (fun h => hmapH _ h.2)
    exact continuous_const.inner h1
  have hAn : 4 * (n : ℝ) ^ 2 + 1 ≤ A := by rw [hAdef, hm]; nlinarith
  obtain ⟨hInt, hIle⟩ := hP n ε' A (by omega) hAn
  have hIntK : Integrable (fun h : UJ ε' => K1 * hsn (umat h) ^ (-A)) (muG ε') := hInt.const_mul K1
  refine ⟨hIntK.mono' hcontF.aestronglyMeasurable (ae_of_all _ hpt), ?_⟩
  have hvol : 0 ≤ (muG ε' (nbh ε' (1 / 4))).toReal := ENNReal.toReal_nonneg
  have hcst := const_le C₀ hC₀ m (8 * m * B) R hm4 hLm hR1 hgn
  have hmn : m - 1 = n := by rw [hm]; ring
  rw [hmn] at hcst
  calc ∫ h, ‖⟪d1, π (embH e (umat h)) v⟫_ℂ‖ ∂muG ε' ≤ ∫ h, K1 * hsn (umat h) ^ (-A) ∂muG ε' :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hIntK (ae_of_all _ hpt)
    _ = K1 * ∫ h, hsn (umat h) ^ (-A) ∂muG ε' := integral_const_mul _ _
    _ ≤ K1 * (Real.exp (10 * (n : ℝ) ^ 2) * (muG ε' (nbh ε' (1 / 4))).toReal) := by gcongr
    _ = (K1 * Real.exp (10 * (n : ℝ) ^ 2)) * (muG ε' (nbh ε' (1 / 4))).toReal := by ring
    _ ≤ big (100 + 50 * C₀) n B * (muG ε' (nbh ε' (1 / 4))).toReal := by
        gcongr
        rw [hK1, hM2def, hK0, hAdef]
        unfold big
        rw [← hm]
        exact hcst
    _ = _ := by ring

end GlobalTheory.SepReal.DerInt
