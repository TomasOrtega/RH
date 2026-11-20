import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.RaisingLoweringNormIdentities
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.OneParameterSubgroups.OneParam
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ConjTransposeEqOfInG

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

/- English proof (translation)
Simplify using `[Matrix.trace, dMat, Matrix.diagonal_mul]`.
-/
theorem trace_dMat (d : Fin n → ℝ) (X : Matrix (Fin n) (Fin n) ℂ) :
    trace (dMat d * X) = ∑ a, (d a : ℂ) * X a a := by
  simp [Matrix.trace, dMat, Matrix.diagonal_mul]

/- English proof (translation)
Simplify using `only [stJ, Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, conjTranspose_apply]`.
-/
theorem stJ_apply (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    stJ ε X a b = (if ε a then 1 else -1) * star (X b a) * (if ε b then 1 else -1) := by
  simp only [stJ, Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, conjTranspose_apply]

/- English proof (translation)
Apply the tactic sequence `rw [stJ_apply]; split_ifs <;> simp`.
-/
theorem norm_stJ_apply (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    ‖stJ ε X a b‖ = ‖X b a‖ := by
  rw [stJ_apply]; split_ifs <;> simp

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem l1_le_card_mul_norm (X : Matrix (Fin n) (Fin n) ℂ) : l1 X ≤ (n : ℝ) ^ 2 * ‖X‖ := by
  calc l1 X ≤ ∑ _a : Fin n, ∑ _b : Fin n, ‖X‖ :=
        sum_le_sum fun a _ => sum_le_sum fun b _ => Matrix.norm_entry_le_entrywise_sup_norm X
    _ = _ := by simp; ring

/- English proof (translation)
Rewrite using `[Matrix.norm_le_iff (by positivity)]`. Introduce `a b`. Rewrite using `[Matrix.mul_apply]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul]`.

Conclude with `mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm X) (Matrix.norm_entry_le_entrywise_sup_norm Y) (norm_nonneg _) (norm_nonneg _)`. Use `_ = _ := by simp`.
-/
theorem norm_mul_le_n (X Y : Matrix (Fin n) (Fin n) ℂ) : ‖X * Y‖ ≤ n * (‖X‖ * ‖Y‖) := by
  rw [Matrix.norm_le_iff (by positivity)]
  intro a b
  rw [Matrix.mul_apply]
  calc _ ≤ ∑ c, ‖X a c * Y c b‖ := norm_sum_le _ _
    _ ≤ ∑ _c : Fin n, ‖X‖ * ‖Y‖ := sum_le_sum fun c _ => by
        rw [norm_mul]
        exact mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm X)
          (Matrix.norm_entry_le_entrywise_sup_norm Y) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp

/- English proof (translation)
Establish `e : actM E X w - ((t : ℂ) * trace (dMat d * X)) • w = ∑ a, ∑ b, X a b • (E a b w - (if a = b then (((t * d a : ℝ)) : ℂ) else 0) • w)`. Simplify using `only [actM, LinearMap.sum_apply, LinearMap.smul_apply, smul_sub, sum_sub_distrib, trace_dMat, mul_sum, sum_smul]`. Use `congr 1`. Use `sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[sum_eq_single a (fun b _ hb => by rw [if_neg (Ne.symm hb), zero_smul, smul_zero]) (by simp), if_pos rfl, smul_smul]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, l1, mul_sum]`. Use `(norm_sum_le _ _).trans (sum_le_sum fun a _ => ?_)` and prove the remaining obligations.

Rewrite using `[mul_sum]`. Use `(norm_sum_le _ _).trans (sum_le_sum fun b _ => ?_)` and prove the remaining obligations. Distinguish the cases in `h0 : X a b = 0`. Simplify using `[h0]`. Rewrite using `[norm_smul, mul_comm]`.

Conclude with `mul_le_mul_of_nonneg_right (h a b h0) (norm_nonneg _)`.
-/
theorem act_bound {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    (E : Fin n → Fin n → Module.End ℂ M) (w : M) (d : Fin n → ℝ) (t C : ℝ)
    (X : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ a b, X a b ≠ 0 → ‖E a b w - (if a = b then (((t * d a : ℝ)) : ℂ) else 0) • w‖ ≤ C) :
    ‖actM E X w - ((t : ℂ) * trace (dMat d * X)) • w‖ ≤ C * l1 X := by
  have e : actM E X w - ((t : ℂ) * trace (dMat d * X)) • w =
      ∑ a, ∑ b, X a b • (E a b w - (if a = b then (((t * d a : ℝ)) : ℂ) else 0) • w) := by
    simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply, smul_sub, sum_sub_distrib,
      trace_dMat, mul_sum, sum_smul]
    congr 1
    refine sum_congr rfl fun a _ => ?_
    rw [sum_eq_single a (fun b _ hb => by rw [if_neg (Ne.symm hb), zero_smul, smul_zero])
      (by simp), if_pos rfl, smul_smul]
    congr 1; push_cast; ring
  rw [e, l1, mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun a _ => ?_)
  rw [mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun b _ => ?_)
  by_cases h0 : X a b = 0
  · simp [h0]
  · rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right (h a b h0) (norm_nonneg _)

/- English proof (translation)
Introduce `h2 h3a h3b h3c hinf n ε d Λ₀ R`. Take `⟨C, hC, hB⟩` from `h2 n ε d Λ₀`. Take `⟨K, hK, hT⟩` from `h3c n |R|`. Use `set C' : ℝ := C * (n : ℝ) ^ 2 * (1 + |R|) with hC'`. Use `set Cd : ℝ := ∑ a, |d a| with hCd`.

Use `set ρb : ℝ := 2 * (n * (|R| * |R|)) with hρb`. Establish `hC'0 : 0 ≤ C'` using `by positivity`. Establish `hCd0 : 0 ≤ Cd` using `sum_nonneg fun a _ => abs_nonneg _`. Use `⟨(3 * C' + C' * 1 * ρb + Cd * K + C' * 1 * K) * Real.exp (Cd * ρb), ?_⟩` and prove the remaining obligations. Introduce `t ht H _ _ σ lam w ⟨hσ, hw, hw1, hhw, hcas⟩ hlam Y hY hYR`.

Take `⟨bp, bl, ball⟩` from `hB t ht (smD ε σ) (smE ε σ) lam ⟨w, hw⟩ ⟨(isDerivedOn_smE hσ).glRep, hinf n ε H σ hσ, hw1, hhw, hcas⟩ hlam`. Set `φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] H` to `{ toFun := fun X => ((actM (smE ε σ) X ⟨w, hw⟩ : smD ε σ) : H) map_add' := fun X X' => by simp [actM, add_smul, sum_add_distrib] map_smul' := fun c X => by simp [actM, smul_sum, smul_smul] }`. Establish `hφ : ∀ X, phiW ε σ w X = φ X` using `fun X => by rw [phiW, dif_pos hw]; rfl`. Set `dl : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ` to `{ toFun := fun X => trace (dMat d * X) map_add' := fun X X' => by rw [Matrix.mul_add, trace_add] map_smul' := fun c X => by simp }`. Establish `hsub : ∀ X (c : ℂ), ‖φ X - c • w‖ = ‖actM (smE ε σ) X ⟨w, hw⟩ - c • (⟨w, hw⟩ : smD ε σ)‖` using `fun X c => rfl`.

Establish `hYn : ‖Y‖ ≤ |R|`. Rewrite using `[Matrix.norm_le_iff (abs_nonneg R)]`. Introduce `a b`. Use `(le_abs_self _).trans (sq_le_sq.mp ?_)` and prove the remaining obligations. Use `le_trans ?_ hYR` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Set `Yl : Matrix (Fin n) (Fin n) ℂ` to `Matrix.of fun a b => if InLL ε d a b then Y a b else 0`. Set `Yp : Matrix (Fin n) (Fin n) ℂ` to `Matrix.of fun a b => if InNP ε d a b then Y a b else 0`. Use `set Ym := partNM ε d Y with hYm`. Establish `hpart : ∀ (p : Fin n → Fin n → Prop) [∀ a b, Decidable (p a b)], ‖(Matrix.of fun a b => if p a b then Y a b else 0 : Matrix (Fin n) (Fin n) ℂ)‖ ≤ |R|`.

Introduce `p _`. Rewrite using `[Matrix.norm_le_iff (abs_nonneg R)]`. Introduce `a b`. Rewrite using `[Matrix.of_apply]`. Use `split_ifs`.

Conclude with `(Matrix.norm_entry_le_entrywise_sup_norm Y).trans hYn`. Simplify using the standard rewrite rules. Establish `hYmn : ‖Ym‖ ≤ |R|` using `hpart _`. Establish `hsum : Yl + Yp + Ym = Y`. Use extensionality with `a b`.

Simplify using `only [Yl, Yp, hYm, partNM, Matrix.add_apply, Matrix.of_apply, InLL, InNP, InNM]`. Break down `lt_trichotomy a b with h | h | h` into its components or cases. Apply the tactic sequence `by_cases he : ε a = ε b <;> by_cases hd : d a = d b <;> simp [h, he, hd, lt_asymm h, eq_comm]`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Apply the tactic sequence `by_cases he : ε a = ε b <;> by_cases hd : d a = d b <;> simp [h, he, hd, lt_asymm h, eq_comm]`. Establish `hne : ∀ a b, InNP ε d a b → a ≠ b`. Apply the tactic sequence `rintro a b (h | h) rfl <;> exact lt_irrefl _ h.1`. Establish `hbd : ∀ X : Matrix (Fin n) (Fin n) ℂ, ‖X‖ ≤ |R| → C * l1 X ≤ C'` using `fun X hX => by`. Use `(l1_le_card_mul_norm X).trans (mul_le_mul_of_nonneg_left hX (by positivity))` as an intermediate fact.

Combine the equalities or inequalities in the displayed calculation. Establish `hNP : ∀ X : Matrix (Fin n) (Fin n) ℂ, ‖X‖ ≤ |R| → (∀ a b, X a b ≠ 0 → InNP ε d a b) → ‖φ X‖ ≤ C'`. Introduce `X hX hs`. Establish `h0 : trace (dMat d * X) = 0`. Rewrite using `[trace_dMat]`.

Use `sum_eq_zero fun a _ => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Conclude with `hne a a (hs a a (right_ne_zero_of_mul h)) rfl`. Use `act_bound (smE ε σ) ⟨w, hw⟩ d t C X fun a b h => by` as an intermediate fact. Rewrite using `[if_neg (hne a b (hs a b h)), zero_smul, sub_zero]`.

Conclude with `bp a b (hs a b h)`. Rewrite `this` using `[h0, mul_zero, zero_smul, sub_zero]`. Conclude with `this.trans (hbd X hX)`. Establish `hstn : ∀ X : Matrix (Fin n) (Fin n) ℂ, ‖stJ ε X‖ ≤ 1 * ‖X‖` using `fun X => by`. Rewrite using `[one_mul, Matrix.norm_le_iff (norm_nonneg _)]`.

Introduce `a b`. Rewrite using `[norm_stJ_apply]`. Conclude with `Matrix.norm_entry_le_entrywise_sup_norm X`. Establish `hdn : ∀ X, ‖dl X‖ ≤ Cd * ‖X‖` using `fun X => by show ‖trace (dMat d * X)‖ ≤ _`. Rewrite using `[trace_dMat, hCd, sum_mul]`.

Use `(norm_sum_le _ _).trans (sum_le_sum fun a _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_eq_abs]`. Conclude with `mul_le_mul_of_nonneg_left (Matrix.norm_entry_le_entrywise_sup_norm X) (abs_nonneg _)`. Establish `hdl : dl Yl = trace (dMat d * Y)` using `by show trace (dMat d * Yl) = _`. Rewrite using `[trace_dMat, trace_dMat]`.

Conclude with `sum_congr rfl fun a _ => by simp [Yl, InLL]`. Establish `hdiag : ∀ a, (Y a a).re = 0` using `fun a => by`. Use `congrArg Complex.re (congrFun (congrFun hY a) a)` as an intermediate fact. Simplify using `only [Jm, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, conjTranspose_apply, Matrix.zero_apply] at this`. Apply the tactic sequence `split_ifs at this <;> simp at this <;> linarith`.

Use `set Z : Matrix (Fin n) (Fin n) ℂ := (((Real.sqrt t)⁻¹ : ℝ) : ℂ) • Y with hZ`. Establish `hZG : inG ε Z`. Establish `hY' : Yᴴ * Jm ε + Jm ε * Y = 0` using `hY`. Use `show Zᴴ * Jm ε + Jm ε * Z = 0`. Rewrite using `[hZ, conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hY', smul_zero]`.

Establish `key` using `N.one_param w hw1 φ dl (stJ ε) hC'0 hCd0 zero_le_one hK ht hdn hstn (fun X X' => by simp [stJ, Matrix.mul_add, Matrix.add_mul]) (fun X => by show trace (dMat d * stJ ε X) = starRingEnd ℂ (trace (dMat d * X))`. Rewrite using `[trace_dMat, trace_dMat, map_sum]`. Use `sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Apply the tactic sequence `rw [stJ_apply]; split_ifs <;> simp)`. Use `Yl Yp Ym (Y * Ym - Ym * Y)`.

Use the proof step `(fun τ => NormedSpace.exp ((τ : ℂ) • Y) * Ym * NormedSpace.exp (-((τ : ℂ) • Y)))`. Use the proof step `(by rw [hdl, trace_dMat, Complex.re_sum]; exact sum_eq_zero fun a _ => by simp [hdiag])`. Use the proof step `(fun τ hτ => hT Y Ym hYn hYmn τ hτ.1 hτ.2)`. Use the proof step `(hNP Yp (hpart _) fun a b h => by`. Assume the negation of the conclusion as `h'; exact h (by simp [Yp, h']))`.

Use the proof step `(hNP _ ((hstn Ym).trans (by simpa using hYmn)) fun a b h => by`. Assume the negation of the conclusion as `h'`. Apply `h` to reduce the goal to its premises. Rewrite using `[← norm_eq_zero, norm_stJ_apply, norm_eq_zero]`. Simplify using `[hYm, partNM, InNM, h'])`.

Use the proof step `(by`. Rewrite using `[hsub]`. Use `(act_bound (smE ε σ) ⟨w, hw⟩ d t C Yl fun a b h => bl a b ?_).trans (hbd Yl (hpart _))` and prove the remaining obligations. Assume the negation of the conclusion as `h'; exact h (by simp [Yl, h']))`. Use the proof step `(fun X => by`.

Rewrite using `[hsub]`. Use `(ball X).trans ?_` and prove the remaining obligations. Establish `h1` using `l1_le_card_mul_norm X`. Establish `h0 : 0 ≤ C * Real.sqrt t` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hC']`. Establish `: 0 ≤ C * Real.sqrt t * ((n : ℝ) ^ 2 * ‖X‖) * |R|` using `by positivity`. Use the proof step `nlinarith)`. Use the proof step `(fun s => σ (NormedSpace.exp ((s : ℂ) • Z)))`. Use the proof step `(fun s v => hσ.2.1 _ (exp_smul_mem_UJset hZG s) v)`.

Use the proof step `(by simp [hσ.1.1])`. Use the proof step `(fun s _ => by rw [hsum, ← hφ]; exact h3b n ε H σ w hσ hw Z hZG s)`. Use the proof step `(fun s _ => by`. Use `h3a n ε H σ w hσ hw _ (exp_smul_mem_UJset hZG s) Ym` as an intermediate fact. Rewrite `this` using `[hφ, hφ, ← Matrix.exp_neg]`.

Establish `e : (s : ℂ) • Z = ((s / Real.sqrt t : ℝ) : ℂ) • Y`. Rewrite using `[hZ, smul_smul]`. Use `push_cast`. Rewrite using `[div_eq_mul_inv]`. Rewrite using `[this, e])`.

Establish `hρ : ‖Y * Ym - Ym * Y‖ ≤ ρb`. Establish `a1` using `(norm_mul_le_n Y Ym).trans (mul_le_mul_of_nonneg_left (mul_le_mul hYn hYmn (norm_nonneg _) (abs_nonneg _)) (Nat.cast_nonneg n))`. Establish `a2` using `(norm_mul_le_n Ym Y).trans (mul_le_mul_of_nonneg_left (mul_le_mul hYmn hYn (norm_nonneg _) (abs_nonneg _)) (Nat.cast_nonneg n))`. Use `norm_sub_le (Y * Ym) (Ym * Y)` as an intermediate fact. Rewrite using `[hρb]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hq : -(qForm ε d Y) = dl (Y * Ym - Ym * Y)` using `by rw [qForm, neg_neg]; rfl`. Rewrite using `[hq, ← hdl]`. Simplify using `only [Complex.ofReal_one, one_smul] at key`. Use `key.trans ?_` and prove the remaining obligations.

Rewrite using `[div_mul_eq_mul_div]`. Establish `hd2 : ‖dl (Y * Ym - Ym * Y)‖ ≤ Cd * ρb` using `(hdn _).trans (mul_le_mul_of_nonneg_left hρ hCd0)`. Establish `hρ0 : 0 ≤ ρb` using `by positivity`. Use `gcongr`.
-/
theorem matrixCoeffBounds_imply_bound : MatrixCoeffBoundsImplyBound := by
  classical
  intro h2 h3a h3b h3c hinf n ε d Λ₀ R
  obtain ⟨C, hC, hB⟩ := h2 n ε d Λ₀
  obtain ⟨K, hK, hT⟩ := h3c n |R|
  set C' : ℝ := C * (n : ℝ) ^ 2 * (1 + |R|) with hC'
  set Cd : ℝ := ∑ a, |d a| with hCd
  set ρb : ℝ := 2 * (n * (|R| * |R|)) with hρb
  have hC'0 : 0 ≤ C' := by positivity
  have hCd0 : 0 ≤ Cd := sum_nonneg fun a _ => abs_nonneg _
  refine ⟨(3 * C' + C' * 1 * ρb + Cd * K + C' * 1 * K) * Real.exp (Cd * ρb), ?_⟩
  intro t ht H _ _ σ lam w ⟨hσ, hw, hw1, hhw, hcas⟩ hlam Y hY hYR
  obtain ⟨bp, bl, ball⟩ := hB t ht (smD ε σ) (smE ε σ) lam ⟨w, hw⟩
    ⟨(isDerivedOn_smE hσ).glRep, hinf n ε H σ hσ, hw1, hhw, hcas⟩ hlam
  let φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] H :=
    { toFun := fun X => ((actM (smE ε σ) X ⟨w, hw⟩ : smD ε σ) : H)
      map_add' := fun X X' => by simp [actM, add_smul, sum_add_distrib]
      map_smul' := fun c X => by simp [actM, smul_sum, smul_smul] }
  have hφ : ∀ X, phiW ε σ w X = φ X := fun X => by rw [phiW, dif_pos hw]; rfl
  let dl : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun X => trace (dMat d * X)
      map_add' := fun X X' => by rw [Matrix.mul_add, trace_add]
      map_smul' := fun c X => by simp }
  have hsub : ∀ X (c : ℂ), ‖φ X - c • w‖ =
      ‖actM (smE ε σ) X ⟨w, hw⟩ - c • (⟨w, hw⟩ : smD ε σ)‖ := fun X c => rfl
  have hYn : ‖Y‖ ≤ |R| := by
    rw [Matrix.norm_le_iff (abs_nonneg R)]
    intro a b
    refine (le_abs_self _).trans (sq_le_sq.mp ?_)
    refine le_trans ?_ hYR
    calc ‖Y a b‖ ^ 2 ≤ ∑ j, ‖Y a j‖ ^ 2 :=
          single_le_sum (f := fun j => ‖Y a j‖ ^ 2) (fun j _ => by positivity) (mem_univ b)
      _ ≤ S7.hs Y := single_le_sum (f := fun i => ∑ j, ‖Y i j‖ ^ 2)
          (fun i _ => by positivity) (mem_univ a)
  let Yl : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun a b => if InLL ε d a b then Y a b else 0
  let Yp : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun a b => if InNP ε d a b then Y a b else 0
  set Ym := partNM ε d Y with hYm
  have hpart : ∀ (p : Fin n → Fin n → Prop) [∀ a b, Decidable (p a b)],
      ‖(Matrix.of fun a b => if p a b then Y a b else 0 : Matrix (Fin n) (Fin n) ℂ)‖ ≤ |R| := by
    intro p _
    rw [Matrix.norm_le_iff (abs_nonneg R)]
    intro a b
    rw [Matrix.of_apply]
    split_ifs
    · exact (Matrix.norm_entry_le_entrywise_sup_norm Y).trans hYn
    · simp
  have hYmn : ‖Ym‖ ≤ |R| := hpart _
  have hsum : Yl + Yp + Ym = Y := by
    ext a b
    simp only [Yl, Yp, hYm, partNM, Matrix.add_apply, Matrix.of_apply, InLL, InNP, InNM]
    rcases lt_trichotomy a b with h | h | h
    · by_cases he : ε a = ε b <;> by_cases hd : d a = d b <;> simp [h, he, hd, lt_asymm h, eq_comm]
    · subst h; simp
    · by_cases he : ε a = ε b <;> by_cases hd : d a = d b <;> simp [h, he, hd, lt_asymm h, eq_comm]
  have hne : ∀ a b, InNP ε d a b → a ≠ b := by
    rintro a b (h | h) rfl <;> exact lt_irrefl _ h.1
  have hbd : ∀ X : Matrix (Fin n) (Fin n) ℂ, ‖X‖ ≤ |R| → C * l1 X ≤ C' := fun X hX => by
    have := (l1_le_card_mul_norm X).trans (mul_le_mul_of_nonneg_left hX (by positivity))
    calc C * l1 X ≤ C * ((n : ℝ) ^ 2 * |R|) := mul_le_mul_of_nonneg_left this hC
      _ ≤ C' := by rw [hC']; nlinarith [mul_nonneg hC (sq_nonneg (n : ℝ))]
  have hNP : ∀ X : Matrix (Fin n) (Fin n) ℂ, ‖X‖ ≤ |R| → (∀ a b, X a b ≠ 0 → InNP ε d a b) →
      ‖φ X‖ ≤ C' := by
    intro X hX hs
    have h0 : trace (dMat d * X) = 0 := by
      rw [trace_dMat]
      refine sum_eq_zero fun a _ => ?_
      by_contra h
      exact hne a a (hs a a (right_ne_zero_of_mul h)) rfl
    have := act_bound (smE ε σ) ⟨w, hw⟩ d t C X fun a b h => by
      rw [if_neg (hne a b (hs a b h)), zero_smul, sub_zero]; exact bp a b (hs a b h)
    rw [h0, mul_zero, zero_smul, sub_zero] at this
    exact this.trans (hbd X hX)
  have hstn : ∀ X : Matrix (Fin n) (Fin n) ℂ, ‖stJ ε X‖ ≤ 1 * ‖X‖ := fun X => by
    rw [one_mul, Matrix.norm_le_iff (norm_nonneg _)]
    intro a b
    rw [norm_stJ_apply]; exact Matrix.norm_entry_le_entrywise_sup_norm X
  have hdn : ∀ X, ‖dl X‖ ≤ Cd * ‖X‖ := fun X => by
    show ‖trace (dMat d * X)‖ ≤ _
    rw [trace_dMat, hCd, sum_mul]
    refine (norm_sum_le _ _).trans (sum_le_sum fun a _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (Matrix.norm_entry_le_entrywise_sup_norm X) (abs_nonneg _)
  have hdl : dl Yl = trace (dMat d * Y) := by
    show trace (dMat d * Yl) = _
    rw [trace_dMat, trace_dMat]
    exact sum_congr rfl fun a _ => by simp [Yl, InLL]
  have hdiag : ∀ a, (Y a a).re = 0 := fun a => by
    have := congrArg Complex.re (congrFun (congrFun hY a) a)
    simp only [Jm, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, conjTranspose_apply,
      Matrix.zero_apply] at this
    split_ifs at this <;> simp at this <;> linarith
  set Z : Matrix (Fin n) (Fin n) ℂ := (((Real.sqrt t)⁻¹ : ℝ) : ℂ) • Y with hZ
  have hZG : inG ε Z := by
    have hY' : Yᴴ * Jm ε + Jm ε * Y = 0 := hY
    show Zᴴ * Jm ε + Jm ε * Z = 0
    rw [hZ, conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
      Matrix.mul_smul, ← smul_add, hY', smul_zero]
  have key := N.one_param w hw1 φ dl (stJ ε) hC'0 hCd0 zero_le_one hK ht hdn hstn
    (fun X X' => by simp [stJ, Matrix.mul_add, Matrix.add_mul])
    (fun X => by
      show trace (dMat d * stJ ε X) = starRingEnd ℂ (trace (dMat d * X))
      rw [trace_dMat, trace_dMat, map_sum]
      refine sum_congr rfl fun a _ => ?_
      rw [stJ_apply]; split_ifs <;> simp)
    Yl Yp Ym (Y * Ym - Ym * Y)
    (fun τ => NormedSpace.exp ((τ : ℂ) • Y) * Ym * NormedSpace.exp (-((τ : ℂ) • Y)))
    (by rw [hdl, trace_dMat, Complex.re_sum]; exact sum_eq_zero fun a _ => by simp [hdiag])
    (fun τ hτ => hT Y Ym hYn hYmn τ hτ.1 hτ.2)
    (hNP Yp (hpart _) fun a b h => by
      by_contra h'; exact h (by simp [Yp, h']))
    (hNP _ ((hstn Ym).trans (by simpa using hYmn)) fun a b h => by
      by_contra h'
      apply h
      rw [← norm_eq_zero, norm_stJ_apply, norm_eq_zero]
      simp [hYm, partNM, InNM, h'])
    (by
      rw [hsub]
      refine (act_bound (smE ε σ) ⟨w, hw⟩ d t C Yl fun a b h => bl a b ?_).trans (hbd Yl (hpart _))
      by_contra h'; exact h (by simp [Yl, h']))
    (fun X => by
      rw [hsub]
      refine (ball X).trans ?_
      have h1 := l1_le_card_mul_norm X
      have h0 : 0 ≤ C * Real.sqrt t := by positivity
      calc C * Real.sqrt t * l1 X ≤ C * Real.sqrt t * ((n : ℝ) ^ 2 * ‖X‖) :=
            mul_le_mul_of_nonneg_left h1 h0
        _ ≤ C' * Real.sqrt t * ‖X‖ := by
            rw [hC']
            have : 0 ≤ C * Real.sqrt t * ((n : ℝ) ^ 2 * ‖X‖) * |R| := by positivity
            nlinarith)
    (fun s => σ (NormedSpace.exp ((s : ℂ) • Z)))
    (fun s v => hσ.2.1 _ (exp_smul_mem_UJset hZG s) v)
    (by simp [hσ.1.1])
    (fun s _ => by rw [hsum, ← hφ]; exact h3b n ε H σ w hσ hw Z hZG s)
    (fun s _ => by
      have := h3a n ε H σ w hσ hw _ (exp_smul_mem_UJset hZG s) Ym
      rw [hφ, hφ, ← Matrix.exp_neg] at this
      have e : (s : ℂ) • Z = ((s / Real.sqrt t : ℝ) : ℂ) • Y := by
        rw [hZ, smul_smul]; push_cast; rw [div_eq_mul_inv]
      rw [this, e])
  have hρ : ‖Y * Ym - Ym * Y‖ ≤ ρb := by
    have a1 := (norm_mul_le_n Y Ym).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul hYn hYmn (norm_nonneg _) (abs_nonneg _)) (Nat.cast_nonneg n))
    have a2 := (norm_mul_le_n Ym Y).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul hYmn hYn (norm_nonneg _) (abs_nonneg _)) (Nat.cast_nonneg n))
    have := norm_sub_le (Y * Ym) (Ym * Y)
    rw [hρb]; linarith
  have hq : -(qForm ε d Y) = dl (Y * Ym - Ym * Y) := by rw [qForm, neg_neg]; rfl
  rw [hq, ← hdl]
  simp only [Complex.ofReal_one, one_smul] at key
  refine key.trans ?_
  rw [div_mul_eq_mul_div]
  have hd2 : ‖dl (Y * Ym - Ym * Y)‖ ≤ Cd * ρb :=
    (hdn _).trans (mul_le_mul_of_nonneg_left hρ hCd0)
  have hρ0 : 0 ≤ ρb := by positivity
  gcongr

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
