import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.ProdSubLtEqFactorial
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PBridge
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.RaisingLoweringNormIdentities

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

/- English proof (translation)
Simplify using `only [Lap.Base.dMat, Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]`. Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations. Simplify using `[pmat]`.
-/
theorem trace_dMat_pmat {ε : Fin n → Bool} (y : PCoord ε → ℂ) : trace (Lap.Base.dMat (Dvec n) * pmat y) = 0 := by
  simp only [Lap.Base.dMat, Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]
  refine Finset.sum_eq_zero fun a _ => ?_
  simp [pmat]

/- English proof (translation)
Simplify using `only [pmat]`. Distinguish the cases in `h1 : a < b ∧ ε b ≠ ε a`. Establish `h2 : ¬ (b < a ∧ ε a ≠ ε b)` using `fun h => lt_asymm h.1 h1.1`. Simplify using `only [dif_pos h1, dif_neg h2, star_star]`. Distinguish the cases in `h2 : b < a ∧ ε a ≠ ε b`.

Simplify using `only [dif_neg h1, dif_pos h2]`. Simplify using `only [dif_neg h1, dif_neg h2, star_zero]`.
-/
theorem pmat_herm_apply {ε : Fin n → Bool} (y : PCoord ε → ℂ) (a b : Fin n) :
    pmat y b a = star (pmat y a b) := by
  simp only [pmat]
  by_cases h1 : a < b ∧ ε b ≠ ε a
  · have h2 : ¬ (b < a ∧ ε a ≠ ε b) := fun h => lt_asymm h.1 h1.1
    simp only [dif_pos h1, dif_neg h2, star_star]
  · by_cases h2 : b < a ∧ ε a ≠ ε b
    · simp only [dif_neg h1, dif_pos h2]
    · simp only [dif_neg h1, dif_neg h2, star_zero]

/- English proof (translation)
Establish `key : ∀ x : Fin n × Fin n, (if x.2 < x.1 then w x.1 x.2 * ‖pmat z x.1 x.2‖ ^ 2 else 0) = (if h : x.2 < x.1 ∧ ε x.1 ≠ ε x.2 then w x.1 x.2 * ‖z ⟨x, h⟩‖ ^ 2 else 0)`. Introduce and unpack `⟨a, b⟩`. Simplify using `only`. Distinguish the cases in `h : b < a ∧ ε a ≠ ε b`. Rewrite using `[dif_pos h, if_pos h.1]`.

Establish `hp : pmat z a b = z ⟨(a, b), h⟩`. Simplify using `only [pmat, dif_pos h]`. Rewrite using `[hp]`. Rewrite using `[dif_neg h] split_ifs with hab`. Establish `h2 : ¬ (a < b ∧ ε b ≠ ε a)` using `fun h' => lt_asymm hab h'.1`.

Establish `hp : pmat z a b = 0`. Simplify using `only [pmat, dif_neg h, dif_neg h2]`. Rewrite using `[hp]`. Simplify using the standard rewrite rules. Both sides reduce to the same expression.

Rewrite using `[Finset.sum_congr rfl (fun x _ => key x)]`. Rewrite using `[← Finset.sum_filter_of_ne (p := fun x : Fin n × Fin n => x.2 < x.1 ∧ ε x.1 ≠ ε x.2) (fun x _ hx => by`. Assume the negation of the conclusion as `h`. Conclude with `hx (dif_neg h))]`. Rewrite using `[Finset.sum_subtype (p := fun x : Fin n × Fin n => x.2 < x.1 ∧ ε x.1 ≠ ε x.2) _ (fun x => by simp)]`.

Use `Finset.sum_congr rfl fun ab _ => ?_` and prove the remaining obligations. Conclude with `dif_pos ab.2`.
-/
theorem sum_pairs_pmat_fp {ε : Fin n → Bool} (w : Fin n → Fin n → ℝ) (z : PCoord ε → ℂ) :
    ∑ x : Fin n × Fin n, (if x.2 < x.1 then w x.1 x.2 * ‖pmat z x.1 x.2‖ ^ 2 else 0) =
      ∑ ab : PCoord ε, w ab.1.1 ab.1.2 * ‖z ab‖ ^ 2 := by
  classical
  have key : ∀ x : Fin n × Fin n, (if x.2 < x.1 then w x.1 x.2 * ‖pmat z x.1 x.2‖ ^ 2 else 0) =
      (if h : x.2 < x.1 ∧ ε x.1 ≠ ε x.2 then w x.1 x.2 * ‖z ⟨x, h⟩‖ ^ 2 else 0) := by
    rintro ⟨a, b⟩
    dsimp only
    by_cases h : b < a ∧ ε a ≠ ε b
    · rw [dif_pos h, if_pos h.1]
      have hp : pmat z a b = z ⟨(a, b), h⟩ := by
        simp only [pmat, dif_pos h]
      rw [hp]
    · rw [dif_neg h]
      split_ifs with hab
      · have h2 : ¬ (a < b ∧ ε b ≠ ε a) := fun h' => lt_asymm hab h'.1
        have hp : pmat z a b = 0 := by
          simp only [pmat, dif_neg h, dif_neg h2]
        rw [hp]; simp
      · rfl
  rw [Finset.sum_congr rfl (fun x _ => key x)]
  rw [← Finset.sum_filter_of_ne (p := fun x : Fin n × Fin n => x.2 < x.1 ∧ ε x.1 ≠ ε x.2)
    (fun x _ hx => by
      by_contra h
      exact hx (dif_neg h))]
  rw [Finset.sum_subtype (p := fun x : Fin n × Fin n => x.2 < x.1 ∧ ε x.1 ≠ ε x.2) _
    (fun x => by simp)]
  refine Finset.sum_congr rfl fun ab _ => ?_
  exact dif_pos ab.2

/- English proof (translation)
Simplify using `only [pmat]`. Rewrite using `[dif_neg (fun h => h.2 he), dif_neg (fun h => h.2 he.symm)]`.
-/
private theorem pmat_apply_eq_zero_of_sign_eq {ε : Fin n → Bool} (y : PCoord ε → ℂ) {a b : Fin n} (he : ε a = ε b) :
    pmat y a b = 0 := by
  simp only [pmat]
  rw [dif_neg (fun h => h.2 he), dif_neg (fun h => h.2 he.symm)]

/- English proof (translation)
Establish `hD : ((Dvec n a : ℝ) : ℂ) - ((Dvec n b : ℝ) : ℂ) = ((((b : ℕ) : ℝ) - ((a : ℕ) : ℝ) : ℝ) : ℂ)`. Simplify using `only [Dvec]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `h : b < a ∧ ε a ≠ ε b`.

Establish `hin : Lap.Base.InNM ε (Dvec n) b a` using `Or.inr h`. Establish `hN : Lap.Base.partNM ε (Dvec n) (pmat y) b a = pmat y b a`. Rewrite using `[Lap.Base.partNM, Matrix.of_apply, if_pos hin]`. Rewrite using `[hN, if_pos h.1, hD, pmat_herm_apply y a b, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `h0 : pmat y a b * Lap.Base.partNM ε (Dvec n) (pmat y) b a = 0`. Rewrite using `[Lap.Base.partNM, Matrix.of_apply]`. Use `split_ifs with hin`. Break down `hin with ⟨_, he, _⟩ | h'` into its components or cases.

Rewrite using `[pmat_apply_eq_zero_of_sign_eq y he, zero_mul]`. Conclude with `absurd h' h`. Conclude with `mul_zero _`. Rewrite using `[h0, mul_zero, neg_zero]`. Use `split_ifs with hba`.

Establish `he : ε a = ε b`. Assume the negation of the conclusion as `he`. Conclude with `h ⟨hba, he⟩`. Rewrite using `[pmat_apply_eq_zero_of_sign_eq y he]`. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
theorem qForm_term {ε : Fin n → Bool} (y : PCoord ε → ℂ) (a b : Fin n) :
    -((((Dvec n a : ℝ) : ℂ) - ((Dvec n b : ℝ) : ℂ)) * (pmat y a b * Lap.Base.partNM ε (Dvec n) (pmat y) b a)) =
      (((if b < a then (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) * ‖pmat y a b‖ ^ 2 else 0 : ℝ)) : ℂ) := by
  have hD : ((Dvec n a : ℝ) : ℂ) - ((Dvec n b : ℝ) : ℂ) = ((((b : ℕ) : ℝ) - ((a : ℕ) : ℝ) : ℝ) : ℂ) := by
    simp only [Dvec]; push_cast; ring
  by_cases h : b < a ∧ ε a ≠ ε b
  · have hin : Lap.Base.InNM ε (Dvec n) b a := Or.inr h
    have hN : Lap.Base.partNM ε (Dvec n) (pmat y) b a = pmat y b a := by
      rw [Lap.Base.partNM, Matrix.of_apply, if_pos hin]
    rw [hN, if_pos h.1, hD, pmat_herm_apply y a b, Complex.star_def, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast; ring
  · have h0 : pmat y a b * Lap.Base.partNM ε (Dvec n) (pmat y) b a = 0 := by
      rw [Lap.Base.partNM, Matrix.of_apply]
      split_ifs with hin
      · rcases hin with ⟨_, he, _⟩ | h'
        · rw [pmat_apply_eq_zero_of_sign_eq y he, zero_mul]
        · exact absurd h' h
      · exact mul_zero _
    rw [h0, mul_zero, neg_zero]
    split_ifs with hba
    · have he : ε a = ε b := by
        by_contra he
        exact h ⟨hba, he⟩
      rw [pmat_apply_eq_zero_of_sign_eq y he]; simp
    · simp

/- English proof (translation)
Establish `h1 : Lap.Base.qForm ε (Dvec n) (pmat y) = ∑ a : Fin n, ∑ b : Fin n, -((((Dvec n a : ℝ) : ℂ) - ((Dvec n b : ℝ) : ℂ)) * (pmat y a b * Lap.Base.partNM ε (Dvec n) (pmat y) b a))`. Establish `e : ∀ a b : Fin n, -((((Dvec n a : ℝ) : ℂ) - ((Dvec n b : ℝ) : ℂ)) * (pmat y a b * Lap.Base.partNM ε (Dvec n) (pmat y) b a)) = -(((Dvec n a : ℝ) : ℂ) * (pmat y a b * Lap.Base.partNM ε (Dvec n) (pmat y) b a)) + ((Dvec n b : ℝ) : ℂ) * (Lap.Base.partNM ε (Dvec n) (pmat y) b a * pmat …` using `fun a b => by ring`. Repeatedly rewrite using `[e, Finset.sum_add_distrib, Finset.sum_neg_distrib]`. Rewrite using `[Finset.sum_comm (f := fun a b : Fin n => ((Dvec n b : ℝ) : ℂ) * (Lap.Base.partNM ε (Dvec n) (pmat y) b a * pmat y a b))]`. Simplify using `only [Lap.Base.qForm, Lap.Base.dMat, Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]`.

Simplify using `only [Matrix.sub_apply, Matrix.mul_apply, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1]`. Simplify using `only [qForm_term]`. Establish `e2` using `sum_pairs_pmat_fp (fun a b : Fin n => ((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) y`.

Rewrite `e2` using `[Fintype.sum_prod_type' (f := fun a b : Fin n => (if b < a then (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) * ‖pmat y a b‖ ^ 2 else 0 : ℝ))]`. Rewrite `e2` using `[← Complex.ofReal_inj]`. Simplify using `only [Complex.ofReal_sum] at e2`. Rewrite using `[e2, ← Complex.ofReal_sum]`. Use `congr 1`.

Simplify using `only [Qf, wab, Pi.zero_apply, sub_self, zero_add]`.
-/
theorem qForm_pmat {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    Lap.Base.qForm ε (Dvec n) (pmat y) = ((Qf (0 : Fin n → ℝ) y : ℝ) : ℂ) := by
  have h1 : Lap.Base.qForm ε (Dvec n) (pmat y) = ∑ a : Fin n, ∑ b : Fin n,
      -((((Dvec n a : ℝ) : ℂ) - ((Dvec n b : ℝ) : ℂ)) *
        (pmat y a b * Lap.Base.partNM ε (Dvec n) (pmat y) b a)) := by
    have e : ∀ a b : Fin n, -((((Dvec n a : ℝ) : ℂ) - ((Dvec n b : ℝ) : ℂ)) *
        (pmat y a b * Lap.Base.partNM ε (Dvec n) (pmat y) b a)) =
        -(((Dvec n a : ℝ) : ℂ) * (pmat y a b * Lap.Base.partNM ε (Dvec n) (pmat y) b a)) +
          ((Dvec n b : ℝ) : ℂ) * (Lap.Base.partNM ε (Dvec n) (pmat y) b a * pmat y a b) :=
      fun a b => by ring
    simp_rw [e, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    rw [Finset.sum_comm (f := fun a b : Fin n =>
      ((Dvec n b : ℝ) : ℂ) * (Lap.Base.partNM ε (Dvec n) (pmat y) b a * pmat y a b))]
    simp only [Lap.Base.qForm, Lap.Base.dMat, Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]
    simp only [Matrix.sub_apply, Matrix.mul_apply, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
    ring
  rw [h1]
  simp only [qForm_term]
  have e2 := sum_pairs_pmat_fp (fun a b : Fin n => ((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) y
  rw [Fintype.sum_prod_type' (f := fun a b : Fin n =>
    (if b < a then (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) * ‖pmat y a b‖ ^ 2 else 0 : ℝ))] at e2
  rw [← Complex.ofReal_inj] at e2
  simp only [Complex.ofReal_sum] at e2
  rw [e2, ← Complex.ofReal_sum]
  congr 1
  simp only [Qf, wab, Pi.zero_apply, sub_self, zero_add]

/- English proof (translation)
Take `⟨C, hC⟩` from `hB3 n ε (Dvec n) (lowK ε lam) (S7.hs (pmat y) + 1)`. Establish `hinG : inG ε (pmat y)`. Unfold `inG Jm`. Use extensionality with `a b`. Simplify using `only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, Matrix.zero_apply]`.

Rewrite using `[pmat_herm_apply y a b, star_star]`. Distinguish the cases in `he : ε a = ε b`. Rewrite using `[pmat_apply_eq_zero_of_sign_eq y he]`. Simplify using the standard rewrite rules. Apply the tactic sequence `cases ha : ε a <;> cases hb : ε b <;> simp_all`.

Establish `hR : S7.hs (pmat y) ≤ (S7.hs (pmat y) + 1) ^ 2`. Use polynomial arithmetic with `[sq_nonneg (S7.hs (pmat y) + 1 / 2)]`. Establish `hsq : Filter.Tendsto (fun t : ℕ => Real.sqrt (t : ℝ)) Filter.atTop Filter.atTop`. Use `Filter.tendsto_atTop_atTop.mpr fun b => ⟨⌈b ^ 2⌉₊, fun a ha => ?_⟩` and prove the remaining obligations. Use `(le_abs_self b).trans (Real.abs_le_sqrt ?_)` and prove the remaining obligations.

Conclude with `(Nat.le_ceil _).trans (by exact_mod_cast ha)`. Establish `hC0 : Filter.Tendsto (fun t : ℕ => C / Real.sqrt (t : ℝ)) Filter.atTop (nhds 0)` using `tendsto_const_nhds.div_atTop hsq`. Rewrite using `[tendsto_iff_norm_sub_tendsto_zero]`. Use `squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hC0` and prove the remaining obligations. Use `filter_upwards [hsm, Filter.eventually_ge_atTop 1] with t ht ht1`.

Take `⟨H', i1, i2, σ', w', hw', heq⟩` from `ht`. Use `letI := i1`. Use `letI := i2`. Establish `hlow : lowK ε (lamT lam t) = (t : ℝ) • Dvec n + lowK ε lam`. Use extensionality with `a`.

Simplify using `only [lowK, lamT, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hb` using `hC (t : ℝ) (by exact_mod_cast ht1) H' σ' (lamT lam t) w' hw' hlow (pmat y) hinG hR`. Rewrite `hb` using `[trace_dMat_pmat y, qForm_pmat y, mul_zero, neg_zero, Complex.exp_zero, mul_one]`. Establish `hy : ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y) = ((Real.sqrt t)⁻¹ : ℝ) • y`.

Use extensionality with `ab`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Complex.real_smul]`. Establish `hL : (((Real.exp (-(Qf (0 : Fin n → ℝ) y / 2)) : ℝ) : ℂ)) = Complex.exp (-((Qf (0 : Fin n → ℝ) y : ℝ) : ℂ) / 2)`. Rewrite using `[Complex.ofReal_exp]`. Use `push_cast`.

Put the polynomial expressions in normal form. Rewrite using `[← heq, hy, adKAux_pmat_smul, hL]`. Conclude with `hb`.
-/
theorem matrix_coefficient_pointwise_limit (hB3 : Lap.Base.TangentPairingStatement) {ε : Fin n → Bool} {lam : Fin n → ℝ} (H : ℕ → Type)
    [∀ t, NormedAddCommGroup (H t)] [∀ t, InnerProductSpace ℂ (H t)] [∀ t, CompleteSpace (H t)]
    (σ : ∀ t : ℕ, Matrix (Fin n) (Fin n) ℂ → (H t →L[ℂ] H t)) (T : ∀ t : ℕ, KType ε (lowK ε (lamT lam t)))
    (j : ∀ t : ℕ, (T t).V →L[ℂ] H t)
    (hF : ∀ᶠ t in Filter.atTop, FData ε (lamT lam t) (σ t) (T t) (j t))
    (hsm : ∀ᶠ t in Filter.atTop, ∃ (H' : Type) (_ : NormedAddCommGroup H') (_ : InnerProductSpace ℂ H')
      (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) (w' : H'), Lap.Base.IsHWSmooth ε σ' (lamT lam t) w' ∧
        ∀ z : PCoord ε → ℂ, ⟪w', σ' (NormedSpace.exp (pmat z)) w'⟫_ℂ =
          ⟪(T t).w, fF ε (lamT lam t) (T t) (pmat z) (T t).w⟫_ℂ)
    (y : PCoord ε → ℂ) :
    Filter.Tendsto (fun t : ℕ => ⟪(T t).w, fF ε (lamT lam t) (T t) (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ) Filter.atTop
      (nhds ((Real.exp (-(Qf (0 : Fin n → ℝ) y / 2)) : ℝ) : ℂ)) := by
  obtain ⟨C, hC⟩ := hB3 n ε (Dvec n) (lowK ε lam) (S7.hs (pmat y) + 1)
  have hinG : inG ε (pmat y) := by
    unfold inG Jm
    ext a b
    simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
      Matrix.zero_apply]
    rw [pmat_herm_apply y a b, star_star]
    by_cases he : ε a = ε b
    · rw [pmat_apply_eq_zero_of_sign_eq y he]; simp
    · cases ha : ε a <;> cases hb : ε b <;> simp_all
  have hR : S7.hs (pmat y) ≤ (S7.hs (pmat y) + 1) ^ 2 := by
    nlinarith [sq_nonneg (S7.hs (pmat y) + 1 / 2)]
  have hsq : Filter.Tendsto (fun t : ℕ => Real.sqrt (t : ℝ)) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_atTop.mpr fun b => ⟨⌈b ^ 2⌉₊, fun a ha => ?_⟩
    refine (le_abs_self b).trans (Real.abs_le_sqrt ?_)
    exact (Nat.le_ceil _).trans (by exact_mod_cast ha)
  have hC0 : Filter.Tendsto (fun t : ℕ => C / Real.sqrt (t : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hsq
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hC0
  filter_upwards [hsm, Filter.eventually_ge_atTop 1] with t ht ht1
  obtain ⟨H', i1, i2, σ', w', hw', heq⟩ := ht
  letI := i1
  letI := i2
  have hlow : lowK ε (lamT lam t) = (t : ℝ) • Dvec n + lowK ε lam := by
    ext a
    simp only [lowK, lamT, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hb := hC (t : ℝ) (by exact_mod_cast ht1) H' σ' (lamT lam t) w' hw' hlow (pmat y) hinG hR
  rw [trace_dMat_pmat y, qForm_pmat y, mul_zero, neg_zero, Complex.exp_zero, mul_one] at hb
  have hy : ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y) = ((Real.sqrt t)⁻¹ : ℝ) • y := by
    ext ab
    simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul]
  have hL : (((Real.exp (-(Qf (0 : Fin n → ℝ) y / 2)) : ℝ) : ℂ)) =
      Complex.exp (-((Qf (0 : Fin n → ℝ) y : ℝ) : ℂ) / 2) := by
    rw [Complex.ofReal_exp]; push_cast; ring_nf
  rw [← heq, hy, adKAux_pmat_smul, hL]
  exact hb

end ReciprocityTheory.ChartRestriction.DS
