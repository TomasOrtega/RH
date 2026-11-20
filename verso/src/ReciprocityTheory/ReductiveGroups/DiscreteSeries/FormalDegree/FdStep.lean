import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.ProdSubLtEqFactorial

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem fdS_strictAnti {lam : Fin n → ℝ} (hlam : StrictAnti lam) {c : Fin n → ℕ} (hc : Antitone c) :
    StrictAnti (lam + fun i => (c i : ℝ)) := by
  intro i j hij
  simp only [Pi.add_apply]
  exact add_lt_add_of_lt_of_le (hlam hij) (by exact_mod_cast hc hij.le)

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Move the embeddings inside the algebraic operations. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem fdS_hc {lam : Fin n → ℝ} (hlam : IsHCParam lam) {c : Fin n → ℕ} (hc : Antitone c) :
    IsHCParam (lam + fun i => (c i : ℝ)) := by
  unfold IsHCParam at hlam ⊢
  refine ⟨fdS_strictAnti hlam.1 hc, fun a => ?_⟩
  obtain ⟨m, hm⟩ := hlam.2 a
  refine ⟨m + (c a : ℤ), ?_⟩
  simp only [Pi.add_apply]
  push_cast
  linarith

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Separate the alternatives or extract the components of the hypothesis.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion.

A detailed English derivation is pending.
-/
theorem fdS_gap {ε : Fin n → Bool} {h : ℝ} {lam : Fin n → ℝ} (hlam : StrictAnti lam)
    (hgap : GapAtLeast ε lam h) {c : Fin n → ℕ} (hc : Antitone c) :
    GapAtLeast ε (lam + fun i => (c i : ℝ)) h := by
  unfold GapAtLeast at hgap ⊢
  intro a b hab
  have h0 := hgap a b hab
  simp only [Pi.add_apply]
  rcases lt_trichotomy a b with hlt | heq | hgt
  · have h1 := hlam hlt
    have h2 : (c b : ℝ) ≤ c a := by exact_mod_cast hc hlt.le
    rw [abs_of_pos (by linarith)] at h0
    rw [abs_of_pos (by linarith)]
    linarith
  · exact absurd (congrArg ε heq) hab
  · have h1 := hlam hgt
    have h2 : (c a : ℝ) ≤ c b := by exact_mod_cast hc hgt.le
    rw [abs_of_neg (by linarith)] at h0
    rw [abs_of_neg (by linarith)]
    linarith

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. A detailed English derivation is pending.
-/
private theorem vand_ne_zero_of_strictAnti {μ : Fin n → ℝ} (hμ : StrictAnti μ) : Vand μ ≠ 0 := by
  unfold Vand
  refine Finset.prod_ne_zero_iff.mpr (fun a _ => Finset.prod_ne_zero_iff.mpr (fun b hb => ?_))
  have hab : a < b := (Finset.mem_filter.mp hb).2
  exact sub_ne_zero.mpr (hμ hab).ne'

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Clear the denominators using the available nonvanishing facts.
-/
theorem fdS_stepQ {ε : Fin n → Bool} {h : ℝ} (dfun : (Fin n → ℝ) → ℝ)
    (hstep : ∀ (μ : Fin n → ℝ) (s : Fin n), IsHCParam μ → GapAtLeast ε μ h → GapAtLeast ε (μ + Pi.single s 1) h →
      StrictAnti (μ + Pi.single s 1) → dfun (μ + Pi.single s 1) = dfun μ * ratioV μ s)
    {μ : Fin n → ℝ} (hμ : IsHCParam μ) (hg : GapAtLeast ε μ h) (s : Fin n)
    (hg' : GapAtLeast ε (μ + Pi.single s 1) h) (hs : StrictAnti (μ + Pi.single s 1)) :
    dfun (μ + Pi.single s 1) / Vand (μ + Pi.single s 1) = dfun μ / Vand μ := by
  have hμ1 : StrictAnti μ := by unfold IsHCParam at hμ; exact hμ.1
  rw [hstep μ s hμ hg hg' hs, ratioV_eq_vand hμ1 s]
  have h1 := vand_ne_zero_of_strictAnti hμ1
  have h2 := vand_ne_zero_of_strictAnti hs
  field_simp

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use linear arithmetic over natural numbers and integers.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Move the embeddings inside the algebraic operations. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem fdS_main {ε : Fin n → Bool} {h : ℝ} (dfun : (Fin n → ℝ) → ℝ)
    (hstep : ∀ (μ : Fin n → ℝ) (s : Fin n), IsHCParam μ → GapAtLeast ε μ h → GapAtLeast ε (μ + Pi.single s 1) h →
      StrictAnti (μ + Pi.single s 1) → dfun (μ + Pi.single s 1) = dfun μ * ratioV μ s)
    {lam : Fin n → ℝ} (hlam : IsHCParam lam) (hgap : GapAtLeast ε lam h) :
    ∀ (N : ℕ) (c : Fin n → ℕ), Antitone c → ∑ i, c i = N →
      dfun (lam + fun i => (c i : ℝ)) / Vand (lam + fun i => (c i : ℝ)) = dfun lam / Vand lam := by
  have hlam1 : StrictAnti lam := by unfold IsHCParam at hlam; exact hlam.1
  intro N
  induction N with
  | zero =>
    intro c _ hsum
    have hc0 : ∀ i, c i = 0 := fun i => (Finset.sum_eq_zero_iff.mp hsum) i (Finset.mem_univ i)
    have hfun : (lam + fun i => (c i : ℝ)) = lam := by
      funext i
      simp [hc0 i]
    rw [hfun]
  | succ N ih =>
    intro c hc hsum
    have hne : (univ.filter (fun i => c i ≠ 0)).Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hemp
      have h0 : ∑ i, c i = 0 := Finset.sum_eq_zero (fun i hi => by simpa using hemp hi)
      omega
    obtain ⟨s, hs_mem, hs_max⟩ : ∃ s ∈ univ.filter (fun i => c i ≠ 0), ∀ j ∈ univ.filter (fun i => c i ≠ 0), j ≤ s :=
      ⟨_, Finset.max'_mem _ hne, fun j hj => Finset.le_max' _ j hj⟩
    have hcs : c s ≠ 0 := (Finset.mem_filter.mp hs_mem).2
    have hbig : ∀ j, s < j → c j = 0 := by
      intro j hj
      by_contra hcj
      exact absurd hj (not_lt.mpr (hs_max j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcj⟩)))
    set c' : Fin n → ℕ := fun i => if i = s then c i - 1 else c i with hc'_def
    have hcc : ∀ i, c i = c' i + (if i = s then 1 else 0) := by
      intro i
      simp only [hc'_def]
      by_cases h : i = s
      · rw [if_pos h, if_pos h, h]; omega
      · rw [if_neg h, if_neg h]; rfl
    have hc' : Antitone c' := by
      intro i j hij
      simp only [hc'_def]
      rcases eq_or_ne i s with hi | hi <;> rcases eq_or_ne j s with hj | hj
      · rw [hi, hj]
      · have hsj : s < j := lt_of_le_of_ne (hi ▸ hij) (Ne.symm hj)
        rw [if_neg hj, hbig j hsj]
        exact Nat.zero_le _
      · have h' := hc hij
        rw [if_pos hj, if_neg hi]
        omega
      · rw [if_neg hj, if_neg hi]
        exact hc hij
    have hsum' : ∑ i, c' i = N := by
      have h' : ∑ i, c i = ∑ i, c' i + 1 := by
        rw [Finset.sum_congr rfl (fun i _ => hcc i), Finset.sum_add_distrib]
        simp
      omega
    have hfun : (lam + fun i => (c' i : ℝ)) + Pi.single s 1 = lam + fun i => (c i : ℝ) := by
      funext i
      simp only [Pi.add_apply, Pi.single_apply]
      rw [hcc i]
      push_cast
      split_ifs <;> ring
    have hQ := fdS_stepQ dfun hstep (fdS_hc hlam hc') (fdS_gap hlam1 hgap hc') s
      (by rw [hfun]; exact fdS_gap hlam1 hgap hc) (by rw [hfun]; exact fdS_strictAnti hlam1 hc)
    rw [hfun] at hQ
    rw [hQ, ih c' hc' hsum']

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem fd_step {ε : Fin n → Bool} {h : ℝ} (dfun : (Fin n → ℝ) → ℝ)
    (hstep : ∀ (μ : Fin n → ℝ) (s : Fin n), IsHCParam μ → GapAtLeast ε μ h →
      GapAtLeast ε (μ + Pi.single s 1) h → StrictAnti (μ + Pi.single s 1) → dfun (μ + Pi.single s 1) = dfun μ * ratioV μ s)
    {lam : Fin n → ℝ} (hlam : IsHCParam lam) (hgap : GapAtLeast ε lam h) (t : ℕ) :
    dfun (lamT lam t) / Vand (lamT lam t) = dfun lam / Vand lam := by
  have hD : ∀ a : Fin n, ((n : ℝ) - 1) - ((a : ℕ) : ℝ) = ((n - 1 - (a : ℕ) : ℕ) : ℝ) := by
    intro a
    have ha := a.2
    rw [Nat.cast_sub (by omega : (a : ℕ) ≤ n - 1), Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hc : Antitone (fun a : Fin n => t * (n - 1 - (a : ℕ))) := by
    intro i j hij
    have h' := Fin.le_iff_val_le_val.mp hij
    exact Nat.mul_le_mul le_rfl (by omega)
  have hfun : lamT lam t = lam + fun i => (((fun a : Fin n => t * (n - 1 - (a : ℕ))) i : ℕ) : ℝ) := by
    funext i
    simp only [lamT, Pi.add_apply, Pi.smul_apply, Dvec, smul_eq_mul]
    rw [hD i]
    push_cast
    ring
  rw [hfun]
  exact fdS_main dfun hstep hlam hgap _ _ hc rfl

end ReciprocityTheory.ChartRestriction.DS
