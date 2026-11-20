import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData

namespace GlobalTheory.LowestKType

open Formalism.IndefR.IndefiniteWeightData Formalism.IndefR.IndefiniteWeightData.WeightData

variable {D : WeightData}

/- English proof (translation)
Extract witnesses or component facts from the available result. Replace the relevant objects with their definitions. Use linear arithmetic over natural numbers and integers.
-/
lemma r_eq (h : D.Hyp) : D.r = D.p + D.q := by
  obtain ⟨hk, hj, hjm, -⟩ := h
  unfold WeightData.r WeightData.p WeightData.q
  omega

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
lemma nV_eq (h : D.Hyp) : D.nV = D.p + D.q + D.t := by
  unfold WeightData.nV
  rw [r_eq h]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
lemma nV_cast (h : D.Hyp) : (D.nV : ℚ) = D.p + D.q + D.t := by
  rw [nV_eq h]; push_cast; ring

/- English proof (translation)
Extract witnesses or component facts from the available result. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Use linear arithmetic over natural numbers and integers.
-/
lemma lam_tail (h : D.Hyp) (c : ℕ) : D.lam (D.p + c) = -D.b (D.j + c) := by
  obtain ⟨hk, hj, hjm, -⟩ := h
  unfold WeightData.lam WeightData.p
  rw [if_neg (by omega)]
  congr 2
  omega

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
lemma lam_step (h : D.Hyp) (i : ℕ) (h1 : 1 ≤ i) (h2 : i < D.r) :
    (D.lam (i + 1) : ℚ) + 1 ≤ D.lam i := by
  have : D.lam (i + 1) + 1 ≤ D.lam i := h.2.2.2.2.2.1 i h1 h2
  exact_mod_cast this

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
lemma aMinus_rev (c : ℕ) (hc : c ≤ D.q + 1) :
    D.aMinus (D.q + 1 - c) = ((D.b (D.j + c) : ℚ) - D.e) + (1 - (D.t : ℚ) - 2 * (c : ℚ)) / 2 := by
  have : D.q + 1 - (D.q + 1 - c) = c := by omega
  unfold WeightData.aMinus
  rw [this]

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Supply the required witnesses or components.
-/
lemma exists_half_r (h : D.Hyp) : ∃ u : ℕ, (D.q : ℚ) = 2 * u + 1 - D.p := by
  obtain ⟨u, hu⟩ := h.2.2.2.1
  rw [r_eq h] at hu
  have : (D.p : ℚ) + D.q = 2 * u + 1 := by exact_mod_cast hu
  exact ⟨u, by linarith⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
lemma weightData_t_odd (h : D.Hyp) : ∃ w : ℕ, (D.t : ℚ) = 2 * w + 1 := by
  obtain ⟨u, hu⟩ := h.2.2.2.2.1
  exact ⟨u, by exact_mod_cast hu⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
lemma aPlus_int (h : D.Hyp) (i : ℕ) : ∃ z : ℤ, D.aPlus i = z := by
  obtain ⟨u, hu⟩ := exists_half_r h
  obtain ⟨w, hw⟩ := weightData_t_odd h
  refine ⟨D.lam i + D.e - w - 1 + i - D.p, ?_⟩
  unfold WeightData.aPlus
  rw [nV_cast h, hu, hw]
  push_cast
  ring

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Replace the chosen expression with an arbitrary variable. Rewrite the conclusion using the stated equalities.

Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
lemma aMinus_int (h : D.Hyp) (s : ℕ) : ∃ z : ℤ, D.aMinus s = z := by
  obtain ⟨w, hw⟩ := weightData_t_odd h
  refine ⟨D.b (D.j + (D.q + 1 - s)) - D.e - w - ((D.q + 1 - s : ℕ) : ℤ), ?_⟩
  unfold WeightData.aMinus
  generalize D.q + 1 - s = c
  rw [hw]
  push_cast
  ring

/- English proof (translation)
Rewrite the indicated hypotheses using the stated equalities. Replace the relevant objects with their definitions. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions.

Expand and normalize the polynomial expressions, which then agree. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma theta_param (h : D.Hyp) (i : ℕ) (h2 : i ≤ D.nV) :
    D.thetaWt i + ((D.p : ℚ) - D.q) / 2 - D.e + D.rhoNV i = D.uSideTarget i := by
  rw [nV_eq h] at h2
  unfold WeightData.thetaWt WeightData.rhoNV WeightData.uSideTarget
  by_cases hi : i ≤ D.p
  · simp only [if_pos hi]
    unfold WeightData.aPlus
    ring
  · by_cases hi' : i ≤ D.p + D.t
    · simp only [if_neg hi, if_pos hi']
      rw [nV_cast h]
      ring
    · obtain ⟨c, rfl⟩ : ∃ c, i = D.p + D.t + c := ⟨i - D.p - D.t, by omega⟩
      have e1 : D.p + D.t + c - D.p - D.t = c := by omega
      simp only [if_neg hi, if_neg hi', e1]
      rw [aMinus_rev c (by omega), nV_cast h]
      push_cast
      ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Expand and normalize the polynomial expressions, which then agree.
-/
lemma lamPrime_param (h : D.Hyp) (i : ℕ) (h2 : i ≤ D.nV) :
    D.lamPrime i + D.rhoNV i = D.uSideTarget i - 1 / 2 := by
  rw [← theta_param h i h2]
  unfold WeightData.lamPrime WeightData.dTau
  ring

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma dTau_int (h : D.Hyp) : ∃ z : ℤ, D.dTau = z := by
  obtain ⟨u, hu⟩ := exists_half_r h
  refine ⟨D.p - u - 1 - D.e, ?_⟩
  unfold WeightData.dTau
  rw [hu]; push_cast; ring

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Replace the relevant objects with their definitions. Separate the alternatives or extract the components of the hypothesis.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Substitute using the available equality. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Move the embeddings inside the algebraic operations. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Move the embeddings inside the algebraic operations. Combine the linear equalities and inequalities to obtain the conclusion. Substitute using the available equality. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations. Combine the linear equalities and inequalities to obtain the conclusion.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations.

Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
-/
lemma target_step (h : D.Hyp) (hg : D.GapHyp) (i : ℕ) (h1 : 1 ≤ i) (h2 : i < D.nV) :
    D.uSideTarget (i + 1) + 1 ≤ D.uSideTarget i := by
  have hr := r_eq h
  rw [nV_eq h] at h2
  have ht : 1 ≤ D.t := h.2.2.2.2.1.pos
  unfold WeightData.uSideTarget
  rcases lt_trichotomy i D.p with hi | hi | hi
  · have a1 : i ≤ D.p := by omega
    have a2 : i + 1 ≤ D.p := by omega
    simp only [if_pos a1, if_pos a2]
    exact lam_step h i h1 (by omega)
  · subst hi
    have a2 : ¬ D.p + 1 ≤ D.p := by omega
    have a3 : D.p + 1 ≤ D.p + D.t := by omega
    have h4 := lam_tail h 0
    simp only [add_zero] at h4
    simp only [if_pos (le_refl D.p), if_neg a2, if_pos a3]
    rw [h4]
    have := hg.1
    push_cast
    linarith
  · have a1 : ¬ i ≤ D.p := by omega
    have a2 : ¬ i + 1 ≤ D.p := by omega
    simp only [if_neg a1, if_neg a2]
    rcases lt_trichotomy i (D.p + D.t) with hi' | hi' | hi'
    · have a3 : i ≤ D.p + D.t := by omega
      have a4 : i + 1 ≤ D.p + D.t := by omega
      simp only [if_pos a3, if_pos a4]
      push_cast
      linarith
    · subst hi'
      have a4 : ¬ D.p + D.t + 1 ≤ D.p + D.t := by omega
      have e1 : D.p + D.t + 1 - D.p - D.t = 1 := by omega
      have hq : D.q = D.m - D.j := rfl
      have := hg.2 (by omega)
      simp only [if_pos (le_refl (D.p + D.t)), if_neg a4, e1]
      push_cast
      linarith
    · have a3 : ¬ i ≤ D.p + D.t := by omega
      have a4 : ¬ i + 1 ≤ D.p + D.t := by omega
      simp only [if_neg a3, if_neg a4]
      obtain ⟨c, rfl⟩ : ∃ c, i = D.p + D.t + c := ⟨i - D.p - D.t, by omega⟩
      have e1 : D.p + D.t + c - D.p - D.t = c := by omega
      have e2 : D.p + D.t + c + 1 - D.p - D.t = c + 1 := by omega
      have h3 := lam_step h (D.p + c) (by omega) (by omega)
      rw [add_assoc, lam_tail h, lam_tail h] at h3
      rw [e1, e2]
      push_cast at h3
      linarith

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Supply the required witnesses or components. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Replace the relevant objects with their definitions. Move the embeddings inside the algebraic operations. Combine the linear equalities and inequalities to obtain the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
-/
theorem thetaSide : ThetaSideStatement := by
  intro D h hg
  refine ⟨fun i _ h2 => theta_param h i h2, fun i _ h2 => lamPrime_param h i h2, dTau_int h,
    ?_, ?_, ?_⟩
  · intro i _ _
    obtain ⟨d, hd⟩ := dTau_int h
    unfold WeightData.lamPrime WeightData.thetaWt
    rw [hd]
    split_ifs
    · obtain ⟨z, hz⟩ := aPlus_int h i
      exact ⟨z + d, by rw [hz]; push_cast; ring⟩
    · exact ⟨d, by ring⟩
    · obtain ⟨z, hz⟩ := aMinus_int h (D.q + 1 - (i - D.p - D.t))
      exact ⟨-z + d, by rw [hz]; push_cast; ring⟩
  · intro i h1 h2
    have h3 := target_step h hg i h1 h2
    have h4 := lamPrime_param h i h2.le
    have h5 := lamPrime_param h (i + 1) h2
    unfold WeightData.rhoNV at h4 h5
    push_cast at h5
    linarith
  · intro i h1 h2
    have h3 := target_step h hg i h1 h2
    rw [lamPrime_param h i h2.le, lamPrime_param h (i + 1) h2]
    linarith

end GlobalTheory.LowestKType
