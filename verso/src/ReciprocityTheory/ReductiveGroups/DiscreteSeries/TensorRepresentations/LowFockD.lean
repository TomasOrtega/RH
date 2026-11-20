import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PRVComponents
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.WeylPos
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CarSumSqZeroOfAnti

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

/- English proof (translation)
Establish `key : ∀ c : Fin n, ((if a < c ∧ P c then 1 else 0) + (if c < b ∧ P c then 1 else 0) : ℕ) = (if c < a ∧ P c then 1 else 0) + (if b < c ∧ P c then 1 else 0) + 2 * (if a < c ∧ c < b ∧ P c then 1 else 0) + (if c = a ∧ P c then 1 else 0) + (if c = b ∧ P c then 1 else 0)`. Introduce `c`. Break down `lt_trichotomy c a with hca | rfl | hac` into its components or cases. Establish `h1 : ¬ a < c` using `not_lt_of_gt hca`. Establish `h2 : c < b` using `hca.trans hab`.

Establish `h3 : ¬ b < c` using `not_lt_of_gt h2`. Establish `h4 : c ≠ a` using `hca.ne`. Establish `h5 : c ≠ b` using `h2.ne`. Apply the tactic sequence `by_cases hP : P c <;> simp [h1, h2, h3, h4, h5, hca, hP]`. Establish `h3 : ¬ b < c` using `not_lt_of_gt hab`.

Establish `h5 : c ≠ b` using `hab.ne`. Apply the tactic sequence `by_cases hP : P c <;> simp [hab, h3, h5, hP]`. Break down `lt_trichotomy c b with hcb | rfl | hbc` into its components or cases. Establish `h1 : ¬ c < a` using `not_lt_of_gt hac`. Establish `h3 : ¬ b < c` using `not_lt_of_gt hcb`.

Establish `h4 : c ≠ a` using `hac.ne'`. Establish `h5 : c ≠ b` using `hcb.ne`. Apply the tactic sequence `by_cases hP : P c <;> simp [hac, hcb, h1, h3, h4, h5, hP]`. Establish `h1 : ¬ c < a` using `not_lt_of_gt hac`. Establish `h4 : c ≠ a` using `hac.ne'`.

Apply the tactic sequence `by_cases hP : P c <;> simp [hac, h1, h4, hP]`. Establish `h1 : ¬ c < a` using `not_lt_of_gt hac`. Establish `h2 : ¬ c < b` using `not_lt_of_gt hbc`. Establish `h4 : c ≠ a` using `hac.ne'`. Establish `h5 : c ≠ b` using `hbc.ne'`.

Apply the tactic sequence `by_cases hP : P c <;> simp [hac, hbc, h1, h2, h4, h5, hP]`. Simplify using `only [Finset.card_filter, Finset.mul_sum, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl (fun c _ => key c)`.
-/
theorem lfD_cnt (P : Fin n → Prop) [DecidablePred P] {a b : Fin n} (hab : a < b) :
    (univ.filter fun c => a < c ∧ P c).card + (univ.filter fun c => c < b ∧ P c).card =
      (univ.filter fun c => c < a ∧ P c).card + (univ.filter fun c => b < c ∧ P c).card +
        2 * (univ.filter fun c => a < c ∧ c < b ∧ P c).card +
        (univ.filter fun c => c = a ∧ P c).card + (univ.filter fun c => c = b ∧ P c).card := by
  have key : ∀ c : Fin n, ((if a < c ∧ P c then 1 else 0) + (if c < b ∧ P c then 1 else 0) : ℕ) =
      (if c < a ∧ P c then 1 else 0) + (if b < c ∧ P c then 1 else 0) +
        2 * (if a < c ∧ c < b ∧ P c then 1 else 0) + (if c = a ∧ P c then 1 else 0) +
        (if c = b ∧ P c then 1 else 0) := by
    intro c
    rcases lt_trichotomy c a with hca | rfl | hac
    · have h1 : ¬ a < c := not_lt_of_gt hca
      have h2 : c < b := hca.trans hab
      have h3 : ¬ b < c := not_lt_of_gt h2
      have h4 : c ≠ a := hca.ne
      have h5 : c ≠ b := h2.ne
      by_cases hP : P c <;> simp [h1, h2, h3, h4, h5, hca, hP]
    · have h3 : ¬ b < c := not_lt_of_gt hab
      have h5 : c ≠ b := hab.ne
      by_cases hP : P c <;> simp [hab, h3, h5, hP]
    · rcases lt_trichotomy c b with hcb | rfl | hbc
      · have h1 : ¬ c < a := not_lt_of_gt hac
        have h3 : ¬ b < c := not_lt_of_gt hcb
        have h4 : c ≠ a := hac.ne'
        have h5 : c ≠ b := hcb.ne
        by_cases hP : P c <;> simp [hac, hcb, h1, h3, h4, h5, hP]
      · have h1 : ¬ c < a := not_lt_of_gt hac
        have h4 : c ≠ a := hac.ne'
        by_cases hP : P c <;> simp [hac, h1, h4, hP]
      · have h1 : ¬ c < a := not_lt_of_gt hac
        have h2 : ¬ c < b := not_lt_of_gt hbc
        have h4 : c ≠ a := hac.ne'
        have h5 : c ≠ b := hbc.ne'
        by_cases hP : P c <;> simp [hac, hbc, h1, h2, h4, h5, hP]
  simp only [Finset.card_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun c _ => key c)

/- English proof (translation)
Rewrite using `[Finset.card_filter, Finset.sum_eq_single a]`. Simplify using the standard rewrite rules. Introduce `c _ hc`. Simplify using `[hc]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ a) h`.
-/
theorem lfD_single (P : Fin n → Prop) [DecidablePred P] (a : Fin n) :
    (univ.filter fun c => c = a ∧ P c).card = if P a then 1 else 0 := by
  rw [Finset.card_filter, Finset.sum_eq_single a]
  · simp
  · intro c _ hc
    simp [hc]
  · intro h
    exact absurd (Finset.mem_univ a) h

/- English proof (translation)
Use `⟨(univ.filter fun c => a < c ∧ c < b ∧ ε c ≠ ε a).card, ?_⟩` and prove the remaining obligations. Establish `hc` using `lfD_cnt (fun c => ε c ≠ ε a) hab`. Rewrite `hc` using `[lfD_single, lfD_single, if_neg (fun h => h rfl), if_neg (fun h => h he.symm)]`. Establish `hr` using `congrArg (Nat.cast : ℕ → ℝ) hc`. Move the coercions through the operations in `at hr`.

Simplify using `only [rhoN, ← he]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lf_rhoN_sub_nat (ε : Fin n → Bool) {a b : Fin n} (hab : a < b) (he : ε a = ε b) :
    ∃ m : ℕ, rhoN ε a - rhoN ε b = m := by
  refine ⟨(univ.filter fun c => a < c ∧ c < b ∧ ε c ≠ ε a).card, ?_⟩
  have hc := lfD_cnt (fun c => ε c ≠ ε a) hab
  rw [lfD_single, lfD_single, if_neg (fun h => h rfl), if_neg (fun h => h he.symm)] at hc
  have hr := congrArg (Nat.cast : ℕ → ℝ) hc
  push_cast at hr
  simp only [rhoN, ← he]
  linarith

/- English proof (translation)
Simplify using `only [rhoHol, he]`.
-/
theorem lf_rhoHol_eq (ε : Fin n → Bool) {a b : Fin n} (he : ε a = ε b) : rhoHol ε a = rhoHol ε b := by
  simp only [rhoHol, he]

/- English proof (translation)
It suffices to establish `H : ∀ d, ∀ a b : Fin n, b.val - a.val = d → a < b → ε a = ε b → (lowK ε lam + (rhoHol ε - rhoN ε)) b ≤ (lowK ε lam + (rhoHol ε - rhoN ε)) a by`. Introduce `a b hab he`. Conclude with `H _ a b rfl hab he`. Introduce `d`. Proceed by induction on `d using Nat.strong_induction_on with`.

Consider the case `_ d ih`. Introduce `a b hd hab he`. Distinguish the cases in `hmid : ∃ c, a < c ∧ c < b ∧ ε c = ε a`. Take `⟨c, hac, hcb, hce⟩` from `hmid`. Establish `hac'` using `Fin.lt_def.mp hac`.

Establish `hcb'` using `Fin.lt_def.mp hcb`. Establish `h1` using `ih (c.val - a.val) (by omega) a c rfl hac hce.symm`. Establish `h2` using `ih (b.val - c.val) (by omega) c b rfl hcb (hce.trans he)`. Conclude with `h2.trans h1`. Simplify using `only [not_exists, not_and] at hmid`.

Establish `hC` using `HW.rhoC_consec ε hab he hmid`. Take `⟨m, hm⟩` from `HW.kIrrHW_int ε hF hV a b hab he`. Take `⟨k, hk⟩` from `lf_rhoN_sub_nat ε hab he`. Establish `hH` using `lf_rhoHol_eq ε he`. Establish `hl` using `hlam hab`.

Establish `hlk : lowK ε lam a - lowK ε lam b = lam a - lam b + (rhoN ε a - rhoN ε b) - (rhoC ε a - rhoC ε b)`. Simplify using `only [lowK, Pi.add_apply, Pi.sub_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `hkm : (k : ℝ) < m + 1` using `by linarith`. Establish `hkm' : k < m + 1` using `by exact_mod_cast hkm`.

Establish `hkm'' : (k : ℝ) ≤ m` using `by exact_mod_cast Nat.lt_succ_iff.mp hkm'`. Simplify using `only [Pi.add_apply, Pi.sub_apply]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lf_dom {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : StrictAnti lam) {M : Type*} [AddCommGroup M]
    [Module ℂ M] {F : Fin n → Fin n → Module.End ℂ M} (hF : Formalism.REAL.KRel ε F) {V : Submodule ℂ M}
    (hV : IsKIrrHW ε F (lowK ε lam) V) :
    ∀ a b, a < b → ε a = ε b →
      (lowK ε lam + (rhoHol ε - rhoN ε)) b ≤ (lowK ε lam + (rhoHol ε - rhoN ε)) a := by
  suffices H : ∀ d, ∀ a b : Fin n, b.val - a.val = d → a < b → ε a = ε b →
      (lowK ε lam + (rhoHol ε - rhoN ε)) b ≤ (lowK ε lam + (rhoHol ε - rhoN ε)) a by
    intro a b hab he
    exact H _ a b rfl hab he
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro a b hd hab he
    by_cases hmid : ∃ c, a < c ∧ c < b ∧ ε c = ε a
    · obtain ⟨c, hac, hcb, hce⟩ := hmid
      have hac' := Fin.lt_def.mp hac
      have hcb' := Fin.lt_def.mp hcb
      have h1 := ih (c.val - a.val) (by omega) a c rfl hac hce.symm
      have h2 := ih (b.val - c.val) (by omega) c b rfl hcb (hce.trans he)
      exact h2.trans h1
    · simp only [not_exists, not_and] at hmid
      have hC := HW.rhoC_consec ε hab he hmid
      obtain ⟨m, hm⟩ := HW.kIrrHW_int ε hF hV a b hab he
      obtain ⟨k, hk⟩ := lf_rhoN_sub_nat ε hab he
      have hH := lf_rhoHol_eq ε he
      have hl := hlam hab
      have hlk : lowK ε lam a - lowK ε lam b =
          lam a - lam b + (rhoN ε a - rhoN ε b) - (rhoC ε a - rhoC ε b) := by
        simp only [lowK, Pi.add_apply, Pi.sub_apply]
        ring
      have hkm : (k : ℝ) < m + 1 := by linarith
      have hkm' : k < m + 1 := by exact_mod_cast hkm
      have hkm'' : (k : ℝ) ≤ m := by exact_mod_cast Nat.lt_succ_iff.mp hkm'
      simp only [Pi.add_apply, Pi.sub_apply]
      linarith

end ReciprocityTheory.ChartRestriction.DS
