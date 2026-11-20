import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Numerics
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}

section Num

variable {ε : Fin n → Bool}

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem dot_add_l (u v w : Fin n → ℝ) : dot (u + v) w = dot u w + dot v w := by
  simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem dot_add_r (u v w : Fin n → ℝ) : dot u (v + w) = dot u v + dot u w := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem dot_comm' (u v : Fin n → ℝ) : dot u v = dot v u := by
  simp only [dot, mul_comm]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem dot_neg_r (u v : Fin n → ℝ) : dot u (-v) = - dot u v := by
  simp only [dot, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
private theorem dot_sum_r {k : ℕ} (u : Fin n → ℝ) (f : Fin k → Fin n → ℝ) :
    dot u (∑ i, f i) = ∑ i, dot u (f i) := by
  simp only [dot, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem dot_root_r (u : Fin n → ℝ) (a b : Fin n) : dot u (root a b) = u a - u b := by
  simp [dot, root, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
private theorem root_swap (a b : Fin n) : root b a = - root a b := by
  unfold root
  rw [neg_sub]

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
private theorem nsq_nonneg'' (u : Fin n → ℝ) : 0 ≤ nsq u := by
  unfold nsq dot
  exact Finset.sum_nonneg fun a _ => mul_self_nonneg _

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem nsq_add'' (u v : Fin n → ℝ) : nsq (u + v) = nsq u + 2 * dot u v + nsq v := by
  unfold nsq
  rw [dot_add_l, dot_add_r, dot_add_r, dot_comm' v u]
  ring

/- English proof (translation)
Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
private theorem dot_le_sqrt (u v : Fin n → ℝ) : dot u v ≤ √(nsq u) * √(nsq v) := by
  have := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ u v
  simpa [nsq, dot, sq] using this

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem sqrt_nsq_add_le (u v : Fin n → ℝ) : √(nsq (u + v)) ≤ √(nsq u) + √(nsq v) := by
  have ha := nsq_nonneg'' u
  have hb := nsq_nonneg'' v
  have hs : 0 ≤ √(nsq u) + √(nsq v) := by positivity
  rw [← Real.sqrt_sq hs]
  apply Real.sqrt_le_sqrt
  rw [nsq_add'', add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]
  nlinarith [dot_le_sqrt u v]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem sqrt_nsq_sum_le {ι : Type*} (s : Finset ι) (f : ι → Fin n → ℝ) :
    √(nsq (∑ i ∈ s, f i)) ≤ ∑ i ∈ s, √(nsq (f i)) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [nsq, dot]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (sqrt_nsq_add_le _ _).trans (by linarith)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Supply the required witnesses or components.

Supply the required witnesses or components. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Replace the relevant objects with their definitions. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations.

A detailed English derivation is pending.
-/
private theorem pq_facts {a b : Fin n} (hε : ε a ≠ ε b) :
    1 ≤ (pOf ε : ℝ) ∧ 1 ≤ (qOf ε : ℝ) ∧ (pOf ε : ℝ) + (qOf ε : ℝ) = n := by
  have key : ∀ x y t : Bool, x ≠ y → x ≠ t → y = t := by decide
  have hex : ∀ t : Bool, ∃ c, ε c = t := by
    intro t
    by_cases h : ε a = t
    · exact ⟨a, h⟩
    · exact ⟨b, key _ _ _ hε h⟩
  obtain ⟨c1, hc1⟩ := hex true
  obtain ⟨c2, hc2⟩ := hex false
  have hp : 0 < pOf ε := Finset.card_pos.2 ⟨c1, by simp [hc1]⟩
  have hq : 0 < qOf ε := Finset.card_pos.2 ⟨c2, by simp [hc2]⟩
  have hpq : pOf ε + qOf ε = n := by
    unfold pOf qOf
    have := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (fun a => ε a = true)
    simpa using this
  refine ⟨?_, ?_, ?_⟩
  · exact_mod_cast hp
  · exact_mod_cast hq
  · exact_mod_cast hpq

/- English proof (translation)
Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem gap_gt {a b : Fin n} (hε : ε a ≠ ε b) {h : ℝ}
    (hbig : 2 * (n : ℝ) < h) :
    2 * (n : ℝ) - 3 < h ∧ (n : ℝ) - 1 < h := by
  have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  constructor <;> linarith

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Replace the relevant objects with their definitions. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
-/
theorem vogan_num {Λ ν : Fin n → ℝ} {j : ℕ} (hj : 1 ≤ j) (hν : IsNCSum ε j ν) {h : ℝ}
    (hbig : 2 * (n : ℝ) < h)
    (hc : casValK ε Λ + 2 * (j : ℝ) * (h - n + 1) ≤ casValK ε (Λ + ν)) :
    nsq (Λ + (2 : ℝ) • rhoC ε) ≤ nsq (Λ + ν + (2 : ℝ) • rhoC ε) := by
  obtain ⟨γ, -, hνeq⟩ := hν
  have hcard : ∀ s : Finset (Fin n), (s.card : ℝ) ≤ n := fun s => by
    have := Finset.card_le_univ s
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  have hbound : ∀ a, -(n : ℝ) / 2 ≤ rhoC ε a ∧ rhoC ε a ≤ (n : ℝ) / 2 := by
    intro a
    have h1 := hcard (univ.filter fun b => a < b ∧ ε b = ε a)
    have h2 := hcard (univ.filter fun b => b < a ∧ ε b = ε a)
    have h3 := (Nat.cast_nonneg (univ.filter fun b => a < b ∧ ε b = ε a).card : (0 : ℝ) ≤ _)
    have h4 := (Nat.cast_nonneg (univ.filter fun b => b < a ∧ ε b = ε a).card : (0 : ℝ) ≤ _)
    simp only [rhoC]
    constructor <;> linarith
  have hdot : -((j : ℝ) * n) ≤ dot (rhoC ε) ν := by
    rw [hνeq, dot_sum_r]
    simp only [dot_root_r]
    have hle : ∀ i ∈ (univ : Finset (Fin j)), -(n : ℝ) ≤ rhoC ε (γ i).1 - rhoC ε (γ i).2 :=
      fun i _ => by
        have := hbound (γ i).1
        have := hbound (γ i).2
        linarith
    have := Finset.sum_le_sum hle
    simpa using this
  have hjn : (j : ℝ) * n ≤ j * (h - n + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg j)
  unfold casValK at hc
  have e1 : Λ + (2 : ℝ) • rhoC ε = (Λ + rhoC ε) + rhoC ε := by rw [two_smul]; abel
  have e2 : Λ + ν + (2 : ℝ) • rhoC ε = ((Λ + rhoC ε) + rhoC ε) + ν := by rw [two_smul]; abel
  have e3 : Λ + ν + rhoC ε = (Λ + rhoC ε) + ν := by abel
  rw [e3, nsq_add'' (Λ + rhoC ε) ν] at hc
  rw [e1, e2, nsq_add'' ((Λ + rhoC ε) + rhoC ε) ν, dot_add_l (Λ + rhoC ε) (rhoC ε) ν]
  linarith

end Num

end ReciprocityTheory.ChartRestriction.DS.G2
