import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.CompRevRev

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TwistedDualLemmas

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.LemK

variable {n : ℕ}

section Tens

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/- English proof (translation)
Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem tensV_apply' (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensV E a b f c = E a b (f c) + (if c = a then f b else 0) := by
  simp only [tensV, LinearMap.pi_apply, LinearMap.add_apply, LinearMap.comp_apply]
  split_ifs <;> simp [prj]

/- English proof (translation)
Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem tensVd_apply' (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensVd E a b f c = E a b (f c) - (if c = b then f a else 0) := by
  simp only [tensVd, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply]
  split_ifs <;> simp [prj]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem eeV_apply' (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (d : Fin n) :
    eeV E f d = ∑ c, E c d (f c) := by
  simp [eeV, prj, LinearMap.sum_apply]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem eeVd_apply' (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (d : Fin n) :
    eeVd E f d = -∑ c, E d c (f c) := by
  simp [eeVd, prj, LinearMap.sum_apply]

def twT (ε : Fin n → Bool) : (Fin n → M) →ₗ[ℂ] (Fin n → M) :=
  LinearMap.pi fun c => sg ε (Fin.rev c) • prj (Fin.rev c)

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem twT_apply (ε : Fin n → Bool) (f : Fin n → M) (c : Fin n) :
    twT ε f c = sg ε (Fin.rev c) • f (Fin.rev c) := by
  simp [twT, prj]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem twT_eq_zero {ε : Fin n → Bool} {f : Fin n → M} (h : twT ε f = 0) : f = 0 := by
  funext c
  have := congrFun h (Fin.rev c)
  rw [twT_apply, Fin.rev_rev] at this
  exact (smul_eq_zero.1 this).resolve_left (sg_ne ε c)

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.
-/
theorem twT_tens (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) :
    tensV (twE ε E) a b (twT ε f) = twT ε (twE ε (tensVd E) a b f) := by
  funext c
  rw [tensV_apply', twT_apply, twT_apply, twE_apply, twE_apply, map_smul (twT ε), Pi.smul_apply,
    twT_apply, tensVd_apply', map_smul]
  simp only [Fin.rev_inj]
  by_cases hc : c = a
  · subst hc
    simp only [if_true]
    unfold sg; split_ifs <;> module
  · simp [hc]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Take a linear combination of the given relations to obtain the conclusion.
-/
theorem twT_ee (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) :
    eeV (twE ε E) (twT ε f) = twT ε (eeVd E f) := by
  funext d
  rw [eeV_apply', twT_apply, eeVd_apply', smul_neg, Finset.smul_sum,
    ← sum_rev (fun c => sg ε (Fin.rev d) • E (Fin.rev d) c (f c)), ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [twT_apply, twE_apply, map_smul, smul_smul, ← neg_smul]
  congr 1
  linear_combination (-sg ε (Fin.rev d)) * sg_sq ε (Fin.rev c)

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem mem_Xs {A : Module.End ℂ (Fin n → M)} {S : Submodule ℂ M} {θ : ℝ} {f : Fin n → M} :
    f ∈ Xs A S θ ↔ (∀ c, f c ∈ S) ∧ A f = ((θ : ℝ) : ℂ) • f := by
  simp [Xs, Submodule.mem_inf, Submodule.mem_pi, LinearMap.mem_ker, sub_eq_zero]

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem xs_tw {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} {S : Submodule ℂ M} {θ : ℝ}
    {f : Fin n → M} (h : f ∈ Xs (eeVd E) S θ) : twT ε f ∈ Xs (eeV (twE ε E)) S θ := by
  rw [mem_Xs] at h ⊢
  refine ⟨fun c => ?_, ?_⟩
  · rw [twT_apply]; exact S.smul_mem _ (h.1 _)
  · rw [twT_ee, h.2, map_smul]

/- English proof (translation)
Establish an intermediate fact. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities.
-/
theorem khwT_tw {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} {μ : Fin n → ℝ}
    {f : Fin n → M} (h : IsKHWVec ε (tensVd E) μ f) :
    IsKHWVec (ε ∘ Fin.rev) (tensV (twE ε E)) (fun a => -μ (Fin.rev a)) (twT ε f) := by
  have h' := khw_tw h
  exact ⟨fun a => by rw [twT_tens, h'.1, map_smul], fun a b hab he => by
    rw [twT_tens, h'.2 a b hab he, map_zero]⟩

end Tens

section Wt

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Supply the required witnesses or components.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rhoN_tw (ε : Fin n → Bool) (a : Fin n) : rhoN (ε ∘ Fin.rev) a = -rhoN ε (Fin.rev a) := by
  unfold rhoN
  simp only [Function.comp_apply]
  have h1 : (univ.filter fun b => a < b ∧ ε (Fin.rev b) ≠ ε (Fin.rev a)).card =
      (univ.filter fun b => b < Fin.rev a ∧ ε b ≠ ε (Fin.rev a)).card := by
    refine Finset.card_nbij' Fin.rev Fin.rev ?_ ?_ ?_ ?_
    · intro b hb; simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢
      exact ⟨Fin.rev_lt_rev.2 hb.1, hb.2⟩
    · intro b hb; simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢
      refine ⟨?_, by simpa using hb.2⟩
      simpa using Fin.rev_lt_rev.2 hb.1
    · intro b _; simp
    · intro b _; simp
  have h2 : (univ.filter fun b => b < a ∧ ε (Fin.rev b) ≠ ε (Fin.rev a)).card =
      (univ.filter fun b => Fin.rev a < b ∧ ε b ≠ ε (Fin.rev a)).card := by
    refine Finset.card_nbij' Fin.rev Fin.rev ?_ ?_ ?_ ?_
    · intro b hb; simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢
      exact ⟨Fin.rev_lt_rev.2 hb.1, hb.2⟩
    · intro b hb; simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢
      refine ⟨?_, by simpa using hb.2⟩
      simpa using Fin.rev_lt_rev.2 hb.1
    · intro b _; simp
    · intro b _; simp
  rw [h1, h2]; ring

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Supply the required witnesses or components.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rhoC_tw (ε : Fin n → Bool) (a : Fin n) : rhoC (ε ∘ Fin.rev) a = -rhoC ε (Fin.rev a) := by
  unfold rhoC
  simp only [Function.comp_apply]
  have h1 : (univ.filter fun b => a < b ∧ ε (Fin.rev b) = ε (Fin.rev a)).card =
      (univ.filter fun b => b < Fin.rev a ∧ ε b = ε (Fin.rev a)).card := by
    refine Finset.card_nbij' Fin.rev Fin.rev ?_ ?_ ?_ ?_
    · intro b hb; simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢
      exact ⟨Fin.rev_lt_rev.2 hb.1, hb.2⟩
    · intro b hb; simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢
      refine ⟨?_, by simpa using hb.2⟩
      simpa using Fin.rev_lt_rev.2 hb.1
    · intro b _; simp
    · intro b _; simp
  have h2 : (univ.filter fun b => b < a ∧ ε (Fin.rev b) = ε (Fin.rev a)).card =
      (univ.filter fun b => Fin.rev a < b ∧ ε b = ε (Fin.rev a)).card := by
    refine Finset.card_nbij' Fin.rev Fin.rev ?_ ?_ ?_ ?_
    · intro b hb; simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢
      exact ⟨Fin.rev_lt_rev.2 hb.1, hb.2⟩
    · intro b hb; simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢
      refine ⟨?_, by simpa using hb.2⟩
      simpa using Fin.rev_lt_rev.2 hb.1
    · intro b _; simp
    · intro b _; simp
  rw [h1, h2]; ring

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lowK_tw (ε : Fin n → Bool) (ν : Fin n → ℝ) :
    lowK (ε ∘ Fin.rev) (fun a => -ν (Fin.rev a)) = fun a => -lowK ε ν (Fin.rev a) := by
  funext a
  simp only [lowK, Pi.add_apply, Pi.sub_apply, rhoN_tw, rhoC_tw]
  ring

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities.
-/
theorem casVal_tw (lam : Fin n → ℝ) : casVal (fun a => -lam (Fin.rev a)) = casVal lam := by
  unfold casVal nsq dot
  simp only [neg_mul_neg]
  rw [sum_rev (fun a => lam a * lam a)]

/- English proof (translation)
Replace the relevant objects with their definitions. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem pOf_tw (ε : Fin n → Bool) : pOf (ε ∘ Fin.rev) = pOf ε := by
  unfold pOf
  refine Finset.card_nbij' Fin.rev Fin.rev ?_ ?_ ?_ ?_ <;> intro b hb <;> simp_all

/- English proof (translation)
Replace the relevant objects with their definitions. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem qOf_tw (ε : Fin n → Bool) : qOf (ε ∘ Fin.rev) = qOf ε := by
  unfold qOf
  refine Finset.card_nbij' Fin.rev Fin.rev ?_ ?_ ?_ ?_ <;> intro b hb <;> simp_all

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Use the resulting assumption. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem gapLap_tw {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ} (hg : GapLap ε lam h) :
    GapLap (ε ∘ Fin.rev) (fun a => -lam (Fin.rev a)) h := by
  obtain ⟨h1, h2, h3⟩ := hg
  refine ⟨fun a b hab => ?_, fun a b hab => ?_, ?_⟩
  · have := h1 (Fin.rev_lt_rev.2 hab)
    simp only; linarith
  · have := h2 (Fin.rev a) (Fin.rev b) hab
    rw [abs_sub_comm] at this
    simp only; rwa [neg_sub_neg]
  · have e : hNeed (ε ∘ Fin.rev) = hNeed ε := by unfold hNeed; rw [pOf_tw, qOf_tw]
    rw [e]; exact h3

/- English proof (translation)
Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem root_rev (a b x : Fin n) : root (Fin.rev b) (Fin.rev a) x = -root a b (Fin.rev x) := by
  have e : ∀ i j : Fin n, (j = Fin.rev i ↔ Fin.rev j = i) := fun i j => by
    constructor <;> rintro rfl <;> simp
  simp only [root, Pi.sub_apply, Pi.single_apply, e]
  ring

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem cone_ev (k : Fin n → Fin n → ℕ) (y : Fin n) :
    (∑ a, ∑ b, if a < b then (k a b : ℝ) • root a b else 0) y =
      ∑ a, ∑ b, if a < b then (k a b : ℝ) * root a b y else 0 := by
  simp only [Finset.sum_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> simp

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem cone_rev {β : Fin n → ℝ} (h : InRootCone (fun a => -β (Fin.rev a))) : InRootCone β := by
  obtain ⟨m, hm⟩ := h
  refine ⟨fun a b => m (Fin.rev b) (Fin.rev a), ?_⟩
  funext x
  have hx := congrFun hm (Fin.rev x)
  simp only [Fin.rev_rev] at hx
  rw [cone_ev] at hx
  rw [cone_ev, show β x = -(-β x) by ring, hx, ← sum_rev, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← sum_rev, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Fin.rev_rev, Fin.rev_lt_rev, root_rev]
  split_ifs <;> ring

end Wt

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TwistedDualLemmas
