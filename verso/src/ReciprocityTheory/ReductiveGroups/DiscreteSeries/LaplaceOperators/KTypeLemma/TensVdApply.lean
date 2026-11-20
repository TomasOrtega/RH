import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.CompRevRev

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TwistedDualLemmas

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.LemK

variable {n : ℕ}

section Tens

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/- English proof (translation)
Simplify using `only [tensV, LinearMap.pi_apply, LinearMap.add_apply, LinearMap.comp_apply]`. Apply the tactic sequence `split_ifs <;> simp [prj]`.
-/
theorem tensV_apply' (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensV E a b f c = E a b (f c) + (if c = a then f b else 0) := by
  simp only [tensV, LinearMap.pi_apply, LinearMap.add_apply, LinearMap.comp_apply]
  split_ifs <;> simp [prj]

/- English proof (translation)
Simplify using `only [tensVd, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply]`. Apply the tactic sequence `split_ifs <;> simp [prj]`.
-/
theorem tensVd_apply' (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensVd E a b f c = E a b (f c) - (if c = b then f a else 0) := by
  simp only [tensVd, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply]
  split_ifs <;> simp [prj]

/- English proof (translation)
Simplify using `[eeV, prj, LinearMap.sum_apply]`.
-/
theorem eeV_apply' (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (d : Fin n) :
    eeV E f d = ∑ c, E c d (f c) := by
  simp [eeV, prj, LinearMap.sum_apply]

/- English proof (translation)
Simplify using `[eeVd, prj, LinearMap.sum_apply]`.
-/
theorem eeVd_apply' (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (d : Fin n) :
    eeVd E f d = -∑ c, E d c (f c) := by
  simp [eeVd, prj, LinearMap.sum_apply]

def twT (ε : Fin n → Bool) : (Fin n → M) →ₗ[ℂ] (Fin n → M) :=
  LinearMap.pi fun c => sg ε (Fin.rev c) • prj (Fin.rev c)

/- English proof (translation)
Simplify using `[twT, prj]`.
-/
theorem twT_apply (ε : Fin n → Bool) (f : Fin n → M) (c : Fin n) :
    twT ε f c = sg ε (Fin.rev c) • f (Fin.rev c) := by
  simp [twT, prj]

/- English proof (translation)
Use function extensionality and compare the values at `c`. Use `congrFun h (Fin.rev c)` as an intermediate fact. Rewrite `this` using `[twT_apply, Fin.rev_rev]`. Conclude with `(smul_eq_zero.1 this).resolve_left (sg_ne ε c)`.
-/
theorem twT_eq_zero {ε : Fin n → Bool} {f : Fin n → M} (h : twT ε f = 0) : f = 0 := by
  funext c
  have := congrFun h (Fin.rev c)
  rw [twT_apply, Fin.rev_rev] at this
  exact (smul_eq_zero.1 this).resolve_left (sg_ne ε c)

/- English proof (translation)
Use function extensionality and compare the values at `c`. Rewrite using `[tensV_apply', twT_apply, twT_apply, twE_apply, twE_apply, map_smul (twT ε), Pi.smul_apply, twT_apply, tensVd_apply', map_smul]`. Simplify using `only [Fin.rev_inj]`. Distinguish the cases in `hc : c = a`. Substitute `hc` using the available equality.

Simplify using `only [if_true]`. Apply the tactic sequence `unfold sg; split_ifs <;> module`. Simplify using `[hc]`.
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
Use function extensionality and compare the values at `d`. Rewrite using `[eeV_apply', twT_apply, eeVd_apply', smul_neg, Finset.smul_sum, ← sum_rev (fun c => sg ε (Fin.rev d) • E (Fin.rev d) c (f c)), ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[twT_apply, twE_apply, map_smul, smul_smul, ← neg_smul]`. Use `congr 1`.

Take the linear combination `(-sg ε (Fin.rev d)) * sg_sq ε (Fin.rev c)`.
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
Simplify using `[Xs, Submodule.mem_inf, Submodule.mem_pi, LinearMap.mem_ker, sub_eq_zero]`.
-/
theorem mem_Xs {A : Module.End ℂ (Fin n → M)} {S : Submodule ℂ M} {θ : ℝ} {f : Fin n → M} :
    f ∈ Xs A S θ ↔ (∀ c, f c ∈ S) ∧ A f = ((θ : ℝ) : ℂ) • f := by
  simp [Xs, Submodule.mem_inf, Submodule.mem_pi, LinearMap.mem_ker, sub_eq_zero]

/- English proof (translation)
Rewrite `h`, the goal using `[mem_Xs]`. Use `⟨fun c => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[twT_apply]`. Conclude with `S.smul_mem _ (h.1 _)`. Rewrite using `[twT_ee, h.2, map_smul]`.
-/
theorem xs_tw {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} {S : Submodule ℂ M} {θ : ℝ}
    {f : Fin n → M} (h : f ∈ Xs (eeVd E) S θ) : twT ε f ∈ Xs (eeV (twE ε E)) S θ := by
  rw [mem_Xs] at h ⊢
  refine ⟨fun c => ?_, ?_⟩
  · rw [twT_apply]; exact S.smul_mem _ (h.1 _)
  · rw [twT_ee, h.2, map_smul]

/- English proof (translation)
Establish `h'` using `khw_tw h`. Conclude with `⟨fun a => by rw [twT_tens, h'.1, map_smul], fun a b hab he => by`. Rewrite using `[twT_tens, h'.2 a b hab he, map_zero]⟩`.
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
Unfold `rhoN`. Simplify using `only [Function.comp_apply]`. Establish `h1 : (univ.filter fun b => a < b ∧ ε (Fin.rev b) ≠ ε (Fin.rev a)).card = (univ.filter fun b => b < Fin.rev a ∧ ε b ≠ ε (Fin.rev a)).card`. Use `Finset.card_nbij' Fin.rev Fin.rev ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `b hb`.

Simplify using `only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢`. Conclude with `⟨Fin.rev_lt_rev.2 hb.1, hb.2⟩`. Introduce `b hb`. Simplify using `only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢`. Use `⟨?_, by simpa using hb.2⟩` and prove the remaining obligations.

Simplify using `using Fin.rev_lt_rev.2 hb.1`. Introduce `b _`. Simplify using the standard rewrite rules. Introduce `b _`. Simplify using the standard rewrite rules.

Establish `h2 : (univ.filter fun b => b < a ∧ ε (Fin.rev b) ≠ ε (Fin.rev a)).card = (univ.filter fun b => Fin.rev a < b ∧ ε b ≠ ε (Fin.rev a)).card`. Use `Finset.card_nbij' Fin.rev Fin.rev ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `b hb`. Simplify using `only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢`. Conclude with `⟨Fin.rev_lt_rev.2 hb.1, hb.2⟩`.

Introduce `b hb`. Simplify using `only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢`. Use `⟨?_, by simpa using hb.2⟩` and prove the remaining obligations. Simplify using `using Fin.rev_lt_rev.2 hb.1`. Introduce `b _`.

Simplify using the standard rewrite rules. Introduce `b _`. Simplify using the standard rewrite rules. Rewrite using `[h1, h2]`. Expand and normalize the polynomial expressions, which then agree.
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
Unfold `rhoC`. Simplify using `only [Function.comp_apply]`. Establish `h1 : (univ.filter fun b => a < b ∧ ε (Fin.rev b) = ε (Fin.rev a)).card = (univ.filter fun b => b < Fin.rev a ∧ ε b = ε (Fin.rev a)).card`. Use `Finset.card_nbij' Fin.rev Fin.rev ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `b hb`.

Simplify using `only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢`. Conclude with `⟨Fin.rev_lt_rev.2 hb.1, hb.2⟩`. Introduce `b hb`. Simplify using `only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢`. Use `⟨?_, by simpa using hb.2⟩` and prove the remaining obligations.

Simplify using `using Fin.rev_lt_rev.2 hb.1`. Introduce `b _`. Simplify using the standard rewrite rules. Introduce `b _`. Simplify using the standard rewrite rules.

Establish `h2 : (univ.filter fun b => b < a ∧ ε (Fin.rev b) = ε (Fin.rev a)).card = (univ.filter fun b => Fin.rev a < b ∧ ε b = ε (Fin.rev a)).card`. Use `Finset.card_nbij' Fin.rev Fin.rev ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `b hb`. Simplify using `only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢`. Conclude with `⟨Fin.rev_lt_rev.2 hb.1, hb.2⟩`.

Introduce `b hb`. Simplify using `only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢`. Use `⟨?_, by simpa using hb.2⟩` and prove the remaining obligations. Simplify using `using Fin.rev_lt_rev.2 hb.1`. Introduce `b _`.

Simplify using the standard rewrite rules. Introduce `b _`. Simplify using the standard rewrite rules. Rewrite using `[h1, h2]`. Expand and normalize the polynomial expressions, which then agree.
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
Use function extensionality and compare the values at `a`. Simplify using `only [lowK, Pi.add_apply, Pi.sub_apply, rhoN_tw, rhoC_tw]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lowK_tw (ε : Fin n → Bool) (ν : Fin n → ℝ) :
    lowK (ε ∘ Fin.rev) (fun a => -ν (Fin.rev a)) = fun a => -lowK ε ν (Fin.rev a) := by
  funext a
  simp only [lowK, Pi.add_apply, Pi.sub_apply, rhoN_tw, rhoC_tw]
  ring

/- English proof (translation)
Unfold `casVal nsq dot`. Simplify using `only [neg_mul_neg]`. Rewrite using `[sum_rev (fun a => lam a * lam a)]`.
-/
theorem casVal_tw (lam : Fin n → ℝ) : casVal (fun a => -lam (Fin.rev a)) = casVal lam := by
  unfold casVal nsq dot
  simp only [neg_mul_neg]
  rw [sum_rev (fun a => lam a * lam a)]

/- English proof (translation)
Unfold `pOf`. Apply the tactic sequence `refine Finset.card_nbij' Fin.rev Fin.rev ?_ ?_ ?_ ?_ <;> intro b hb <;> simp_all`.
-/
theorem pOf_tw (ε : Fin n → Bool) : pOf (ε ∘ Fin.rev) = pOf ε := by
  unfold pOf
  refine Finset.card_nbij' Fin.rev Fin.rev ?_ ?_ ?_ ?_ <;> intro b hb <;> simp_all

/- English proof (translation)
Unfold `qOf`. Apply the tactic sequence `refine Finset.card_nbij' Fin.rev Fin.rev ?_ ?_ ?_ ?_ <;> intro b hb <;> simp_all`.
-/
theorem qOf_tw (ε : Fin n → Bool) : qOf (ε ∘ Fin.rev) = qOf ε := by
  unfold qOf
  refine Finset.card_nbij' Fin.rev Fin.rev ?_ ?_ ?_ ?_ <;> intro b hb <;> simp_all

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `hg`. Use `⟨fun a b hab => ?_, fun a b hab => ?_, ?_⟩` and prove the remaining obligations. Use `h1 (Fin.rev_lt_rev.2 hab)` as an intermediate fact. Simplify using `only`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `h2 (Fin.rev a) (Fin.rev b) hab` as an intermediate fact. Rewrite `this` using `[abs_sub_comm]`. Simplify using `only`. Rewrite using `[neg_sub_neg]` and apply the resulting hypothesis. Establish `e : hNeed (ε ∘ Fin.rev) = hNeed ε` using `by unfold hNeed; rw [pOf_tw, qOf_tw]`.

Rewrite using `[e]`. Conclude with `h3`.
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
Establish `e : ∀ i j : Fin n, (j = Fin.rev i ↔ Fin.rev j = i)` using `fun i j => by`. Apply the tactic sequence `constructor <;> rintro rfl <;> simp`. Simplify using `only [root, Pi.sub_apply, Pi.single_apply, e]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem root_rev (a b x : Fin n) : root (Fin.rev b) (Fin.rev a) x = -root a b (Fin.rev x) := by
  have e : ∀ i j : Fin n, (j = Fin.rev i ↔ Fin.rev j = i) := fun i j => by
    constructor <;> rintro rfl <;> simp
  simp only [root, Pi.sub_apply, Pi.single_apply, e]
  ring

/- English proof (translation)
Simplify using `only [Finset.sum_apply]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem cone_ev (k : Fin n → Fin n → ℕ) (y : Fin n) :
    (∑ a, ∑ b, if a < b then (k a b : ℝ) • root a b else 0) y =
      ∑ a, ∑ b, if a < b then (k a b : ℝ) * root a b y else 0 := by
  simp only [Finset.sum_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> simp

/- English proof (translation)
Take `⟨m, hm⟩` from `h`. Use `⟨fun a b => m (Fin.rev b) (Fin.rev a), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Establish `hx` using `congrFun hm (Fin.rev x)`. Simplify using `only [Fin.rev_rev] at hx`.

Rewrite `hx` using `[cone_ev]`. Rewrite using `[cone_ev, show β x = -(-β x) by ring, hx, ← sum_rev, ← Finset.sum_neg_distrib]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[← sum_rev, ← Finset.sum_neg_distrib]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `only [Fin.rev_rev, Fin.rev_lt_rev, root_rev]`. Apply the tactic sequence `split_ifs <;> ring`.
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
