import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IndOfNot

open Finset

noncomputable section

namespace CompanionTheory.D.LK

open GlobalTheory.CompanionTheory.DSNormLt (sig sig_anti sig_mul pair_eq term_le normSq_le pair_lt abs_sig rho_eq)
open PI.UpqRep

variable {n : ℕ}

def ind (A : Finset (Pos n)) (a b : Fin n) : ℝ := ∑ i ∈ A, if i.1 = (a, b) then 1 else 0

/- English proof (translation)
Unfold `ind`. Use `split_ifs with h h1`. Rewrite using `[Finset.sum_eq_single_of_mem _ h1 fun i _ hi => if_neg fun e => hi (Subtype.ext e), if_pos rfl]`. Conclude with `Finset.sum_eq_zero fun i hi => if_neg fun e => h1 ((Subtype.ext e : i = ⟨(a, b), h⟩) ▸ hi)`. Conclude with `Finset.sum_eq_zero fun i _ => if_neg fun e => h (by have := i.2; rwa [e] at this)`.
-/
theorem ind_eq (A : Finset (Pos n)) (a b : Fin n) :
    ind A a b = if h : a < b then (if (⟨(a, b), h⟩ : Pos n) ∈ A then 1 else 0) else 0 := by
  unfold ind
  split_ifs with h h1
  · rw [Finset.sum_eq_single_of_mem _ h1 fun i _ hi => if_neg fun e => hi (Subtype.ext e), if_pos rfl]
  · exact Finset.sum_eq_zero fun i hi => if_neg fun e => h1 ((Subtype.ext e : i = ⟨(a, b), h⟩) ▸ hi)
  · exact Finset.sum_eq_zero fun i _ => if_neg fun e => h (by have := i.2; rwa [e] at this)

/- English proof (translation)
Rewrite using `[Finset.sum_sub_distrib]`. Unfold `wt ind`. Rewrite using `[Finset.sum_comm, Finset.sum_comm (s := univ), card_filter, card_filter, Nat.cast_sum, Nat.cast_sum]`. Apply the tactic sequence `congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_`. Apply the tactic sequence `simp only [Prod.ext_iff, ite_and] split_ifs <;> simp`.

Apply the tactic sequence `simp only [Prod.ext_iff, ite_and, Finset.sum_ite_eq, mem_univ, if_true] split_ifs <;> simp`.
-/
theorem wt_eq (A : Finset (Pos n)) (c : Fin n) : wt A c = ∑ b, (ind A c b - ind A b c) := by
  rw [Finset.sum_sub_distrib]
  unfold wt ind
  rw [Finset.sum_comm, Finset.sum_comm (s := univ), card_filter, card_filter, Nat.cast_sum, Nat.cast_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_
  · simp only [Prod.ext_iff, ite_and]
    split_ifs <;> simp
  · simp only [Prod.ext_iff, ite_and, Finset.sum_ite_eq, mem_univ, if_true]
    split_ifs <;> simp

def sc (ε : Fin n → Bool) (a b : Fin n) : ℝ := if ε a = ε b then sig a b else 0

/- English proof (translation)
Unfold `sc`. Distinguish the cases in `h : ε a = ε b`. Rewrite using `[if_pos h, if_pos h.symm, sig_anti]`. Rewrite using `[if_neg h, if_neg (Ne.symm h), neg_zero]`.
-/
theorem sc_anti (ε : Fin n → Bool) (a b : Fin n) : sc ε b a = -sc ε a b := by
  unfold sc
  by_cases h : ε a = ε b
  · rw [if_pos h, if_pos h.symm, sig_anti]
  · rw [if_neg h, if_neg (Ne.symm h), neg_zero]

/- English proof (translation)
Unfold `rhoC`. Use `congr 1`. Simplify using `only [Finset.card_filter, Nat.cast_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Unfold `sc sig`.

Break down `lt_trichotomy a b with h | h | h` into its components or cases. Apply the tactic sequence `by_cases h2 : ε b = ε a <;> simp [h, h.not_gt, h2, eq_comm (a := ε a)]`. Simplify using `[h]`. Apply the tactic sequence `by_cases h2 : ε b = ε a <;> simp [h, h.not_gt, h2, eq_comm (a := ε a)]`.
-/
theorem rhoC_eq (ε : Fin n → Bool) (a : Fin n) : rhoC ε a = (∑ b, sc ε a b) / 2 := by
  unfold rhoC
  congr 1
  simp only [Finset.card_filter, Nat.cast_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  unfold sc sig
  rcases lt_trichotomy a b with h | h | h
  · by_cases h2 : ε b = ε a <;> simp [h, h.not_gt, h2, eq_comm (a := ε a)]
  · simp [h]
  · by_cases h2 : ε b = ε a <;> simp [h, h.not_gt, h2, eq_comm (a := ε a)]

/- English proof (translation)
Take `⟨w, hw, hmin⟩` from `Finset.exists_min_image (univ.filter fun w : Equiv.Perm (Fin n) => ∀ c, ε (w c) = ε c) (fun w => ∑ c, κ (w c) * ((c : ℕ) : ℝ)) ⟨1, by simp⟩`. Establish `hw'` using `(mem_filter.1 hw).2`. Use `⟨w, hw', fun a b hab h => ?_⟩` and prove the remaining obligations. Use `hmin (w * Equiv.swap a b) (mem_filter.2 ⟨mem_univ _, fun c => by` as an intermediate fact. Rewrite using `[Equiv.Perm.mul_apply, hw', Equiv.swap_apply_def]`.

Use `split_ifs with h1 h2`. Rewrite using `[h1, h]`. Rewrite using `[h2, h]`. Use the proof step `rfl⟩)`. Establish `e : ∑ c, κ ((w * Equiv.swap a b) c) * ((c : ℕ) : ℝ) - ∑ c, κ (w c) * ((c : ℕ) : ℝ) = (κ (w a) - κ (w b)) * (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))`.

Rewrite using `[← Finset.sum_sub_distrib, Finset.sum_eq_add_of_mem a b (mem_univ _) (mem_univ _) hab.ne]`. Simplify using `only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]`. Expand and normalize the polynomial expressions, which then agree. Introduce `c _ hc`. Rewrite using `[Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hc.1 hc.2, sub_self]`.

Establish `hp : (0 : ℝ) < ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)` using `sub_pos.2 (by exact_mod_cast hab)`. Establish `: 0 ≤ (κ (w a) - κ (w b)) * (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))` using `by rw [← e]; linarith`. Combine the linear relations using `[nonneg_of_mul_nonneg_left this hp]`.
-/
theorem exists_sort (ε : Fin n → Bool) (κ : Fin n → ℝ) : ∃ w : Equiv.Perm (Fin n), (∀ c, ε (w c) = ε c) ∧
    ∀ a b, a < b → ε a = ε b → κ (w b) ≤ κ (w a) := by
  obtain ⟨w, hw, hmin⟩ := Finset.exists_min_image (univ.filter fun w : Equiv.Perm (Fin n) => ∀ c, ε (w c) = ε c)
    (fun w => ∑ c, κ (w c) * ((c : ℕ) : ℝ)) ⟨1, by simp⟩
  have hw' := (mem_filter.1 hw).2
  refine ⟨w, hw', fun a b hab h => ?_⟩
  have := hmin (w * Equiv.swap a b) (mem_filter.2 ⟨mem_univ _, fun c => by
    rw [Equiv.Perm.mul_apply, hw', Equiv.swap_apply_def]
    split_ifs with h1 h2
    · rw [h1, h]
    · rw [h2, h]
    · rfl⟩)
  have e : ∑ c, κ ((w * Equiv.swap a b) c) * ((c : ℕ) : ℝ) - ∑ c, κ (w c) * ((c : ℕ) : ℝ) =
      (κ (w a) - κ (w b)) * (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_add_of_mem a b (mem_univ _) (mem_univ _) hab.ne]
    · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]; ring
    · intro c _ hc
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hc.1 hc.2, sub_self]
  have hp : (0 : ℝ) < ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ) := sub_pos.2 (by exact_mod_cast hab)
  have : 0 ≤ (κ (w a) - κ (w b)) * (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by rw [← e]; linarith
  linarith [nonneg_of_mul_nonneg_left this hp]

/- English proof (translation)
Introduce `n ε lam ν B C hl hB hBn hC _ hdom hn`. Use `set κ := lowK ε lam + rhoC ε - wt B with hκ`. Use `set μ := lowK ε lam + (2 : ℝ) • rhoC ε - wt B - wt C with hμ`. Take `⟨w, hw, hs⟩` from `exists_sort ε κ`. Take `⟨m, hm, hm2⟩` from `hdom w hw`.

Establish `i1 : ∑ a, κ (w a) * μ (w a) ≤ ∑ a, κ (w a) * ν a`. Rewrite using `[← sub_nonneg, ← Finset.sum_sub_distrib]`. Establish `e : ∀ a, κ (w a) * ν a - κ (w a) * μ (w a) = ∑ c, ∑ d, (m c d : ℝ) * (κ (w a) * root c d a)` using `fun a => by`. Use `congrFun hm2 a` as an intermediate fact. Simplify using `only [Pi.sub_apply, Function.comp, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this`.

Rewrite using `[← mul_sub, this, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun d _ => by ring`. Simplify using `only [e]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_nonneg fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_nonneg fun d _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum]`.

Distinguish the cases in `h0 : m c d = 0`. Simplify using `[h0]`. Use `mul_nonneg (Nat.cast_nonneg _) ?_` and prove the remaining obligations. Simplify using `only [root, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', mem_univ, if_true, sub_nonneg]`. Conclude with `hs c d (hm c d h0).1 (hm c d h0).2`.

Set `tC : Fin n → Fin n → ℝ` to `fun a b => 2 * (ind C a b - ind C b a) - sc ε a b`. Establish `htC : ∀ a b, |tC a b| ≤ if ε a = ε b then 1 else 0` using `fun a b => by`. Simplify using `only [tC, ind_eq, sc, sig]`. Break down `lt_trichotomy a b with h | h | h` into its components or cases. Simplify using `only [dif_pos h, dif_neg h.not_gt, if_pos h]`.

Distinguish the cases in `h1 : (⟨(a, b), h⟩ : Pos n) ∈ C`. Establish `: ε a = ε b` using `hC _ h1`. Simplify using `[h1, this]`. Evaluate the numerical expressions. Apply the tactic sequence `simp only [h1, if_false]; split_ifs <;> simp`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `only [dif_pos h, dif_neg h.not_gt, if_pos h, if_neg h.not_gt]`. Distinguish the cases in `h1 : (⟨(b, a), h⟩ : Pos n) ∈ C`. Establish `: ε a = ε b` using `(hC _ h1).symm`.

Simplify using `[h1, this]`. Evaluate the numerical expressions. Apply the tactic sequence `simp only [h1, if_false]; split_ifs <;> simp`. Establish `i2 : ∑ a, κ a * (wt C a - rhoC ε a) ≤ ∑ a, κ (w a) * rhoC ε a`. Establish `p1` using `pair_eq tC (fun a b => by simp only [tC]; rw [sc_anti ε a b]; ring) κ`.

Establish `p2` using `pair_eq (sc ε) (sc_anti ε) fun a => κ (w a)`. Establish `e : ∀ a, wt C a - rhoC ε a = (∑ b, tC a b) / 2` using `fun a => by`. Simplify using `only [tC]`. Rewrite using `[wt_eq, rhoC_eq, Finset.sum_sub_distrib (f := fun b => 2 * (ind C a b - ind C b a)), ← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [e]`. Simplify using `only [rhoC_eq]`. Establish `: ∑ a, ∑ b, tC a b * (κ a - κ b) ≤ ∑ a, ∑ b, sc ε a b * (κ (w a) - κ (w b))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[abs_mul]`.

Conclude with `mul_le_mul_of_nonneg_right (htC a b) (abs_nonneg _))`. Use `_ = ∑ a, ∑ b, (if ε (w a) = ε (w b) then 1 else 0) * |κ (w a) - κ (w b)| := by`. Rewrite using `[← Equiv.sum_comp w]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← Equiv.sum_comp w]`.

Use `_ = _ := by`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[hw, hw, sc, sig]`. Distinguish the cases in `h : ε a = ε b`. Break down `lt_trichotomy a b with h1 | h1 | h1` into its components or cases.

Simplify using `[h, h1, abs_of_nonneg (sub_nonneg.2 (hs a b h1 h))]`. Simplify using `[h1]`. Simplify using `[h, h1, h1.not_gt, abs_of_nonpos (sub_nonpos.2 (hs b a h1 h.symm))]`. Simplify using `[h]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hκw : ∀ a, κ (w a) = ν a + rhoC ε a`. Establish `e1 : ∑ a, κ a * κ a = ∑ a, κ (w a) * μ (w a) + ∑ a, κ a * (wt C a - rhoC ε a)`. Rewrite using `[Equiv.sum_comp w fun a => κ a * μ a, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `only [hκ, hμ, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e2 : ∑ a, κ (w a) * κ (w a) = ∑ a, κ a * κ a` using `Equiv.sum_comp w fun a => κ a * κ a`. Establish `e3 : ∑ a, (κ (w a) - (ν a + rhoC ε a)) ^ 2 = ∑ a, κ (w a) * κ (w a) - 2 * ∑ a, κ (w a) * ν a - 2 * ∑ a, κ (w a) * rhoC ε a + ∑ a, (ν a + rhoC ε a) * (ν a + rhoC ε a)`. Simplify using `only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun a _ => by ring`.

Establish `hn' : ∑ a, (ν a + rhoC ε a) * (ν a + rhoC ε a) = ∑ a, κ a * κ a` using `hn`. Establish `h0 : ∑ a, (κ (w a) - (ν a + rhoC ε a)) ^ 2 = 0` using `le_antisymm (by linarith) (Finset.sum_nonneg fun _ _ => sq_nonneg _)`. Introduce `a`. Use `(Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).1 h0 a (mem_univ _)` as an intermediate fact. Conclude with `sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)`.

Set `t : Fin n → Fin n → ℝ` to `fun a b => (sig a b - sc ε a b) - 2 * (ind B a b - ind B b a) + sc ε (w.symm a) (w.symm b)`. Establish `hws : ∀ c, ε (w.symm c) = ε c` using `fun c => by rw [← hw, Equiv.apply_symm_apply]`. Establish `ta : ∀ a b, t b a = -t a b` using `fun a b => by`. Simplify using `only [t]`. Rewrite using `[sig_anti a b, sc_anti ε a b, sc_anti ε (w.symm a)]`.

Expand and normalize the polynomial expressions, which then agree. Establish `tb : ∀ a b, a < b → |t a b| ≤ 1` using `fun a b h => by`. Simplify using `only [t, ind_eq, dif_pos h, dif_neg h.not_gt, sc, hws]`. Distinguish the cases in `h1 : ε a = ε b`. Rewrite using `[if_neg fun h2 => hBn _ h2 h1]`.

Simplify `abs_sig _ _` using `[h1]`. Apply the tactic sequence `simp only [if_neg h1, sig, if_pos h] split_ifs <;> norm_num`. Establish `tb' : ∀ a b, |t a b| ≤ 1` using `fun a b => by`. Break down `lt_trichotomy a b with h | h | h` into its components or cases. Conclude with `tb a b h`.

Substitute `h` using the available equality. Use `ta a a` as an intermediate fact. Rewrite using `[show t a a = 0 by linarith]; simp`. Rewrite using `[ta, abs_neg]`. Conclude with `tb b a h`.

Take `⟨⟨⟨c, d⟩, hcd⟩, hi⟩` from `hB`. Establish `hne : t c d = -sig c d`. Establish `h1 : ¬ε c = ε d` using `hBn _ hi`. Establish `hcd' : c < d` using `hcd`. Simplify using `only [t, ind_eq, dif_pos hcd', dif_neg hcd'.not_gt, sc, hws, if_neg h1, if_pos hi, sig, if_pos hcd']`.

Evaluate the numerical expressions. Establish `j1` using `pair_lt t ta tb' hl c d (ne_of_lt hcd) hne`. Establish `j2` using `normSq_le t ta tb'`. Establish `f1 : ∀ a, (ν + (2 : ℝ) • rhoC ε) (w.symm a) = lam a + (∑ b, t a b) / 2` using `fun a => by`. Establish `h1` using `hκw (w.symm a)`.

Establish `h2` using `rho_eq ε a`. Establish `h3` using `rhoC_eq ε a`. Establish `h4` using `rhoC_eq ε (w.symm a)`. Rewrite `h4` using `[← Equiv.sum_comp w.symm]`. Establish `h5` using `wt_eq B a`.

Simplify using `only [hκ, lowK, Equiv.apply_symm_apply, Pi.add_apply, Pi.sub_apply] at h1`. Simplify using `only [t, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib]`. Rewrite using `[Finset.sum_sub_distrib (f := fun b => sig a b - sc ε a b), Finset.sum_sub_distrib (f := fun b => sig a b), ← Finset.mul_sum]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `f2 : ∀ a, (lowK ε lam + (2 : ℝ) • rhoC ε) a = lam a + (∑ b, sig a b) / 2` using `fun a => by`.

Use `rho_eq ε a` as an intermediate fact. Simplify using `only [lowK, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `ex : ∀ y : Fin n → ℝ, ∑ a, (lam a + y a) * (lam a + y a) = ∑ a, lam a ^ 2 + 2 * ∑ a, lam a * y a + ∑ a, y a ^ 2` using `fun y => by`. Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]`.

Conclude with `Finset.sum_congr rfl fun a _ => by ring`. Unfold `vNormSq nsq dot`. Rewrite using `[← Equiv.sum_comp w.symm]`. Simplify using `only [f1, f2]`. Rewrite using `[ex, ex]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem K_type_count : NumK := by
  intro n ε lam ν B C hl hB hBn hC _ hdom hn
  set κ := lowK ε lam + rhoC ε - wt B with hκ
  set μ := lowK ε lam + (2 : ℝ) • rhoC ε - wt B - wt C with hμ
  obtain ⟨w, hw, hs⟩ := exists_sort ε κ
  obtain ⟨m, hm, hm2⟩ := hdom w hw
  have i1 : ∑ a, κ (w a) * μ (w a) ≤ ∑ a, κ (w a) * ν a := by
    rw [← sub_nonneg, ← Finset.sum_sub_distrib]
    have e : ∀ a, κ (w a) * ν a - κ (w a) * μ (w a) = ∑ c, ∑ d, (m c d : ℝ) * (κ (w a) * root c d a) := fun a => by
      have := congrFun hm2 a
      simp only [Pi.sub_apply, Function.comp, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [← mul_sub, this, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun d _ => by ring
    simp only [e]
    rw [Finset.sum_comm]
    refine Finset.sum_nonneg fun c _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_nonneg fun d _ => ?_
    rw [← Finset.mul_sum]
    by_cases h0 : m c d = 0
    · simp [h0]
    · refine mul_nonneg (Nat.cast_nonneg _) ?_
      simp only [root, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', mem_univ, if_true, sub_nonneg]
      exact hs c d (hm c d h0).1 (hm c d h0).2
  let tC : Fin n → Fin n → ℝ := fun a b => 2 * (ind C a b - ind C b a) - sc ε a b
  have htC : ∀ a b, |tC a b| ≤ if ε a = ε b then 1 else 0 := fun a b => by
    simp only [tC, ind_eq, sc, sig]
    rcases lt_trichotomy a b with h | h | h
    · simp only [dif_pos h, dif_neg h.not_gt, if_pos h]
      by_cases h1 : (⟨(a, b), h⟩ : Pos n) ∈ C
      · have : ε a = ε b := hC _ h1
        simp [h1, this]; norm_num
      · simp only [h1, if_false]; split_ifs <;> simp
    · subst h; simp
    · simp only [dif_pos h, dif_neg h.not_gt, if_pos h, if_neg h.not_gt]
      by_cases h1 : (⟨(b, a), h⟩ : Pos n) ∈ C
      · have : ε a = ε b := (hC _ h1).symm
        simp [h1, this]; norm_num
      · simp only [h1, if_false]; split_ifs <;> simp
  have i2 : ∑ a, κ a * (wt C a - rhoC ε a) ≤ ∑ a, κ (w a) * rhoC ε a := by
    have p1 := pair_eq tC (fun a b => by simp only [tC]; rw [sc_anti ε a b]; ring) κ
    have p2 := pair_eq (sc ε) (sc_anti ε) fun a => κ (w a)
    have e : ∀ a, wt C a - rhoC ε a = (∑ b, tC a b) / 2 := fun a => by
      simp only [tC]
      rw [wt_eq, rhoC_eq, Finset.sum_sub_distrib (f := fun b => 2 * (ind C a b - ind C b a)), ← Finset.mul_sum]
      ring
    simp only [e]
    simp only [rhoC_eq]
    have : ∑ a, ∑ b, tC a b * (κ a - κ b) ≤ ∑ a, ∑ b, sc ε a b * (κ (w a) - κ (w b)) := by
      calc _ ≤ ∑ a, ∑ b, (if ε a = ε b then 1 else 0) * |κ a - κ b| :=
            Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => (le_abs_self _).trans (by
              rw [abs_mul]; exact mul_le_mul_of_nonneg_right (htC a b) (abs_nonneg _))
        _ = ∑ a, ∑ b, (if ε (w a) = ε (w b) then 1 else 0) * |κ (w a) - κ (w b)| := by
            rw [← Equiv.sum_comp w]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [← Equiv.sum_comp w]
        _ = _ := by
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
            rw [hw, hw, sc, sig]
            by_cases h : ε a = ε b
            · rcases lt_trichotomy a b with h1 | h1 | h1
              · simp [h, h1, abs_of_nonneg (sub_nonneg.2 (hs a b h1 h))]
              · simp [h1]
              · simp [h, h1, h1.not_gt, abs_of_nonpos (sub_nonpos.2 (hs b a h1 h.symm))]
            · simp [h]
    linarith
  have hκw : ∀ a, κ (w a) = ν a + rhoC ε a := by
    have e1 : ∑ a, κ a * κ a = ∑ a, κ (w a) * μ (w a) + ∑ a, κ a * (wt C a - rhoC ε a) := by
      rw [Equiv.sum_comp w fun a => κ a * μ a, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [hκ, hμ, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have e2 : ∑ a, κ (w a) * κ (w a) = ∑ a, κ a * κ a := Equiv.sum_comp w fun a => κ a * κ a
    have e3 : ∑ a, (κ (w a) - (ν a + rhoC ε a)) ^ 2 = ∑ a, κ (w a) * κ (w a) - 2 * ∑ a, κ (w a) * ν a -
        2 * ∑ a, κ (w a) * rhoC ε a + ∑ a, (ν a + rhoC ε a) * (ν a + rhoC ε a) := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    have hn' : ∑ a, (ν a + rhoC ε a) * (ν a + rhoC ε a) = ∑ a, κ a * κ a := hn
    have h0 : ∑ a, (κ (w a) - (ν a + rhoC ε a)) ^ 2 = 0 :=
      le_antisymm (by linarith) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    intro a
    have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).1 h0 a (mem_univ _)
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
  let t : Fin n → Fin n → ℝ := fun a b =>
    (sig a b - sc ε a b) - 2 * (ind B a b - ind B b a) + sc ε (w.symm a) (w.symm b)
  have hws : ∀ c, ε (w.symm c) = ε c := fun c => by rw [← hw, Equiv.apply_symm_apply]
  have ta : ∀ a b, t b a = -t a b := fun a b => by
    simp only [t]; rw [sig_anti a b, sc_anti ε a b, sc_anti ε (w.symm a)]; ring
  have tb : ∀ a b, a < b → |t a b| ≤ 1 := fun a b h => by
    simp only [t, ind_eq, dif_pos h, dif_neg h.not_gt, sc, hws]
    by_cases h1 : ε a = ε b
    · rw [if_neg fun h2 => hBn _ h2 h1]
      simpa [h1] using abs_sig _ _
    · simp only [if_neg h1, sig, if_pos h]
      split_ifs <;> norm_num
  have tb' : ∀ a b, |t a b| ≤ 1 := fun a b => by
    rcases lt_trichotomy a b with h | h | h
    · exact tb a b h
    · subst h
      have := ta a a
      rw [show t a a = 0 by linarith]; simp
    · rw [ta, abs_neg]; exact tb b a h
  obtain ⟨⟨⟨c, d⟩, hcd⟩, hi⟩ := hB
  have hne : t c d = -sig c d := by
    have h1 : ¬ε c = ε d := hBn _ hi
    have hcd' : c < d := hcd
    simp only [t, ind_eq, dif_pos hcd', dif_neg hcd'.not_gt, sc, hws, if_neg h1, if_pos hi, sig, if_pos hcd']
    norm_num
  have j1 := pair_lt t ta tb' hl c d (ne_of_lt hcd) hne
  have j2 := normSq_le t ta tb'
  have f1 : ∀ a, (ν + (2 : ℝ) • rhoC ε) (w.symm a) = lam a + (∑ b, t a b) / 2 := fun a => by
    have h1 := hκw (w.symm a)
    have h2 := rho_eq ε a
    have h3 := rhoC_eq ε a
    have h4 := rhoC_eq ε (w.symm a)
    rw [← Equiv.sum_comp w.symm] at h4
    have h5 := wt_eq B a
    simp only [hκ, lowK, Equiv.apply_symm_apply, Pi.add_apply, Pi.sub_apply] at h1
    simp only [t, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib]
    rw [Finset.sum_sub_distrib (f := fun b => sig a b - sc ε a b), Finset.sum_sub_distrib (f := fun b => sig a b),
      ← Finset.mul_sum]
    linarith
  have f2 : ∀ a, (lowK ε lam + (2 : ℝ) • rhoC ε) a = lam a + (∑ b, sig a b) / 2 := fun a => by
    have := rho_eq ε a
    simp only [lowK, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have ex : ∀ y : Fin n → ℝ, ∑ a, (lam a + y a) * (lam a + y a) =
      ∑ a, lam a ^ 2 + 2 * ∑ a, lam a * y a + ∑ a, y a ^ 2 := fun y => by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  unfold vNormSq nsq dot
  rw [← Equiv.sum_comp w.symm]
  simp only [f1, f2]
  rw [ex, ex]
  linarith

end CompanionTheory.D.LK
