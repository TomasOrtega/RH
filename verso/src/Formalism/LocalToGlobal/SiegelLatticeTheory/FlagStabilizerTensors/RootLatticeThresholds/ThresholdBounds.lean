import Mathlib
import Formalism.HermitianCurvature.StatementSz

noncomputable section

open Finset

namespace Formalism.L2.SG.Pf.ThresholdBounds

open Formalism.FourierDecayAlt

variable (c : Sz.Cfg)

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem v_eq_vlast_add_four_mul_Del (i : ℕ) : c.v i = c.vlast + 4 * c.Del * ((c.k : ℝ) - 1 - (i : ℝ)) := rfl

/- English proof (translation)
Rewrite using `[v_eq_vlast_add_four_mul_Del c i, v_eq_vlast_add_four_mul_Del c j]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem v_sub (i j : ℕ) : c.v i - c.v j = 4 * c.Del * ((j : ℝ) - (i : ℝ)) := by
  rw [v_eq_vlast_add_four_mul_Del c i, v_eq_vlast_add_four_mul_Del c j]; ring

/- English proof (translation)
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => intro h`. Use linear arithmetic over natural numbers and integers. Consider the case `succ n ih`.

Introduce `hj hjm`. Break down `Nat.eq_zero_or_pos n with hn | hn` into its components or cases. Substitute `hn` using the available equality. Conclude with `le_refl _`. Establish `h1` using `ih (by omega) (by omega)`.

Establish `h2` using `hOk.hgap n (by omega) (by omega)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem b_one_le (hOk : c.Ok) : ∀ j : ℕ, 1 ≤ j → j ≤ c.m → c.b 1 ≤ c.b j := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ n ih =>
    intro hj hjm
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; exact le_refl _
    · have h1 := ih (by omega) (by omega)
      have h2 := hOk.hgap n (by omega) (by omega)
      linarith

/- English proof (translation)
Establish `hk4 : (4 : ℝ) ≤ c.k` using `by exact_mod_cast hOk.hk`. Establish `hm2 : (2 : ℝ) ≤ c.m` using `by exact_mod_cast hOk.hm`. Establish `hD` using `hOk.hDel`. Establish `hv0` using `hOk.hv0`. Establish `hlk : (l : ℝ) + 1 ≤ c.k` using `by exact_mod_cast hl`.

Establish `hvl : c.vlast ≤ c.v l`. Rewrite using `[v_eq_vlast_add_four_mul_Del c l]`. Use `mul_nonneg (by linarith : (0 : ℝ) ≤ 4 * c.Del) (by linarith : (0 : ℝ) ≤ (c.k : ℝ) - 1 - l)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hmk : (8 : ℝ) * c.Del ≤ (c.m : ℝ) * c.k * c.Del`.

Establish `h8 : (8 : ℝ) ≤ (c.m : ℝ) * c.k` using `by nlinarith`. Conclude with `mul_le_mul_of_nonneg_right h8 (by linarith)`. Establish `hkD : 4 * c.Del ≤ (c.k : ℝ) * c.Del` using `mul_le_mul_of_nonneg_right hk4 (by linarith)`. Establish `hw1 : ∀ i, de i = 0 ∨ de i = 1` using `(show (∀ i, de i = 0 ∨ de i = 1) ∧ de (c.k - 1) = 0 from hw).1`. Distinguish the cases in `h1 : i = 1`.

Substitute `h1` using the available equality. Establish `hu : c.u de 1 = c.a` using `by simp [Formalism.FourierDecayAlt.Sz.Cfg.u]`. Establish `ha` using `hOk.ha`. Establish `e` using `v_sub c 1 l`. Move the coercions through the operations in `at e`.

Establish `hl0 : 0 ≤ 4 * c.Del * (l : ℝ)` using `by positivity`. Rewrite using `[hu]`. Apply `ne_of_gt` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Distinguish the cases in `hk : i = c.k`.

Establish `hu : c.u de i = c.ulast` using `by rw [Formalism.FourierDecayAlt.Sz.Cfg.u, if_neg h1, if_pos hk]`. Rewrite using `[hu]`. Consider the cases of `ht : c.top`. Establish `hul : c.ulast = c.vlast - 1 / 2` using `by simp [Formalism.FourierDecayAlt.Sz.Cfg.ulast, ht]`. Rewrite using `[hul]`.

Break down `Nat.lt_or_ge (l + 1) c.k with hlt | hge` into its components or cases. Establish `h2' : l + 2 ≤ c.k` using `by omega`. Establish `h2 : (l : ℝ) + 2 ≤ c.k` using `by exact_mod_cast h2'`. Establish `hvl' : c.vlast + 4 * c.Del ≤ c.v l`. Rewrite using `[v_eq_vlast_add_four_mul_Del c l]`.

Use `mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ (c.k : ℝ) - 1 - l by linarith) (by linarith : (0 : ℝ) ≤ 4 * c.Del)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Apply `ne_of_lt` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Establish `heq : (l : ℝ) + 1 = c.k` using `by exact_mod_cast (le_antisymm hl hge)`.

Establish `hv' : c.v l = c.vlast` using `by rw [v_eq_vlast_add_four_mul_Del c l, ← heq]; ring`. Apply `ne_of_gt` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hul : c.ulast = -c.bp` using `by simp [Formalism.FourierDecayAlt.Sz.Cfg.ulast, ht]`. Rewrite using `[hul]`.

Establish `hbp` using `(hOk.htop ht).1`. Apply `ne_of_lt` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hu : c.u de i = c.v (i - 1) - 1 / 2 - de (i - 1) * c.Del` using `by rw [Formalism.FourierDecayAlt.Sz.Cfg.u, if_neg h1, if_neg hk]`. Rewrite using `[hu]`.

Take `⟨j, rfl⟩ : ∃ j, i = j + 1` from `⟨i - 1, by omega⟩`. Simplify using `only [Nat.add_sub_cancel]`. Establish `e` using `v_sub c j l`. Establish `hde` using `hw1 j`. Break down `lt_trichotomy j l with hjl | rfl | hlj` into its components or cases.

Establish `h' : (j : ℝ) + 1 ≤ l` using `by exact_mod_cast hjl`. Establish `: 4 * c.Del * 1 ≤ 4 * c.Del * ((l : ℝ) - j)` using `mul_le_mul_of_nonneg_left (by linarith) (by linarith)`. Apply the tactic sequence `rcases hde with h | h <;> rw [h] <;> apply ne_of_gt <;> linarith`. Apply the tactic sequence `rcases hde with h | h <;> rw [h]`. Apply `ne_of_gt` to reduce the goal to its premises.

Combine the linear equalities and inequalities to obtain the conclusion. Apply `ne_of_lt` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h' : (l : ℝ) + 1 ≤ j` using `by exact_mod_cast hlj`. Establish `: 4 * c.Del * ((l : ℝ) - j) ≤ 4 * c.Del * (-1)` using `mul_le_mul_of_nonneg_left (by linarith) (by linarith)`.

Apply the tactic sequence `rcases hde with h | h <;> rw [h] <;> apply ne_of_lt <;> linarith`.
-/
theorem qfac_ne (hOk : c.Ok) (hb1 : 40 * (c.m : ℝ) * c.k * c.Del ≤ c.b 1) {de : ℕ → ℝ} (hw : Sz.IsWord c.k de)
    {l : ℕ} (hl : l + 1 ≤ c.k) {Y : ℝ} (hY1 : 5 / 2 ≤ c.v l + Y) (hY2 : c.v l + Y ≤ c.Del / 2) {i : ℕ} (hi1 : 1 ≤ i)
    (hik : i ≤ c.k) : Y + 1 / 2 + c.u de i ≠ 0 := by
  have hk4 : (4 : ℝ) ≤ c.k := by exact_mod_cast hOk.hk
  have hm2 : (2 : ℝ) ≤ c.m := by exact_mod_cast hOk.hm
  have hD := hOk.hDel
  have hv0 := hOk.hv0
  have hlk : (l : ℝ) + 1 ≤ c.k := by exact_mod_cast hl
  have hvl : c.vlast ≤ c.v l := by
    rw [v_eq_vlast_add_four_mul_Del c l]
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 4 * c.Del) (by linarith : (0 : ℝ) ≤ (c.k : ℝ) - 1 - l)
    linarith
  have hmk : (8 : ℝ) * c.Del ≤ (c.m : ℝ) * c.k * c.Del := by
    have h8 : (8 : ℝ) ≤ (c.m : ℝ) * c.k := by nlinarith
    exact mul_le_mul_of_nonneg_right h8 (by linarith)
  have hkD : 4 * c.Del ≤ (c.k : ℝ) * c.Del := mul_le_mul_of_nonneg_right hk4 (by linarith)
  have hw1 : ∀ i, de i = 0 ∨ de i = 1 :=
    (show (∀ i, de i = 0 ∨ de i = 1) ∧ de (c.k - 1) = 0 from hw).1
  by_cases h1 : i = 1
  · subst h1
    have hu : c.u de 1 = c.a := by simp [Formalism.FourierDecayAlt.Sz.Cfg.u]
    have ha := hOk.ha
    have e := v_sub c 1 l
    push_cast at e
    have hl0 : 0 ≤ 4 * c.Del * (l : ℝ) := by positivity
    rw [hu]; apply ne_of_gt; linarith
  · by_cases hk : i = c.k
    · have hu : c.u de i = c.ulast := by rw [Formalism.FourierDecayAlt.Sz.Cfg.u, if_neg h1, if_pos hk]
      rw [hu]
      cases ht : c.top
      · have hul : c.ulast = c.vlast - 1 / 2 := by simp [Formalism.FourierDecayAlt.Sz.Cfg.ulast, ht]
        rw [hul]
        rcases Nat.lt_or_ge (l + 1) c.k with hlt | hge
        · have h2' : l + 2 ≤ c.k := by omega
          have h2 : (l : ℝ) + 2 ≤ c.k := by exact_mod_cast h2'
          have hvl' : c.vlast + 4 * c.Del ≤ c.v l := by
            rw [v_eq_vlast_add_four_mul_Del c l]
            have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ (c.k : ℝ) - 1 - l by linarith)
              (by linarith : (0 : ℝ) ≤ 4 * c.Del)
            linarith
          apply ne_of_lt; linarith
        · have heq : (l : ℝ) + 1 = c.k := by exact_mod_cast (le_antisymm hl hge)
          have hv' : c.v l = c.vlast := by rw [v_eq_vlast_add_four_mul_Del c l, ← heq]; ring
          apply ne_of_gt; linarith
      · have hul : c.ulast = -c.bp := by simp [Formalism.FourierDecayAlt.Sz.Cfg.ulast, ht]
        rw [hul]
        have hbp := (hOk.htop ht).1
        apply ne_of_lt; linarith
    · have hu : c.u de i = c.v (i - 1) - 1 / 2 - de (i - 1) * c.Del := by rw [Formalism.FourierDecayAlt.Sz.Cfg.u, if_neg h1, if_neg hk]
      rw [hu]
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have e := v_sub c j l
      have hde := hw1 j
      rcases lt_trichotomy j l with hjl | rfl | hlj
      · have h' : (j : ℝ) + 1 ≤ l := by exact_mod_cast hjl
        have : 4 * c.Del * 1 ≤ 4 * c.Del * ((l : ℝ) - j) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        rcases hde with h | h <;> rw [h] <;> apply ne_of_gt <;> linarith
      · rcases hde with h | h <;> rw [h]
        · apply ne_of_gt; linarith
        · apply ne_of_lt; linarith
      · have h' : (l : ℝ) + 1 ≤ j := by exact_mod_cast hlj
        have : 4 * c.Del * ((l : ℝ) - j) ≤ 4 * c.Del * (-1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        rcases hde with h | h <;> rw [h] <;> apply ne_of_lt <;> linarith

/- English proof (translation)
Use `show -(T * T') * ∏ i ∈ Icc 1 c.k, ((Y + 1 / 2 + c.u de i) * (Y + 1 / 2 + c.u de' i)) ≠ 0`. Use `mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero hT hT')) ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_Icc]`.

Conclude with `mul_ne_zero (qfac_ne c hOk hb1 hw hl hY1 hY2 hi.1 hi.2) (qfac_ne c hOk hb1 hw' hl hY1 hY2 hi.1 hi.2)`.
-/
theorem q_ne (hOk : c.Ok) (hb1 : 40 * (c.m : ℝ) * c.k * c.Del ≤ c.b 1) {de de' : ℕ → ℝ} (hw : Sz.IsWord c.k de)
    (hw' : Sz.IsWord c.k de') {l : ℕ} (hl : l + 1 ≤ c.k) {T T' : ℝ} (hT : T ≠ 0) (hT' : T' ≠ 0) {Y : ℝ}
    (hY1 : 5 / 2 ≤ c.v l + Y) (hY2 : c.v l + Y ≤ c.Del / 2) : c.q de de' T T' Y ≠ 0 := by
  show -(T * T') * ∏ i ∈ Icc 1 c.k, ((Y + 1 / 2 + c.u de i) * (Y + 1 / 2 + c.u de' i)) ≠ 0
  refine mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero hT hT')) ?_
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  rw [Finset.mem_Icc] at hi
  exact mul_ne_zero (qfac_ne c hOk hb1 hw hl hY1 hY2 hi.1 hi.2)
    (qfac_ne c hOk hb1 hw' hl hY1 hY2 hi.1 hi.2)

/- English proof (translation)
Establish `hk4 : (4 : ℝ) ≤ c.k` using `by exact_mod_cast hOk.hk`. Establish `hm2 : (2 : ℝ) ≤ c.m` using `by exact_mod_cast hOk.hm`. Establish `hD` using `hOk.hDel`. Establish `hv0` using `hOk.hv0`. Establish `hlk : (l : ℝ) + 1 ≤ c.k` using `by exact_mod_cast hl`.

Establish `hvl : c.vlast ≤ c.v l`. Rewrite using `[v_eq_vlast_add_four_mul_Del c l]`. Use `mul_nonneg (by linarith : (0 : ℝ) ≤ 4 * c.Del) (by linarith : (0 : ℝ) ≤ (c.k : ℝ) - 1 - l)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hmk : (8 : ℝ) * c.Del ≤ (c.m : ℝ) * c.k * c.Del`.

Establish `h8 : (8 : ℝ) ≤ (c.m : ℝ) * c.k` using `by nlinarith`. Conclude with `mul_le_mul_of_nonneg_right h8 (by linarith)`. Use `show (∏ s ∈ Icc 1 (c.k + c.m - 1), ((t - c.v l) + c.lam s)) ≠ 0`. Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `s hs`.

Rewrite `hs` using `[Finset.mem_Icc]`. Distinguish the cases in `hsk : s < c.k`. Establish `hlam : c.lam s = c.v s` using `by simp [Formalism.FourierDecayAlt.Sz.Cfg.lam, hsk]`. Rewrite using `[hlam]`. Establish `e` using `v_sub c s l`.

Break down `lt_trichotomy s l with h | rfl | h` into its components or cases. Establish `h' : (s : ℝ) + 1 ≤ l` using `by exact_mod_cast h`. Establish `: 4 * c.Del * 1 ≤ 4 * c.Del * ((l : ℝ) - s)` using `mul_le_mul_of_nonneg_left (by linarith) (by linarith)`. Apply `ne_of_gt` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion.

Apply `ne_of_gt` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h' : (l : ℝ) + 1 ≤ s` using `by exact_mod_cast h`. Establish `: 4 * c.Del * ((l : ℝ) - s) ≤ 4 * c.Del * (-1)` using `mul_le_mul_of_nonneg_left (by linarith) (by linarith)`. Apply `ne_of_lt` to reduce the goal to its premises.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlam : c.lam s = -c.b (s + 1 - c.k)` using `by simp [Formalism.FourierDecayAlt.Sz.Cfg.lam, hsk]`. Rewrite using `[hlam]`. Establish `hj1 : 1 ≤ s + 1 - c.k` using `by omega`. Establish `hjm : s + 1 - c.k ≤ c.m` using `by have := hOk.hm; omega`.

Establish `hbj` using `b_one_le c hOk _ hj1 hjm`. Apply `ne_of_lt` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem P_ne (hOk : c.Ok) (hb1 : 40 * (c.m : ℝ) * c.k * c.Del ≤ c.b 1) {l : ℕ} (hl : l + 1 ≤ c.k) {t : ℝ}
    (ht0 : 0 < t) (ht4 : t < 4) : c.P (t - c.v l) ≠ 0 := by
  have hk4 : (4 : ℝ) ≤ c.k := by exact_mod_cast hOk.hk
  have hm2 : (2 : ℝ) ≤ c.m := by exact_mod_cast hOk.hm
  have hD := hOk.hDel
  have hv0 := hOk.hv0
  have hlk : (l : ℝ) + 1 ≤ c.k := by exact_mod_cast hl
  have hvl : c.vlast ≤ c.v l := by
    rw [v_eq_vlast_add_four_mul_Del c l]
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 4 * c.Del) (by linarith : (0 : ℝ) ≤ (c.k : ℝ) - 1 - l)
    linarith
  have hmk : (8 : ℝ) * c.Del ≤ (c.m : ℝ) * c.k * c.Del := by
    have h8 : (8 : ℝ) ≤ (c.m : ℝ) * c.k := by nlinarith
    exact mul_le_mul_of_nonneg_right h8 (by linarith)
  show (∏ s ∈ Icc 1 (c.k + c.m - 1), ((t - c.v l) + c.lam s)) ≠ 0
  rw [Finset.prod_ne_zero_iff]
  intro s hs
  rw [Finset.mem_Icc] at hs
  by_cases hsk : s < c.k
  · have hlam : c.lam s = c.v s := by simp [Formalism.FourierDecayAlt.Sz.Cfg.lam, hsk]
    rw [hlam]
    have e := v_sub c s l
    rcases lt_trichotomy s l with h | rfl | h
    · have h' : (s : ℝ) + 1 ≤ l := by exact_mod_cast h
      have : 4 * c.Del * 1 ≤ 4 * c.Del * ((l : ℝ) - s) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      apply ne_of_gt; linarith
    · apply ne_of_gt; linarith
    · have h' : (l : ℝ) + 1 ≤ s := by exact_mod_cast h
      have : 4 * c.Del * ((l : ℝ) - s) ≤ 4 * c.Del * (-1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      apply ne_of_lt; linarith
  · have hlam : c.lam s = -c.b (s + 1 - c.k) := by simp [Formalism.FourierDecayAlt.Sz.Cfg.lam, hsk]
    rw [hlam]
    have hj1 : 1 ≤ s + 1 - c.k := by omega
    have hjm : s + 1 - c.k ≤ c.m := by have := hOk.hm; omega
    have hbj := b_one_le c hOk _ hj1 hjm
    apply ne_of_lt; linarith

/- English proof (translation)
Use extensionality with `Y`. Simplify using `only [Formalism.FourierDecayAlt.Sz.Cfg.cutI, Set.mem_ofPred_eq, Set.mem_Icc]`. Apply the tactic sequence `constructor <;> (rintro ⟨h1, h2⟩; constructor <;> linarith)`.
-/
theorem cutI_eq (l : ℕ) : c.cutI l = Set.Icc (5 / 2 - c.v l) (c.Del / 2 - c.v l) := by
  ext Y
  simp only [Formalism.FourierDecayAlt.Sz.Cfg.cutI, Set.mem_ofPred_eq, Set.mem_Icc]
  constructor <;> (rintro ⟨h1, h2⟩; constructor <;> linarith)

/- English proof (translation)
Use extensionality with `Y`. Simplify using `only [Formalism.FourierDecayAlt.Sz.Cfg.cutIntervalLong, Set.mem_ofPred_eq, Set.mem_Icc]`. Apply the tactic sequence `constructor <;> (rintro ⟨h1, h2⟩; constructor <;> linarith)`.
-/
theorem cutIntervalLong_eq_Icc (l : ℕ) (N : ℝ) : c.cutIntervalLong l N = Set.Icc (5 / 2 - c.v l) (N ^ 3 - c.v l) :=
  by
  ext Y
  simp only [Formalism.FourierDecayAlt.Sz.Cfg.cutIntervalLong, Set.mem_ofPred_eq, Set.mem_Icc]
  constructor <;> (rintro ⟨h1, h2⟩; constructor <;> linarith)

/- English proof (translation)
Establish `hP : Continuous c.P` using `by show Continuous (fun Y : ℝ => ∏ s ∈ Icc 1 (c.k + c.m - 1), (Y + c.lam s))`. Conclude with `continuous_finsetProd _ (fun s _ => continuous_add_const _)`. Establish `hq : Continuous (fun Y => c.q de de' T T' Y)` using `by show Continuous (fun Y : ℝ => -(T * T') * ∏ i ∈ Icc 1 c.k, ((Y + 1 / 2 + c.u de i) * (Y + 1 / 2 + c.u de' i)))`. Conclude with `continuous_const.mul (continuous_finsetProd _ (fun i _ => by fun_prop))`. Establish `hP1 : Continuous (fun Y : ℝ => c.P (Y + 1))` using `hP.comp (continuous_add_const 1)`.

Establish `hd : ContinuousOn (fun Y => c.P Y * c.P (Y + 1) / c.q de de' T T' Y) S` using `(hP.mul hP1).continuousOn.div hq.continuousOn (fun Y hY => q_ne c hOk hb1 hw hw' hl hT hT' (hS Y hY).1 (hS Y hY).2)`. Establish `h : ContinuousOn (fun Y => gm * ((ka ^ (c.m - 1))⁻¹ * Real.sqrt |c.P Y * c.P (Y + 1) / c.q de de' T T' Y|)) S` using `continuousOn_const.mul (continuousOn_const.mul hd.abs.sqrt)`. Conclude with `h`.
-/
private theorem continuousOn_mul_be_of_window (hOk : c.Ok) (hb1 : 40 * (c.m : ℝ) * c.k * c.Del ≤ c.b 1)
    {de de' : ℕ → ℝ} (hw : Formalism.FourierDecayAlt.Sz.IsWord c.k de) (hw' : Formalism.FourierDecayAlt.Sz.IsWord c.k de') {l : ℕ} (hl : l + 1 ≤ c.k)
    {T T' : ℝ} (hT : T ≠ 0) (hT' : T' ≠ 0) (ka gm : ℝ) {S : Set ℝ}
    (hS : ∀ Y ∈ S, 5 / 2 ≤ c.v l + Y ∧ c.v l + Y ≤ c.Del / 2) :
    ContinuousOn (fun Y => gm * c.be ka de de' T T' Y) S := by
  have hP : Continuous c.P := by
    show Continuous (fun Y : ℝ => ∏ s ∈ Icc 1 (c.k + c.m - 1), (Y + c.lam s))
    exact continuous_finsetProd _ (fun s _ => continuous_add_const _)
  have hq : Continuous (fun Y => c.q de de' T T' Y) := by
    show Continuous (fun Y : ℝ =>
      -(T * T') * ∏ i ∈ Icc 1 c.k, ((Y + 1 / 2 + c.u de i) * (Y + 1 / 2 + c.u de' i)))
    exact continuous_const.mul (continuous_finsetProd _ (fun i _ => by fun_prop))
  have hP1 : Continuous (fun Y : ℝ => c.P (Y + 1)) := hP.comp (continuous_add_const 1)
  have hd : ContinuousOn (fun Y => c.P Y * c.P (Y + 1) / c.q de de' T T' Y) S :=
    (hP.mul hP1).continuousOn.div hq.continuousOn
      (fun Y hY => q_ne c hOk hb1 hw hw' hl hT hT' (hS Y hY).1 (hS Y hY).2)
  have h : ContinuousOn (fun Y => gm * ((ka ^ (c.m - 1))⁻¹ *
      Real.sqrt |c.P Y * c.P (Y + 1) / c.q de de' T T' Y|)) S :=
    continuousOn_const.mul (continuousOn_const.mul hd.abs.sqrt)
  exact h

/- English proof (translation)
Rewrite using `[cutI_eq c l]`. Conclude with `isCompact_Icc.bddAbove_image (continuousOn_mul_be_of_window c hOk hb1 hw hw' hl hT hT' ka gm (fun Y hY => ⟨by linarith [hY.1], by linarith [hY.2]⟩))`.
-/
theorem bdd_cutI (hOk : c.Ok) (hb1 : 40 * (c.m : ℝ) * c.k * c.Del ≤ c.b 1) {de de' : ℕ → ℝ} (hw : Sz.IsWord c.k de)
    (hw' : Sz.IsWord c.k de') {l : ℕ} (hl : l + 1 ≤ c.k) {T T' : ℝ} (hT : T ≠ 0) (hT' : T' ≠ 0) (ka gm : ℝ) :
    BddAbove ((fun Y => gm * c.be ka de de' T T' Y) '' c.cutI l) := by
  rw [cutI_eq c l]
  exact isCompact_Icc.bddAbove_image (continuousOn_mul_be_of_window c hOk hb1 hw hw' hl hT hT' ka gm
    (fun Y hY => ⟨by linarith [hY.1], by linarith [hY.2]⟩))

/- English proof (translation)
Establish `hP0 : c.P (11 / 4 - c.v l) ≠ 0` using `P_ne c hOk hb1 hl (by norm_num) (by norm_num)`. Establish `hP1 : c.P (11 / 4 - c.v l + 1) ≠ 0`. Establish `h` using `P_ne c hOk hb1 hl (t := 15 / 4) (by norm_num) (by norm_num)`. Rewrite `h` using `[show (15 / 4 : ℝ) - c.v l = 11 / 4 - c.v l + 1 by ring]`. Then use the resulting hypothesis. Establish `hq : c.q de de' T T' (11 / 4 - c.v l) ≠ 0` using `q_ne c hOk hb1 hw hw' hl hT hT' (by linarith) (by linarith)`.

Establish `hs : 0 < Real.sqrt |c.P (11 / 4 - c.v l) * c.P (11 / 4 - c.v l + 1) / c.q de de' T T' (11 / 4 - c.v l)|` using `Real.sqrt_pos.mpr (abs_pos.mpr (div_ne_zero (mul_ne_zero hP0 hP1) hq))`. Use `show 0 < gm * ((ka ^ (c.m - 1))⁻¹ * Real.sqrt |c.P (11 / 4 - c.v l) * c.P (11 / 4 - c.v l + 1) / c.q de de' T T' (11 / 4 - c.v l)|)`. Conclude with `mul_pos hgm (mul_pos (inv_pos.mpr (pow_pos hka _)) hs)`.
-/
private theorem mul_be_pos_of_isWord (hOk : c.Ok) (hb1 : 40 * (c.m : ℝ) * c.k * c.Del ≤ c.b 1)
    {de de' : ℕ → ℝ} (hw : Formalism.FourierDecayAlt.Sz.IsWord c.k de) (hw' : Formalism.FourierDecayAlt.Sz.IsWord c.k de') {l : ℕ} (hl : l + 1 ≤ c.k)
    {T T' : ℝ} (hT : T ≠ 0) (hT' : T' ≠ 0) {ka gm : ℝ} (hka : 0 < ka) (hgm : 0 < gm)
    (hN : 11 / 4 ≤ c.Del / 2) : 0 < gm * c.be ka de de' T T' (11 / 4 - c.v l) := by
  have hP0 : c.P (11 / 4 - c.v l) ≠ 0 := P_ne c hOk hb1 hl (by norm_num) (by norm_num)
  have hP1 : c.P (11 / 4 - c.v l + 1) ≠ 0 := by
    have h := P_ne c hOk hb1 hl (t := 15 / 4) (by norm_num) (by norm_num)
    rwa [show (15 / 4 : ℝ) - c.v l = 11 / 4 - c.v l + 1 by ring] at h
  have hq : c.q de de' T T' (11 / 4 - c.v l) ≠ 0 :=
    q_ne c hOk hb1 hw hw' hl hT hT' (by linarith) (by linarith)
  have hs : 0 < Real.sqrt |c.P (11 / 4 - c.v l) * c.P (11 / 4 - c.v l + 1) / c.q de de' T T' (11 / 4 - c.v l)| :=
    Real.sqrt_pos.mpr (abs_pos.mpr (div_ne_zero (mul_ne_zero hP0 hP1) hq))
  show 0 < gm * ((ka ^ (c.m - 1))⁻¹ *
    Real.sqrt |c.P (11 / 4 - c.v l) * c.P (11 / 4 - c.v l + 1) / c.q de de' T T' (11 / 4 - c.v l)|)
  exact mul_pos hgm (mul_pos (inv_pos.mpr (pow_pos hka _)) hs)

/- English proof (translation)
Establish `hbdd` using `bdd_cutI c hOk hb1 hw hw' hl hT hT' ka gm`. Establish `hY0 : (11 / 4 - c.v l) ∈ c.cutI l` using `by show 5 / 2 ≤ c.v l + (11 / 4 - c.v l) ∧ c.v l + (11 / 4 - c.v l) ≤ c.Del / 2`. Apply the tactic sequence `constructor <;> linarith`. Conclude with `lt_of_lt_of_le (mul_be_pos_of_isWord c hOk hb1 hw hw' hl hT hT' hka hgm (by linarith)) (le_csSup hbdd ⟨_, hY0, rfl⟩)`.
-/
theorem supI_pos (hOk : c.Ok) (hb1 : 40 * (c.m : ℝ) * c.k * c.Del ≤ c.b 1) (hD : 11 / 2 ≤ c.Del) {de de' : ℕ → ℝ}
    (hw : Sz.IsWord c.k de) (hw' : Sz.IsWord c.k de') {l : ℕ} (hl : l + 1 ≤ c.k) {T T' : ℝ} (hT : T ≠ 0)
    (hT' : T' ≠ 0) {ka gm : ℝ} (hka : 0 < ka) (hgm : 0 < gm) :
    0 < sSup ((fun Y => gm * c.be ka de de' T T' Y) '' c.cutI l) := by
  have hbdd := bdd_cutI c hOk hb1 hw hw' hl hT hT' ka gm
  have hY0 : (11 / 4 - c.v l) ∈ c.cutI l := by
    show 5 / 2 ≤ c.v l + (11 / 4 - c.v l) ∧ c.v l + (11 / 4 - c.v l) ≤ c.Del / 2
    constructor <;> linarith
  exact lt_of_lt_of_le (mul_be_pos_of_isWord c hOk hb1 hw hw' hl hT hT' hka hgm (by linarith))
    (le_csSup hbdd ⟨_, hY0, rfl⟩)

/- English proof (translation)
Establish `hbdd : BddAbove ((fun Y => gm * c.be ka de de' T T' Y) '' c.cutIntervalLong l N)`. Rewrite using `[cutIntervalLong_eq_Icc c l N]`. Conclude with `isCompact_Icc.bddAbove_image (continuousOn_mul_be_of_window c hOk hb1 hw hw' hl hT hT' ka gm (fun Y hY => ⟨by linarith [hY.1], by linarith [hY.2]⟩))`. Establish `hY0 : (11 / 4 - c.v l) ∈ c.cutIntervalLong l N` using `by show 5 / 2 ≤ c.v l + (11 / 4 - c.v l) ∧ c.v l + (11 / 4 - c.v l) ≤ N ^ 3`. Apply the tactic sequence `constructor <;> linarith`.

Conclude with `lt_of_lt_of_le (mul_be_pos_of_isWord c hOk hb1 hw hw' hl hT hT' hka hgm (by linarith)) (le_csSup hbdd ⟨_, hY0, rfl⟩)`.
-/
theorem sSup_be_image_cutIntervalLong_pos (hOk : c.Ok) (hb1 : 40 * (c.m : ℝ) * c.k * c.Del ≤ c.b 1) {N : ℝ} (hN1 : 11 / 4 ≤ N ^ 3)
    (hN2 : N ^ 3 ≤ c.Del / 2) {de de' : ℕ → ℝ} (hw : Sz.IsWord c.k de) (hw' : Sz.IsWord c.k de') {l : ℕ}
    (hl : l + 1 ≤ c.k) {T T' : ℝ} (hT : T ≠ 0) (hT' : T' ≠ 0) {ka gm : ℝ} (hka : 0 < ka) (hgm : 0 < gm) :
    0 < sSup ((fun Y => gm * c.be ka de de' T T' Y) '' c.cutIntervalLong l N) := by
  have hbdd : BddAbove ((fun Y => gm * c.be ka de de' T T' Y) '' c.cutIntervalLong l N) := by
    rw [cutIntervalLong_eq_Icc c l N]
    exact isCompact_Icc.bddAbove_image (continuousOn_mul_be_of_window c hOk hb1 hw hw' hl hT hT' ka gm
      (fun Y hY => ⟨by linarith [hY.1], by linarith [hY.2]⟩))
  have hY0 : (11 / 4 - c.v l) ∈ c.cutIntervalLong l N := by
    show 5 / 2 ≤ c.v l + (11 / 4 - c.v l) ∧ c.v l + (11 / 4 - c.v l) ≤ N ^ 3
    constructor <;> linarith
  exact lt_of_lt_of_le (mul_be_pos_of_isWord c hOk hb1 hw hw' hl hT hT' hka hgm (by linarith))
    (le_csSup hbdd ⟨_, hY0, rfl⟩)

end Formalism.L2.SG.Pf.ThresholdBounds
