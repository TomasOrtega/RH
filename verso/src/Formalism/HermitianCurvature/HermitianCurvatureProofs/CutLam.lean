import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMP2

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

section cfg

variable (c : Sz.Cfg)

/- English proof (translation)
Simplify using `only [Sz.Cfg.v]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cfg_v_sub (i : ℕ) : c.v i - c.v (i + 1) = 4 * c.Del := by
  simp only [Sz.Cfg.v]
  push_cast
  ring

/- English proof (translation)
Establish `hD` using `hok.hDel`. Establish `hi' : (i : ℝ) + 1 ≤ (c.k : ℝ)` using `by exact_mod_cast hi`. Simplify using `only [Sz.Cfg.v]`. Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem cfg_v_ge_vlast (hok : c.Ok) (i : ℕ) (hi : i + 1 ≤ c.k) : c.vlast ≤ c.v i := by
  have hD := hok.hDel
  have hi' : (i : ℝ) + 1 ≤ (c.k : ℝ) := by exact_mod_cast hi
  simp only [Sz.Cfg.v]
  push_cast
  nlinarith

/- English proof (translation)
Establish `hD` using `hok.hDel`. Establish `hij' : (i : ℝ) + 1 ≤ (j : ℝ)` using `by exact_mod_cast hij`. Simplify using `only [Sz.Cfg.v]`. Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem cfg_v_lt (hok : c.Ok) {i j : ℕ} (hij : i < j) : c.v j < c.v i := by
  have hD := hok.hDel
  have hij' : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hij
  simp only [Sz.Cfg.v]
  push_cast
  nlinarith

/- English proof (translation)
Introduce `j j' hj hjj' hj'm`. Proceed by induction on `j' with`. Consider the case `zero => omega`. Consider the case `succ n ih`. Establish `hg` using `hok.hgap n (by omega) (by omega)`.

Break down `Nat.lt_succ_iff_lt_or_eq.mp hjj' with h | h` into its components or cases. Use `ih h (by omega)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Substitute `h` using the available equality. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cfg_b_lt (hok : c.Ok) : ∀ {j j' : ℕ}, 1 ≤ j → j < j' → j' ≤ c.m → c.b j < c.b j' := by
  intro j j' hj hjj' hj'm
  induction j' with
  | zero => omega
  | succ n ih =>
    have hg := hok.hgap n (by omega) (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.mp hjj' with h | h
    · have := ih h (by omega)
      linarith
    · subst h
      linarith

/- English proof (translation)
Break down `Nat.lt_or_ge 1 j with h | h` into its components or cases. Use `cfg_b_lt c hok (le_refl 1) h hjm` as an intermediate fact. Combine the linear relations using `[hok.hb1]`. Establish `e : j = 1` using `by omega`. Substitute `e` using the available equality.

Conclude with `hok.hb1`.
-/
theorem cfg_b_ge_one (hok : c.Ok) {j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ c.m) : 1 ≤ c.b j := by
  rcases Nat.lt_or_ge 1 j with h | h
  · have := cfg_b_lt c hok (le_refl 1) h hjm
    linarith [hok.hb1]
  · have e : j = 1 := by omega
    subst e
    exact hok.hb1

/- English proof (translation)
Establish `hk4` using `hok.hk`. Establish `hD` using `hok.hDel`. Establish `hv0` using `hok.hv0`. Establish `hb1` using `hok.hb1`. Establish `ha` using `hok.ha`.

Establish `hkR : (4 : ℝ) ≤ c.k` using `by exact_mod_cast hk4`. Establish `hlamv : ∀ s : ℕ, s < c.k → c.lam s = c.v s` using `fun s hs => by`. Rewrite using `[Sz.Cfg.lam, if_pos hs]`. Establish `hlamb : ∀ s : ℕ, ¬ s < c.k → c.lam s = -c.b (s + 1 - c.k)` using `fun s hs => by`. Rewrite using `[Sz.Cfg.lam, if_neg hs]`.

Establish `hu1 : c.u de 1 = c.a` using `by rw [Sz.Cfg.u, if_pos rfl]`. Establish `huk : c.u de c.k = c.ulast` using `by rw [Sz.Cfg.u, if_neg (by omega), if_pos rfl]`. Establish `hum : ∀ j : ℕ, j ≠ 1 → j ≠ c.k → c.u de j = c.v (j - 1) - 1 / 2 - de (j - 1) * c.Del` using `fun j h1 h2 => by rw [Sz.Cfg.u, if_neg h1, if_neg h2]`. Establish `hde0 : ∀ j, 0 ≤ de j * c.Del ∧ de j * c.Del ≤ c.Del` using `fun j => by`. Apply the tactic sequence `rcases hde j with h | h <;> simp [h] <;> linarith`.

Establish `hul : c.ulast = if c.top then -c.bp else c.vlast - 1 / 2` using `rfl`. Establish `hvk : c.v (c.k - 1) = c.vlast`. Simplify using `only [Sz.Cfg.v]`. Rewrite using `[Nat.cast_sub (by omega)]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨?_, fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩` and prove the remaining obligations. Introduce `s t hst`. Establish `hst' : (s : ℕ) < t` using `hst`. Establish `ht` using `t.isLt`.

Use `show c.lam ((t : ℕ) + 1) < c.lam ((s : ℕ) + 1)`. Distinguish the cases in `h1 : (t : ℕ) + 1 < c.k`. Rewrite using `[hlamv _ h1, hlamv _ (by omega)]`. Conclude with `cfg_v_lt c hok (by omega)`. Rewrite using `[hlamb _ h1]`.

Distinguish the cases in `h2 : (s : ℕ) + 1 < c.k`. Rewrite using `[hlamv _ h2]`. Use `cfg_b_ge_one c hok (j := (t : ℕ) + 1 + 1 - c.k) (by omega) (by omega)` as an intermediate fact. Use `cfg_v_ge_vlast c hok ((s : ℕ) + 1) (by omega)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[hlamb _ h2]`. Use `cfg_b_lt c hok (j := (s : ℕ) + 1 + 1 - c.k) (j' := (t : ℕ) + 1 + 1 - c.k) (by omega) (by omega) (by omega)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `show c.lam ((i : ℕ) + 1) < c.u de ((i : ℕ) + 1)`. Break down `Nat.eq_zero_or_pos (i : ℕ) with h0 | h0` into its components or cases.

Rewrite using `[h0, zero_add, hlamv 1 (by omega), hu1]`. Establish `: 0 < 4 * (c.k : ℝ) * c.Del`. Use `mul_le_mul hkR hD zero_le_one (by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.

Distinguish the cases in `h2 : (i : ℕ) + 1 < c.k`. Rewrite using `[hlamv _ h2, hum _ (by omega) (by omega), Nat.add_sub_cancel]`. Use `cfg_v_sub c (i : ℕ)` as an intermediate fact. Use `hde0 (i : ℕ)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `e : (i : ℕ) + 1 = c.k` using `by omega`. Rewrite using `[hlamb _ h2, e, Nat.add_sub_cancel_left, huk, hul]`. Use `split_ifs with htp`. Use `(hok.htop htp).2` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the linear equalities and inequalities to obtain the conclusion. Use `show c.u de ((i : ℕ) + 2) < c.lam ((i : ℕ) + 1)`. Rewrite using `[hlamv _ (by omega)]`. Distinguish the cases in `h2 : (i : ℕ) + 2 = c.k`. Establish `e : (i : ℕ) + 1 = c.k - 1` using `by omega`.

Rewrite using `[h2, huk, hul, e, hvk]`. Use `split_ifs with htp`. Use `(hok.htop htp).1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `e : (i : ℕ) + 2 - 1 = (i : ℕ) + 1` using `by omega`. Rewrite using `[hum _ (by omega) h2, e]`. Use `hde0 ((i : ℕ) + 1)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cfg_interlaces (r : ℕ) (hm : c.m = 2 * r + 2) (hk : 2 ≤ c.k) (hok : c.Ok) (de : ℕ → ℝ)
    (hde : ∀ i, de i = 0 ∨ de i = 1) :
    C7.LamInterlaces c.k r (c.u de) (fun s : Fin (c.k + 2 * r + 1) => c.lam ((s : ℕ) + 1)) := by
  have hk4 := hok.hk
  have hD := hok.hDel
  have hv0 := hok.hv0
  have hb1 := hok.hb1
  have ha := hok.ha
  have hkR : (4 : ℝ) ≤ c.k := by exact_mod_cast hk4
  have hlamv : ∀ s : ℕ, s < c.k → c.lam s = c.v s := fun s hs => by
    rw [Sz.Cfg.lam, if_pos hs]
  have hlamb : ∀ s : ℕ, ¬ s < c.k → c.lam s = -c.b (s + 1 - c.k) := fun s hs => by
    rw [Sz.Cfg.lam, if_neg hs]
  have hu1 : c.u de 1 = c.a := by rw [Sz.Cfg.u, if_pos rfl]
  have huk : c.u de c.k = c.ulast := by rw [Sz.Cfg.u, if_neg (by omega), if_pos rfl]
  have hum : ∀ j : ℕ, j ≠ 1 → j ≠ c.k → c.u de j = c.v (j - 1) - 1 / 2 - de (j - 1) * c.Del :=
    fun j h1 h2 => by rw [Sz.Cfg.u, if_neg h1, if_neg h2]
  have hde0 : ∀ j, 0 ≤ de j * c.Del ∧ de j * c.Del ≤ c.Del := fun j => by
    rcases hde j with h | h <;> simp [h] <;> linarith
  have hul : c.ulast = if c.top then -c.bp else c.vlast - 1 / 2 := rfl
  have hvk : c.v (c.k - 1) = c.vlast := by
    simp only [Sz.Cfg.v]
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  refine ⟨?_, fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
  · intro s t hst
    have hst' : (s : ℕ) < t := hst
    have ht := t.isLt
    show c.lam ((t : ℕ) + 1) < c.lam ((s : ℕ) + 1)
    by_cases h1 : (t : ℕ) + 1 < c.k
    · rw [hlamv _ h1, hlamv _ (by omega)]
      exact cfg_v_lt c hok (by omega)
    · rw [hlamb _ h1]
      by_cases h2 : (s : ℕ) + 1 < c.k
      · rw [hlamv _ h2]
        have := cfg_b_ge_one c hok (j := (t : ℕ) + 1 + 1 - c.k) (by omega) (by omega)
        have := cfg_v_ge_vlast c hok ((s : ℕ) + 1) (by omega)
        linarith
      · rw [hlamb _ h2]
        have := cfg_b_lt c hok (j := (s : ℕ) + 1 + 1 - c.k) (j' := (t : ℕ) + 1 + 1 - c.k)
          (by omega) (by omega) (by omega)
        linarith
  · show c.lam ((i : ℕ) + 1) < c.u de ((i : ℕ) + 1)
    rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | h0
    · rw [h0, zero_add, hlamv 1 (by omega), hu1]
      have : 0 < 4 * (c.k : ℝ) * c.Del := by
        have := mul_le_mul hkR hD zero_le_one (by linarith)
        linarith
      linarith
    · by_cases h2 : (i : ℕ) + 1 < c.k
      · rw [hlamv _ h2, hum _ (by omega) (by omega), Nat.add_sub_cancel]
        have := cfg_v_sub c (i : ℕ)
        have := hde0 (i : ℕ)
        linarith
      · have e : (i : ℕ) + 1 = c.k := by omega
        rw [hlamb _ h2, e, Nat.add_sub_cancel_left, huk, hul]
        split_ifs with htp
        · have := (hok.htop htp).2
          linarith
        · linarith
  · show c.u de ((i : ℕ) + 2) < c.lam ((i : ℕ) + 1)
    rw [hlamv _ (by omega)]
    by_cases h2 : (i : ℕ) + 2 = c.k
    · have e : (i : ℕ) + 1 = c.k - 1 := by omega
      rw [h2, huk, hul, e, hvk]
      split_ifs with htp
      · have := (hok.htop htp).1
        linarith
      · linarith
    · have e : (i : ℕ) + 2 - 1 = (i : ℕ) + 1 := by omega
      rw [hum _ (by omega) h2, e]
      have := hde0 ((i : ℕ) + 1)
      linarith

end cfg

/- English proof (translation)
Introduce `E _ _ _ Wp Wq _ _ _ _ S hk hok hw hw' v`. Conclude with `⟨cfg_interlaces (S.G.place (S.pl v)) S.G.r rfl hk (hok v) S.de hw.1, cfg_interlaces (S.G.place (S.pl v)) S.G.r rfl hk (hok v) S.de' hw'.1⟩`.
-/
theorem eigenvalue_configuration_interlaces : LamCfgInterlaces := by
  intro E _ _ _ Wp Wq _ _ _ _ S hk hok hw hw' v
  exact ⟨cfg_interlaces (S.G.place (S.pl v)) S.G.r rfl hk (hok v) S.de hw.1,
    cfg_interlaces (S.G.place (S.pl v)) S.G.r rfl hk (hok v) S.de' hw'.1⟩

end Formalism.FourierDecayAlt.P.CutMP
