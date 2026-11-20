import Formalism.FrobeniusBaseCase.FrobeniusBaseCaseProofs.ChainI
import Formalism.FrobeniusBaseCase.FrobeniusBaseCaseProofs.BaseCaseKOneHolds

open MvPowerSeries

namespace Formalism.BaseCaseIdentities

noncomputable section

open Classical

namespace Data

variable {k : Type*} [Field k] {Z C : Type*} [Fintype Z] [Fintype C] (D : Data k Z C)

def mu (J : ℕ) (c : C) : MvPowerSeries Z k := if D.lev c < J then D.m (D.lev c) c else 0

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h c`. Unfold `mu`. Use `split_ifs with hc`. Conclude with `h.1 c hc`.

Rewrite using `[sub_zero]`. Conclude with `h.2 c (not_lt.1 hc)`. Introduce `h`. Use `⟨fun c hc => ?_, fun c hc => ?_⟩` and prove the remaining obligations. Use `h c` as an intermediate fact.

Rewrite `this` using `[mu, if_pos hc]`. Then use the resulting hypothesis. Use `h c` as an intermediate fact. Rewrite `this` using `[mu, if_neg (not_lt.2 hc), sub_zero]`. Then use the resulting hypothesis.
-/
theorem inWTo_iff (J : ℕ) (t : C → MvPowerSeries Z k) :
    D.InWTo J t ↔ ∀ c, D.Wt D.top (t c - D.mu J c) := by
  constructor
  · intro h c
    unfold mu
    split_ifs with hc
    · exact h.1 c hc
    · rw [sub_zero]; exact h.2 c (not_lt.1 hc)
  · intro h
    refine ⟨fun c hc => ?_, fun c hc => ?_⟩
    · have := h c
      rwa [mu, if_pos hc] at this
    · have := h c
      rwa [mu, if_neg (not_lt.2 hc), sub_zero] at this

def main (J : ℕ) (c b : C) : MvPowerSeries Z k :=
  if D.lev c < J ∧ D.lev c + 1 < D.K then
    MvPowerSeries.C (-(D.l : k)⁻¹ * D.g c b) * frob D.q (D.m (D.lev c) c) else 0

/- English proof (translation)
Unfold `main`. Use `split_ifs with h1`. Rewrite using `[D.g_supp c h1.2 b h, mul_zero, map_zero, zero_mul]`. Both sides reduce to the same expression.
-/
theorem main_eq_zero (J : ℕ) (c b : C) (h : D.lev b ≠ D.lev c + 1) : D.main J c b = 0 := by
  unfold main
  split_ifs with h1
  · rw [D.g_supp c h1.2 b h, mul_zero, map_zero, zero_mul]
  · rfl

/- English proof (translation)
Establish `hK` using `D.K_pos`. Distinguish the cases in `hb0 : D.lev b = 0`. Establish `h1 : D.mu (min (J + 1) D.K) b = D.zvec b`. Rewrite using `[mu, if_pos (by rw [hb0]; omega), hb0]`. Both sides reduce to the same expression.

Rewrite using `[h1, Finset.sum_eq_zero, add_zero]`. Introduce `c _`. Conclude with `D.main_eq_zero J c b (by omega)`. Rewrite using `[D.zvec_eq_zero hb0, zero_add]`. Distinguish the cases in `hb : D.lev b < min (J + 1) D.K`.

Take `⟨s, hs⟩ : ∃ s, D.lev b = s + 1` from `⟨D.lev b - 1, by omega⟩`. Rewrite using `[mu, if_pos hb, hs, m_succ, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Distinguish the cases in `hc : D.lev c = s`. Rewrite using `[main, if_pos ⟨by omega, by omega⟩, hc, map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[D.m_eq_zero (by omega) hc, frob_zero D.q_pos, zero_mul, mul_zero, D.main_eq_zero J c b (by omega)]`. Rewrite using `[mu, if_neg hb]`. Use `symm`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `c _`. Unfold `main`. Use `split_ifs with h`. Rewrite using `[D.g_supp c h.2 b (by omega), mul_zero, map_zero, zero_mul]`. Both sides reduce to the same expression.
-/
theorem mu_succ (J : ℕ) (hJ1 : 1 ≤ J) (hJK : J ≤ D.K) (b : C) :
    D.mu (min (J + 1) D.K) b = D.zvec b + ∑ c, D.main J c b := by
  have hK := D.K_pos
  by_cases hb0 : D.lev b = 0
  · have h1 : D.mu (min (J + 1) D.K) b = D.zvec b := by
      rw [mu, if_pos (by rw [hb0]; omega), hb0]
      rfl
    rw [h1, Finset.sum_eq_zero, add_zero]
    intro c _
    exact D.main_eq_zero J c b (by omega)
  · rw [D.zvec_eq_zero hb0, zero_add]
    by_cases hb : D.lev b < min (J + 1) D.K
    · obtain ⟨s, hs⟩ : ∃ s, D.lev b = s + 1 := ⟨D.lev b - 1, by omega⟩
      rw [mu, if_pos hb, hs, m_succ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases hc : D.lev c = s
      · rw [main, if_pos ⟨by omega, by omega⟩, hc, map_mul]
        ring
      · rw [D.m_eq_zero (by omega) hc, frob_zero D.q_pos, zero_mul, mul_zero,
          D.main_eq_zero J c b (by omega)]
    · rw [mu, if_neg hb]
      symm
      apply Finset.sum_eq_zero
      intro c _
      unfold main
      split_ifs with h
      · rw [D.g_supp c h.2 b (by omega), mul_zero, map_zero, zero_mul]
      · rfl

/- English proof (translation)
Unfold `top`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem rho_le_top : rho D.l ≤ D.top := by
  unfold top
  linarith

/- English proof (translation)
Establish `h` using `D.al_good c hg 2 b (by norm_num)`. Establish `h1 : (-(((2 : ℕ) : ℝ) - 1)) = (-1 : ℝ)` using `by norm_num`. Rewrite `h` using `[h1]`. Then use the resulting hypothesis.
-/
theorem v_al_two (c : C) (hg : D.good c) (b : C) : ((-1 : ℝ) : WithTop ℝ) ≤ D.v (D.al c 2 b) := by
  have h := D.al_good c hg 2 b (by norm_num)
  have h1 : (-(((2 : ℕ) : ℝ) - 1)) = (-1 : ℝ) := by norm_num
  rwa [h1] at h

/- English proof (translation)
Establish `hl` using `D.l_ge`. Establish `hcK : D.lev c < D.K` using `by omega`. Establish `hgood` using `D.pure_good c hcK`. Establish `hal` using `D.v_al_two c hgood b`. Establish `hρ` using `rho_pos hl`.

Take `⟨μ, hμdef⟩ : ∃ μ, μ = D.m (D.lev c) c` from `⟨_, rfl⟩`. Take `⟨ν, hνdef⟩ : ∃ ν, ν = τ - μ` from `⟨_, rfl⟩`. Establish `hτ : τ = μ + ν` using `by rw [hνdef]; ring`. Establish `hμ : D.Wt (rho D.l) μ` using `by rw [hμdef]; exact D.wt_m_rho _ _`. Establish `hν' : D.Wt D.top ν` using `by rw [hνdef, hμdef]; exact hν`.

Establish `hdec : MvPowerSeries.C (D.al c 2 b) * τ ^ (D.l ^ 2) + D.main J c b = MvPowerSeries.C (D.al c 2 b) * (μ ^ (D.l ^ 2) - frob D.q μ) + MvPowerSeries.C (D.al c 2 b) * ((μ + ν) ^ (D.l ^ 2) - μ ^ (D.l ^ 2) - ν ^ (D.l ^ 2)) + MvPowerSeries.C (D.al c 2 b) * ν ^ (D.l ^ 2) + (MvPowerSeries. …`. Rewrite using `[hτ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hdec]`. Establish `hqρ` using `D.q_rho`.

Use `HasWt.add (HasWt.add (HasWt.add ?_ ?_) ?_) ?_` and prove the remaining obligations. Establish `h1 : D.Wt (1 + qnum D.l * rho D.l) (μ ^ (D.l ^ 2) - frob D.q μ)`. Rewrite using `[hμdef]`. Conclude with `D.wt_m_pow_sub_frob hcK c`. Use `HasWt.mono ?_ (HasWt.C_mul hal h1)` and prove the remaining obligations.

Unfold `top`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `hasWt_add_pow_sub (e := 2) D.l_prime D.v_l D.rho_le_top hμ hν'`. Use `HasWt.mono ?_ (HasWt.C_mul hal h1)` and prove the remaining obligations. Use `rho_mul hl` as an intermediate fact.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `HasWt.pow hν' (D.l ^ 2)`. Use `HasWt.mono ?_ (HasWt.C_mul hal h1)` and prove the remaining obligations. Use `num_good hl (j := 2) le_rfl` as an intermediate fact.

Unfold `top`. Move the coercions through the operations in `at this ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Distinguish the cases in `hK1 : D.lev c + 1 < D.K`. Rewrite using `[main, if_pos ⟨hcJ, hK1⟩, ← hμdef, ← add_mul, ← map_add]`.

Establish `h1 : D.al c 2 b + -(D.l : k)⁻¹ * D.g c b = D.lam c b`. Rewrite using `[D.al_two c hcK b]`. Use `D.l_ne` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h1]`. Establish `h2 : ((0 : ℝ) : WithTop ℝ) ≤ D.v (D.lam c b)` using `by simpa using D.lam_int c b`. Use `HasWt.mono ?_ (HasWt.C_mul h2 (HasWt.frob hμ D.q))` and prove the remaining obligations. Rewrite using `[D.q_cast]`. Unfold `top`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[main, if_neg (fun h => hK1 h.2), add_zero]`. Establish `h1 : D.Wt (rho D.l + qnum D.l ^ (D.lev c) * sg D.l D.i) μ`. Rewrite using `[hμdef]`. Conclude with `D.wt_m _ _`.

Use `HasWt.mono ?_ (HasWt.C_mul hal (HasWt.frob h1 D.q))` and prove the remaining obligations. Rewrite using `[D.q_cast]`. Establish `hlev : D.lev c + 1 = Kn D.i`. Establish `: D.K = Kn D.i` using `rfl`. Use linear arithmetic over natural numbers and integers.

Establish `h2` using `identity_twenty_d D.l D.i (by omega) D.i_odd`. Rewrite `h2` using `[← hlev, pow_succ']`. Use `D.lR` as an intermediate fact. Unfold `top`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem wt_two (J : ℕ) (hJK : J ≤ D.K) (c b : C) (hcJ : D.lev c < J) (τ : MvPowerSeries Z k)
    (hν : D.Wt D.top (τ - D.m (D.lev c) c)) :
    D.Wt D.top (MvPowerSeries.C (D.al c 2 b) * τ ^ (D.l ^ 2) + D.main J c b) := by
  have hl := D.l_ge
  have hcK : D.lev c < D.K := by omega
  have hgood := D.pure_good c hcK
  have hal := D.v_al_two c hgood b
  have hρ := rho_pos hl
  obtain ⟨μ, hμdef⟩ : ∃ μ, μ = D.m (D.lev c) c := ⟨_, rfl⟩
  obtain ⟨ν, hνdef⟩ : ∃ ν, ν = τ - μ := ⟨_, rfl⟩
  have hτ : τ = μ + ν := by rw [hνdef]; ring
  have hμ : D.Wt (rho D.l) μ := by rw [hμdef]; exact D.wt_m_rho _ _
  have hν' : D.Wt D.top ν := by rw [hνdef, hμdef]; exact hν
  have hdec : MvPowerSeries.C (D.al c 2 b) * τ ^ (D.l ^ 2) + D.main J c b =
      MvPowerSeries.C (D.al c 2 b) * (μ ^ (D.l ^ 2) - frob D.q μ)
      + MvPowerSeries.C (D.al c 2 b) * ((μ + ν) ^ (D.l ^ 2) - μ ^ (D.l ^ 2) - ν ^ (D.l ^ 2))
      + MvPowerSeries.C (D.al c 2 b) * ν ^ (D.l ^ 2)
      + (MvPowerSeries.C (D.al c 2 b) * frob D.q μ + D.main J c b) := by
    rw [hτ]; ring
  rw [hdec]
  have hqρ := D.q_rho
  refine HasWt.add (HasWt.add (HasWt.add ?_ ?_) ?_) ?_
  · have h1 : D.Wt (1 + qnum D.l * rho D.l) (μ ^ (D.l ^ 2) - frob D.q μ) := by
      rw [hμdef]; exact D.wt_m_pow_sub_frob hcK c
    refine HasWt.mono ?_ (HasWt.C_mul hal h1)
    unfold top
    linarith
  · have h1 := hasWt_add_pow_sub (e := 2) D.l_prime D.v_l D.rho_le_top hμ hν'
    refine HasWt.mono ?_ (HasWt.C_mul hal h1)
    have := rho_mul hl
    push_cast
    linarith
  · have h1 := HasWt.pow hν' (D.l ^ 2)
    refine HasWt.mono ?_ (HasWt.C_mul hal h1)
    have := num_good hl (j := 2) le_rfl
    unfold top
    push_cast at this ⊢
    linarith
  · by_cases hK1 : D.lev c + 1 < D.K
    · rw [main, if_pos ⟨hcJ, hK1⟩, ← hμdef, ← add_mul, ← map_add]
      have h1 : D.al c 2 b + -(D.l : k)⁻¹ * D.g c b = D.lam c b := by
        rw [D.al_two c hcK b]
        have := D.l_ne
        field_simp
        ring
      rw [h1]
      have h2 : ((0 : ℝ) : WithTop ℝ) ≤ D.v (D.lam c b) := by simpa using D.lam_int c b
      refine HasWt.mono ?_ (HasWt.C_mul h2 (HasWt.frob hμ D.q))
      rw [D.q_cast]
      unfold top
      linarith
    · rw [main, if_neg (fun h => hK1 h.2), add_zero]
      have h1 : D.Wt (rho D.l + qnum D.l ^ (D.lev c) * sg D.l D.i) μ := by
        rw [hμdef]; exact D.wt_m _ _
      refine HasWt.mono ?_ (HasWt.C_mul hal (HasWt.frob h1 D.q))
      rw [D.q_cast]
      have hlev : D.lev c + 1 = Kn D.i := by
        have : D.K = Kn D.i := rfl
        omega
      have h2 := identity_twenty_d D.l D.i (by omega) D.i_odd
      rw [← hlev, pow_succ'] at h2
      have := D.lR
      unfold top
      nlinarith

/- English proof (translation)
Establish `hl` using `D.l_ge`. Distinguish the cases in `hcJ : D.lev c < J`. Establish `hcK : D.lev c < D.K` using `by omega`. Establish `hgood` using `D.pure_good c hcK`. Establish `hν : D.Wt D.top (t c - D.m (D.lev c) c)`.

Use `ht c` as an intermediate fact. Rewrite `this` using `[mu, if_pos hcJ]`. Then use the resulting hypothesis. Establish `ht' : D.Wt (rho D.l) (t c)`. Establish `h1` using `HasWt.add (D.wt_m_rho (D.lev c) c) (HasWt.mono D.rho_le_top hν)`. Rewrite `h1` using `[add_sub_cancel]`. Then use the resulting hypothesis.

Establish `h2mem : 2 ∈ Finset.Icc 1 N` using `Finset.mem_Icc.2 ⟨by norm_num, hN⟩`. Rewrite using `[← Finset.add_sum_erase _ _ h2mem, add_right_comm]`. Use `HasWt.add (D.wt_two J hJK c b hcJ (t c) hν) ?_` and prove the remaining obligations. Apply `HasWt.sum` to reduce the goal to its premises. Introduce `j hj`.

Establish `hj' : j ≠ 2 ∧ 1 ≤ j ∧ j ≤ N`. Simplify `hj` using `[Finset.mem_erase, Finset.mem_Icc]`. Distinguish the cases in `hj1 : j = 1`. Substitute `hj1` using the available equality. Rewrite using `[D.al_one c hgood b, map_zero, zero_mul]`.

Conclude with `HasWt.zero`. Establish `hj3 : 3 ≤ j` using `by omega`. Use `HasWt.mono ?_ (HasWt.C_mul (D.al_good c hgood j b (by omega)) (HasWt.pow ht' (D.l ^ j)))` and prove the remaining obligations. Use `num_c hl hj3` as an intermediate fact. Unfold `top`.

Use `push_cast`. Conclude with `this`. Establish `ht' : D.Wt D.top (t c)`. Use `ht c` as an intermediate fact. Rewrite `this` using `[mu, if_neg hcJ, sub_zero]`. Then use the resulting hypothesis.

Rewrite using `[main, if_neg (fun h => hcJ h.1), add_zero]`. Apply `HasWt.sum` to reduce the goal to its premises. Introduce `j hj`. Establish `hj' : 1 ≤ j ∧ j ≤ N` using `by simpa [Finset.mem_Icc] using hj`. Distinguish the cases in `hg : D.good c`.

Distinguish the cases in `hj1 : j = 1`. Substitute `hj1` using the available equality. Rewrite using `[D.al_one c hg b, map_zero, zero_mul]`. Conclude with `HasWt.zero`. Use `HasWt.mono ?_ (HasWt.C_mul (D.al_good c hg j b (by omega)) (HasWt.pow ht' (D.l ^ j)))` and prove the remaining obligations.

Use `num_good hl (j := j) (by omega)` as an intermediate fact. Unfold `top`. Use `push_cast`. Conclude with `this`. Use `HasWt.mono ?_ (HasWt.C_mul (D.al_all c j b) (HasWt.pow ht' (D.l ^ j)))` and prove the remaining obligations.

Use `num_d hl (j := j) hj'.1` as an intermediate fact. Unfold `top`. Use `push_cast`. Conclude with `this`.
-/
theorem wt_contrib (J : ℕ) (hJK : J ≤ D.K) (t : C → MvPowerSeries Z k)
    (ht : ∀ c, D.Wt D.top (t c - D.mu J c)) (N : ℕ) (hN : 2 ≤ N) (c b : C) :
    D.Wt D.top
      (∑ j ∈ Finset.Icc 1 N, MvPowerSeries.C (D.al c j b) * t c ^ (D.l ^ j) + D.main J c b) := by
  have hl := D.l_ge
  by_cases hcJ : D.lev c < J
  · have hcK : D.lev c < D.K := by omega
    have hgood := D.pure_good c hcK
    have hν : D.Wt D.top (t c - D.m (D.lev c) c) := by
      have := ht c
      rwa [mu, if_pos hcJ] at this
    have ht' : D.Wt (rho D.l) (t c) := by
      have h1 := HasWt.add (D.wt_m_rho (D.lev c) c) (HasWt.mono D.rho_le_top hν)
      rwa [add_sub_cancel] at h1
    have h2mem : 2 ∈ Finset.Icc 1 N := Finset.mem_Icc.2 ⟨by norm_num, hN⟩
    rw [← Finset.add_sum_erase _ _ h2mem, add_right_comm]
    refine HasWt.add (D.wt_two J hJK c b hcJ (t c) hν) ?_
    apply HasWt.sum
    intro j hj
    have hj' : j ≠ 2 ∧ 1 ≤ j ∧ j ≤ N := by
      simpa [Finset.mem_erase, Finset.mem_Icc] using hj
    by_cases hj1 : j = 1
    · subst hj1
      rw [D.al_one c hgood b, map_zero, zero_mul]
      exact HasWt.zero
    · have hj3 : 3 ≤ j := by omega
      refine HasWt.mono ?_ (HasWt.C_mul (D.al_good c hgood j b (by omega))
        (HasWt.pow ht' (D.l ^ j)))
      have := num_c hl hj3
      unfold top
      push_cast
      exact this
  · have ht' : D.Wt D.top (t c) := by
      have := ht c
      rwa [mu, if_neg hcJ, sub_zero] at this
    rw [main, if_neg (fun h => hcJ h.1), add_zero]
    apply HasWt.sum
    intro j hj
    have hj' : 1 ≤ j ∧ j ≤ N := by simpa [Finset.mem_Icc] using hj
    by_cases hg : D.good c
    · by_cases hj1 : j = 1
      · subst hj1
        rw [D.al_one c hg b, map_zero, zero_mul]
        exact HasWt.zero
      · refine HasWt.mono ?_ (HasWt.C_mul (D.al_good c hg j b (by omega))
          (HasWt.pow ht' (D.l ^ j)))
        have := num_good hl (j := j) (by omega)
        unfold top
        push_cast
        exact this
    · refine HasWt.mono ?_ (HasWt.C_mul (D.al_all c j b) (HasWt.pow ht' (D.l ^ j)))
      have := num_d hl (j := j) hj'.1
      unfold top
      push_cast
      exact this

/- English proof (translation)
Rewrite `ht`, the goal using `[inWTo_iff]`. Introduce `b A`. Establish `h1 : coeff A (D.Psi t b - D.mu (min (J + 1) D.K) b) = coeff A (D.PsiPartial (max A.degree 2) t b - D.mu (min (J + 1) D.K) b)`. Rewrite using `[map_sub, map_sub, D.opIsLimit t hnc b A _ (le_max_left _ _)]`. Rewrite using `[h1]`.

Establish `h2 : D.PsiPartial (max A.degree 2) t b - D.mu (min (J + 1) D.K) b = -∑ c, (∑ j ∈ Finset.Icc 1 (max A.degree 2), MvPowerSeries.C (D.al c j b) * t c ^ (D.l ^ j) + D.main J c b)`. Rewrite using `[D.mu_succ J hJ1 hJK b, PsiPartial, Finset.sum_add_distrib]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2]`. Conclude with `(HasWt.neg (HasWt.sum _ fun c _ => D.wt_contrib J hJK t ht _ (le_max_right _ _) c b)) A`.
-/
theorem step (J : ℕ) (hJ1 : 1 ≤ J) (hJK : J ≤ D.K) (t : C → MvPowerSeries Z k)
    (hnc : NoConst t) (ht : D.InWTo J t) : D.InWTo (min (J + 1) D.K) (D.Psi t) := by
  rw [inWTo_iff] at ht ⊢
  intro b A
  have h1 : coeff A (D.Psi t b - D.mu (min (J + 1) D.K) b) =
      coeff A (D.PsiPartial (max A.degree 2) t b - D.mu (min (J + 1) D.K) b) := by
    rw [map_sub, map_sub, D.opIsLimit t hnc b A _ (le_max_left _ _)]
  rw [h1]
  have h2 : D.PsiPartial (max A.degree 2) t b - D.mu (min (J + 1) D.K) b =
      -∑ c, (∑ j ∈ Finset.Icc 1 (max A.degree 2),
        MvPowerSeries.C (D.al c j b) * t c ^ (D.l ^ j) + D.main J c b) := by
    rw [D.mu_succ J hJ1 hJK b, PsiPartial, Finset.sum_add_distrib]
    ring
  rw [h2]
  exact (HasWt.neg (HasWt.sum _ fun c _ =>
    D.wt_contrib J hJK t ht _ (le_max_right _ _) c b)) A

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `c`. Unfold `start`. Use `split_ifs with h`. Conclude with `D.ord_m h c`.

Conclude with `OrdGE.zero`. Introduce `c hc`. Unfold `start`. Rewrite using `[if_pos hc, sub_self]`. Conclude with `HasWt.zero`.

Introduce `c hc`. Unfold `start`. Rewrite using `[if_neg (not_lt.2 hc)]`. Conclude with `HasWt.zero`.
-/
theorem start_in_W_holds : D.StartInW := by
  refine ⟨?_, ?_, ?_⟩
  · intro c
    unfold start
    split_ifs with h
    · exact D.ord_m h c
    · exact OrdGE.zero
  · intro c hc
    unfold start
    rw [if_pos hc, sub_self]
    exact HasWt.zero
  · intro c hc
    unfold start
    rw [if_neg (not_lt.2 hc)]
    exact HasWt.zero

/- English proof (translation)
Introduce `t hnc hW`. Use `⟨D.noConst_Psi t, ?_⟩` and prove the remaining obligations. Establish `h` using `D.step D.K D.K_pos le_rfl t hnc hW`. Rewrite `h` using `[min_eq_right (by omega)]`. Then use the resulting hypothesis.
-/
theorem psi_in_W_holds : D.PsiW := by
  intro t hnc hW
  refine ⟨D.noConst_Psi t, ?_⟩
  have h := D.step D.K D.K_pos le_rfl t hnc hW
  rwa [min_eq_right (by omega)] at h

/- English proof (translation)
Introduce `t hnc hfix`. Establish `hit : ∀ n, NoConst ((D.Psi)^[n] D.start) ∧ D.InW ((D.Psi)^[n] D.start)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => exact D.start_in_W_holds`.

Consider the case `succ n ih`. Rewrite using `[Function.iterate_succ_apply']`. Conclude with `D.psi_in_W_holds _ ih.1 ih.2`. Unfold `InW`. Rewrite using `[inWTo_iff]`.

Introduce `c A`. Establish `h` using `(D.inWTo_iff _ _).1 (hit A.degree).2 c A`. Establish `hc` using `D.hasUniqueFixedPoint.2 D.start t D.start_in_W_holds.1 hnc hfix A.degree A le_rfl c`. Rewrite `h`, the goal using `[map_sub]`. Rewrite using `[← hc]`.

Conclude with `h`.
-/
theorem chainII_holds : D.ChainII := by
  intro t hnc hfix
  have hit : ∀ n, NoConst ((D.Psi)^[n] D.start) ∧ D.InW ((D.Psi)^[n] D.start) := by
    intro n
    induction n with
    | zero => exact D.start_in_W_holds
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact D.psi_in_W_holds _ ih.1 ih.2
  unfold InW
  rw [inWTo_iff]
  intro c A
  have h := (D.inWTo_iff _ _).1 (hit A.degree).2 c A
  have hc := D.hasUniqueFixedPoint.2 D.start t D.start_in_W_holds.1 hnc hfix A.degree A le_rfl c
  rw [map_sub] at h ⊢
  rw [← hc]
  exact h

/- English proof (translation)
Establish `h1 : D.InWTo 1 D.zvec`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `c hc`. Establish `: D.lev c = 0` using `by omega`. Rewrite using `[this]`.

Use `show D.Wt D.top (D.zvec c - D.zvec c)`. Rewrite using `[sub_self]`. Conclude with `HasWt.zero`. Introduce `c hc`. Rewrite using `[D.zvec_eq_zero (by omega)]`.

Conclude with `HasWt.zero`. Use `⟨h1, fun J t hJ1 hJK hnc ht => D.step J hJ1 hJK t hnc ht, ?_⟩` and prove the remaining obligations. Establish `hK` using `D.K_pos`. Establish `hit : ∀ n, D.InWTo (min (n + 1) D.K) ((D.Psi)^[n] D.zvec)`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero`. Rewrite using `[min_eq_left (by omega)]`. Conclude with `h1`. Consider the case `succ n ih`.

Rewrite using `[Function.iterate_succ_apply']`. Establish `h2` using `D.step _ (by omega) (min_le_right _ _) _ (D.noConst_iterate D.noConst_zvec n) ih`. Establish `h3 : min (min (n + 1) D.K + 1) D.K = min (n + 1 + 1) D.K` using `by omega`. Rewrite `h2` using `[h3]`. Then use the resulting hypothesis. Introduce `n hn`.

Establish `h2` using `hit n`. Rewrite `h2` using `[min_eq_right (by omega)]`. Then use the resulting hypothesis.
-/
theorem second_way_holds : D.SecondWay := by
  have h1 : D.InWTo 1 D.zvec := by
    refine ⟨?_, ?_⟩
    · intro c hc
      have : D.lev c = 0 := by omega
      rw [this]
      show D.Wt D.top (D.zvec c - D.zvec c)
      rw [sub_self]
      exact HasWt.zero
    · intro c hc
      rw [D.zvec_eq_zero (by omega)]
      exact HasWt.zero
  refine ⟨h1, fun J t hJ1 hJK hnc ht => D.step J hJ1 hJK t hnc ht, ?_⟩
  have hK := D.K_pos
  have hit : ∀ n, D.InWTo (min (n + 1) D.K) ((D.Psi)^[n] D.zvec) := by
    intro n
    induction n with
    | zero =>
      rw [min_eq_left (by omega)]
      exact h1
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      have h2 := D.step _ (by omega) (min_le_right _ _) _ (D.noConst_iterate D.noConst_zvec n) ih
      have h3 : min (min (n + 1) D.K + 1) D.K = min (n + 1 + 1) D.K := by omega
      rwa [h3] at h2
  intro n hn
  have h2 := hit n
  rwa [min_eq_right (by omega)] at h2

end Data

end

end Formalism.BaseCaseIdentities
