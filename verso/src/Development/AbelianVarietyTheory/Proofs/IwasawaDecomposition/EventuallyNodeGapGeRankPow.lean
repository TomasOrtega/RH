import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top Filter

namespace GlobalTheory.Mem.Top.NodeGap

/- English proof (translation)
Establish `h1 : (R.k : ℝ) ≤ 2 * s.x ^ (9 / 2 + 10 * s.eps)` using `h.2.2.1.2`. Establish `h2 : s.x ^ (9 / 2 + 10 * s.eps) ≤ s.x ^ 5`. Rewrite using `[← Real.rpow_natCast]`. Conclude with `Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le (by have := s.eps_lt; push_cast; linarith)`. Establish `h3 : R.r ≤ 2 * R.k` using `by have := R.m_add_three_le_k; unfold Ranks.r; omega`.

Establish `h4 : (R.r : ℝ) ≤ 2 * R.k` using `by exact_mod_cast h3`. Establish `h5 : (0 : ℝ) < s.x ^ 5` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem rank_le {s : Scale} {R : Ranks} (h : RankVal s R) (hx : 4 ≤ s.x) : (R.r : ℝ) ≤ s.x ^ 6 := by
  have h1 : (R.k : ℝ) ≤ 2 * s.x ^ (9 / 2 + 10 * s.eps) := h.2.2.1.2
  have h2 : s.x ^ (9 / 2 + 10 * s.eps) ≤ s.x ^ 5 := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le (by have := s.eps_lt; push_cast; linarith)
  have h3 : R.r ≤ 2 * R.k := by have := R.m_add_three_le_k; unfold Ranks.r; omega
  have h4 : (R.r : ℝ) ≤ 2 * R.k := by exact_mod_cast h3
  have h5 : (0 : ℝ) < s.x ^ 5 := by positivity
  calc (R.r : ℝ) ≤ 4 * s.x ^ 5 := by linarith
    _ ≤ s.x * s.x ^ 5 := by gcongr
    _ = s.x ^ 6 := by ring

/- English proof (translation)
Establish `h1 : Real.sqrt (s.x * s.delta1) ≤ (R.m : ℝ)` using `h.2.1.1`. Establish `hx0 : 0 < s.x` using `by linarith [s.one_lt_alt]`. Establish `h2 : (M : ℝ) ^ 2 ≤ s.x * s.delta1`. Establish `e : s.x * s.delta1 = s.x ^ (1 - s.eps / 8)`. Unfold `Scale.delta1`.

Rewrite using `[sub_eq_add_neg, Real.rpow_add hx0, Real.rpow_one]`. Establish `h3 : s.x ^ ((1 : ℝ) / 2) ≤ s.x ^ (1 - s.eps / 8)` using `Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le (by have := s.eps_lt; linarith)`. Rewrite using `[e]`. Use `le_trans ?_ h3` and prove the remaining obligations. Rewrite using `[← Real.sqrt_eq_rpow]`.

Conclude with `Real.le_sqrt_of_sq_le (by rw [← pow_mul]; exact hx)`. Establish `h4 : (M : ℝ) ≤ R.m` using `(Real.le_sqrt_of_sq_le h2).trans h1`. Conclude with `h4` after adjusting the coercions.
-/
theorem le_m {s : Scale} {R : Ranks} (h : RankVal s R) {M : ℕ} (hx : (M : ℝ) ^ 4 ≤ s.x) : M ≤ R.m := by
  have h1 : Real.sqrt (s.x * s.delta1) ≤ (R.m : ℝ) := h.2.1.1
  have hx0 : 0 < s.x := by linarith [s.one_lt_alt]
  have h2 : (M : ℝ) ^ 2 ≤ s.x * s.delta1 := by
    have e : s.x * s.delta1 = s.x ^ (1 - s.eps / 8) := by
      unfold Scale.delta1
      rw [sub_eq_add_neg, Real.rpow_add hx0, Real.rpow_one]
    have h3 : s.x ^ ((1 : ℝ) / 2) ≤ s.x ^ (1 - s.eps / 8) :=
      Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le (by have := s.eps_lt; linarith)
    rw [e]
    refine le_trans ?_ h3
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le (by rw [← pow_mul]; exact hx)
  have h4 : (M : ℝ) ≤ R.m := (Real.le_sqrt_of_sq_le h2).trans h1
  exact_mod_cast h4

/- English proof (translation)
Take `⟨b1, h, -⟩` from `(K.ok.hc u).2.2.1`. Conclude with `⟨b1 τ, h τ⟩`.
-/
theorem b_eq (K : Ctx) (u : K.P.Word) (τ : Tau K.P.R) :
    ∃ b1 : ℤ, ∀ j : Fin K.P.R.m, (K.P.hcW u τ).b j = (b1 : ℚ) + (j.1 : ℚ) * (h0v K.s K.ch : ℚ) ∧
      (K.P.hcW u τ).e j = (K.P.hcW u τ).b j + (h0v K.s K.ch : ℚ) / 2 := by
  obtain ⟨b1, h, -⟩ := (K.ok.hc u).2.2.1
  exact ⟨b1 τ, h τ⟩

/- English proof (translation)
Use `⟨1, one_pos, fun eps C8 _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C _ _ _ => ⟨0, fun cD _ => ⟨6 * N + 1, fun ch hch => ⟨max (max 4 A) ((M : ℝ) ^ 4), fun K _ _ h3 _ hx => ?_⟩⟩⟩⟩⟩` and prove the remaining obligations. Simplify using `only [max_le_iff] at hx`. Take `⟨⟨hx4, hxA⟩, hxM⟩` from `hx`. Use `⟨le_m K.ok.rank hxM, ?_⟩` and prove the remaining obligations. Establish `h1` using `rank_le K.ok.rank hx4`.

Establish `h2 : K.s.x ^ (6 * N + 1) ≤ K.s.x ^ K.ch`. Rewrite using `[← Real.rpow_natCast]`. Conclude with `Real.rpow_le_rpow_of_exponent_le K.s.one_lt_alt.le (by rw [h3]; push_cast; exact hch)`. Establish `h5 : K.s.x ^ K.ch ≤ (⌈K.s.x ^ K.ch⌉₊ : ℝ)` using `Nat.le_ceil _`. Establish `h6 : (0 : ℝ) ≤ (⌈K.s.x ^ K.ch⌉₊ : ℝ)` using `Nat.cast_nonneg _`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem eventually_nodeGap_ge_rank_pow (A : ℝ) (N M : ℕ) : Ev fun K => M ≤ K.P.R.m ∧ A * (K.P.R.r : ℝ) ^ N ≤ (h0v K.s K.ch : ℝ) := by
  refine ⟨1, one_pos, fun eps C8 _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C _ _ _ => ⟨0, fun cD _ => ⟨6 * N + 1, fun ch hch =>
    ⟨max (max 4 A) ((M : ℝ) ^ 4), fun K _ _ h3 _ hx => ?_⟩⟩⟩⟩⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hx4, hxA⟩, hxM⟩ := hx
  refine ⟨le_m K.ok.rank hxM, ?_⟩
  have h1 := rank_le K.ok.rank hx4
  have h2 : K.s.x ^ (6 * N + 1) ≤ K.s.x ^ K.ch := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le K.s.one_lt_alt.le (by rw [h3]; push_cast; exact hch)
  have h5 : K.s.x ^ K.ch ≤ (⌈K.s.x ^ K.ch⌉₊ : ℝ) := Nat.le_ceil _
  have h6 : (0 : ℝ) ≤ (⌈K.s.x ^ K.ch⌉₊ : ℝ) := Nat.cast_nonneg _
  calc A * (K.P.R.r : ℝ) ^ N ≤ K.s.x * (K.s.x ^ 6) ^ N := by gcongr
    _ = K.s.x ^ (6 * N + 1) := by ring
    _ ≤ (h0v K.s K.ch : ℝ) := by unfold h0v; push_cast; linarith

/- English proof (translation)
Take `⟨a, ha, hp⟩` from `eventually_nodeGap_ge_rank_pow A N M`. Use `⟨a, ha, fun e C8 he hle h52 h8 => ?_⟩` and prove the remaining obligations. Take `⟨K0, hK⟩` from `hp e C8 he hle h52 h8`. Use `⟨K0, fun C hC hC8 hL => ?_⟩` and prove the remaining obligations. Take `⟨a1, ha1⟩` from `hK C hC hC8 hL`.

Use `⟨a1, fun cD hcD => ?_⟩` and prove the remaining obligations. Take `⟨a2, ha2⟩` from `ha1 cD hcD`. Use `⟨a2, fun ch hch => ?_⟩` and prove the remaining obligations. Take `⟨a3, ha3⟩` from `ha2 ch hch`. Use `⟨a3, fun K h1 h2 h3 h4 hx X hO => ?_⟩` and prove the remaining obligations.

Take `⟨g1, g2⟩` from `ha3 K h1 h2 h3 h4 hx`. Establish `key : ∀ B : Pre, K.Over B → M ≤ B.R.m ∧ ∃ h : ℕ, A * (B.R.r : ℝ) ^ N ≤ (h : ℝ) ∧ ∀ τ, ∃ b1 : ℤ, ∀ j : Fin B.R.m, (B.hc τ).b j = (b1 : ℚ) + (j.1 : ℚ) * (h : ℚ) ∧ (B.hc τ).e j = (B.hc τ).b j + (h : ℚ) / 2`. Introduce and unpack `B ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩`. Conclude with `⟨g1, _, g2, fun τ => b_eq K K.P.u₀ τ⟩`. Conclude with `key _ hO`.
-/
theorem ev_nodes (A : ℝ) (N M : ℕ) : Ev fun K => ∀ X : Stages, K.Over X.B.toPre → M ≤ X.toD7.R.m ∧
    ∃ h : ℕ, A * (X.toD7.R.r : ℝ) ^ N ≤ (h : ℝ) ∧ ∀ τ, ∃ b1 : ℤ, ∀ j : Fin X.toD7.R.m,
      (X.toD7.hc τ).b j = (b1 : ℚ) + (j.1 : ℚ) * (h : ℚ) ∧ (X.toD7.hc τ).e j = (X.toD7.hc τ).b j + (h : ℚ) / 2 := by
  obtain ⟨a, ha, hp⟩ := eventually_nodeGap_ge_rank_pow A N M
  refine ⟨a, ha, fun e C8 he hle h52 h8 => ?_⟩
  obtain ⟨K0, hK⟩ := hp e C8 he hle h52 h8
  refine ⟨K0, fun C hC hC8 hL => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 hL
  refine ⟨a1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD hcD
  refine ⟨a2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch hch
  refine ⟨a3, fun K h1 h2 h3 h4 hx X hO => ?_⟩
  obtain ⟨g1, g2⟩ := ha3 K h1 h2 h3 h4 hx
  have key : ∀ B : Pre, K.Over B → M ≤ B.R.m ∧
      ∃ h : ℕ, A * (B.R.r : ℝ) ^ N ≤ (h : ℝ) ∧ ∀ τ, ∃ b1 : ℤ, ∀ j : Fin B.R.m,
        (B.hc τ).b j = (b1 : ℚ) + (j.1 : ℚ) * (h : ℚ) ∧ (B.hc τ).e j = (B.hc τ).b j + (h : ℚ) / 2 := by
    rintro B ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩
    exact ⟨g1, _, g2, fun τ => b_eq K K.P.u₀ τ⟩
  exact key _ hO

end GlobalTheory.Mem.Top.NodeGap
