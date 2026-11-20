import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScalePolynomialQuantitiesComparisonStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScaleStatement

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

/- English proof (translation)
Establish `hPb : P ≤ b'` using `by nlinarith`. Establish `hb'0 : 0 < b'` using `by linarith`. Establish `hb0 : 0 < b` using `lt_of_lt_of_le (by positivity) h2`. Establish `hm0 : 0 < m` using `by linarith`. Establish `e1 : b / (m * b / Λ) = Λ / m` using `by field_simp`.

Establish `e2 : 8 * b / (m * b / Λ) = 8 * (Λ / m)` using `by field_simp`. Establish `h3 : Λ / m ≤ P` using `(div_le_self hΛ0.le hm).trans hΛ`. Establish `h4 : 100 * b' ≤ m * b / Λ`. Rewrite using `[le_div_iff₀ hΛ0]`. Establish `a1 : 100 * Λ ≤ P ^ 2` using `by nlinarith`.

Establish `a2 : b' * (100 * Λ) ≤ b' * P ^ 2` using `mul_le_mul_of_nonneg_left a1 hb'0.le`. Establish `a3 : b ≤ m * b` using `le_mul_of_one_le_left hb0.le hm`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[e1, e2]`. Apply the tactic sequence `constructor <;> linarith`.
-/
theorem lstar_ineqs_of_le (m b b' Λ S η t P : ℝ) (hm : 1 ≤ m) (hΛ0 : 0 < Λ) (hΛ : Λ ≤ P) (hS : S ≤ P)
    (hη : η ≤ P) (ht : t ≤ P) (hP : 100 ≤ P) (h1 : P ^ 2 ≤ b') (h2 : b' * P ^ 2 ≤ b) :
    b' + S + η + b / (m * b / Λ) < m * b / Λ ∧ 2 * η + t + 8 * b / (m * b / Λ) + 7 < m * b / Λ := by
  have hPb : P ≤ b' := by nlinarith
  have hb'0 : 0 < b' := by linarith
  have hb0 : 0 < b := lt_of_lt_of_le (by positivity) h2
  have hm0 : 0 < m := by linarith
  have e1 : b / (m * b / Λ) = Λ / m := by field_simp
  have e2 : 8 * b / (m * b / Λ) = 8 * (Λ / m) := by field_simp
  have h3 : Λ / m ≤ P := (div_le_self hΛ0.le hm).trans hΛ
  have h4 : 100 * b' ≤ m * b / Λ := by
    rw [le_div_iff₀ hΛ0]
    have a1 : 100 * Λ ≤ P ^ 2 := by nlinarith
    have a2 : b' * (100 * Λ) ≤ b' * P ^ 2 := mul_le_mul_of_nonneg_left a1 hb'0.le
    have a3 : b ≤ m * b := le_mul_of_one_le_left hb0.le hm
    nlinarith
  rw [e1, e2]
  constructor <;> linarith

/- English proof (translation)
Establish `Q1 : 1 ≤ Q` using `by linarith`. Establish `Q0 : 0 ≤ Q` using `by linarith`. Establish `p1 : Q ≤ Q ^ 6` using `le_self_pow₀ Q1 (by norm_num)`. Establish `p2 : Q ^ 2 ≤ Q ^ 6` using `pow_le_pow_right₀ Q1 (by norm_num)`. Establish `p4 : Q ^ 4 ≤ Q ^ 6` using `pow_le_pow_right₀ Q1 (by norm_num)`.

Establish `p5 : Q ^ 5 ≤ Q ^ 6` using `pow_le_pow_right₀ Q1 (by norm_num)`. Establish `p7 : 100 * Q ^ 6 ≤ Q ^ 7`. Rewrite using `[show Q ^ 7 = Q * Q ^ 6 by ring]; gcongr`. Establish `a1 : n * t ^ 2 * (N + t) * l ^ 2 ≤ Q * Q ^ 2 * (Q + Q) * Q ^ 2` using `by gcongr`. Establish `a2 : k * n ^ 2 * (k * (4 * Δ) + t + l) ≤ Q * Q ^ 2 * (Q * (4 * (2 * Q)) + Q + Q)` using `by gcongr`.

Establish `a3 : k * (4 * Δ) ≤ Q * (4 * (2 * Q))` using `by gcongr`. Establish `a4 : m * h ≤ Q * (4 * Q)` using `by gcongr`. Establish `e1 : Q * Q ^ 2 * (Q + Q) * Q ^ 2 = 2 * Q ^ 6` using `by ring`. Establish `e2 : Q * Q ^ 2 * (Q * (4 * (2 * Q)) + Q + Q) = 8 * Q ^ 5 + 2 * Q ^ 4` using `by ring`. Establish `e3 : Q * (4 * (2 * Q)) = 8 * Q ^ 2` using `by ring`.

Establish `e4 : Q * (4 * Q) = 4 * Q ^ 2` using `by ring`. Apply the tactic sequence `refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith`.
-/
theorem lstar_den_le (n t N l k m Δ h Q : ℝ) (hQ : 100 ≤ Q) (n0 : 0 ≤ n) (t0 : 0 ≤ t) (N0 : 0 ≤ N) (l0 : 0 ≤ l)
    (k0 : 0 ≤ k) (m0 : 0 ≤ m) (Δ0 : 0 ≤ Δ) (h0 : 0 ≤ h) (hn : n ≤ Q) (ht : t ≤ Q) (hN : N ≤ Q) (hl : l ≤ Q)
    (hk : k ≤ Q) (hm : m ≤ Q) (hΔ : Δ ≤ 2 * Q) (hh : h ≤ 4 * Q) :
    n * t ^ 2 * (N + t) * l ^ 2 + k * n ^ 2 * (k * (4 * Δ) + t + l) ≤ Q ^ 7 ∧ k * (4 * Δ) ≤ Q ^ 7 ∧
      m * h ≤ Q ^ 7 ∧ t ≤ Q ^ 7 ∧ 100 ≤ Q ^ 7 := by
  have Q1 : 1 ≤ Q := by linarith
  have Q0 : 0 ≤ Q := by linarith
  have p1 : Q ≤ Q ^ 6 := le_self_pow₀ Q1 (by norm_num)
  have p2 : Q ^ 2 ≤ Q ^ 6 := pow_le_pow_right₀ Q1 (by norm_num)
  have p4 : Q ^ 4 ≤ Q ^ 6 := pow_le_pow_right₀ Q1 (by norm_num)
  have p5 : Q ^ 5 ≤ Q ^ 6 := pow_le_pow_right₀ Q1 (by norm_num)
  have p7 : 100 * Q ^ 6 ≤ Q ^ 7 := by
    rw [show Q ^ 7 = Q * Q ^ 6 by ring]; gcongr
  have a1 : n * t ^ 2 * (N + t) * l ^ 2 ≤ Q * Q ^ 2 * (Q + Q) * Q ^ 2 := by gcongr
  have a2 : k * n ^ 2 * (k * (4 * Δ) + t + l) ≤ Q * Q ^ 2 * (Q * (4 * (2 * Q)) + Q + Q) := by gcongr
  have a3 : k * (4 * Δ) ≤ Q * (4 * (2 * Q)) := by gcongr
  have a4 : m * h ≤ Q * (4 * Q) := by gcongr
  have e1 : Q * Q ^ 2 * (Q + Q) * Q ^ 2 = 2 * Q ^ 6 := by ring
  have e2 : Q * Q ^ 2 * (Q * (4 * (2 * Q)) + Q + Q) = 8 * Q ^ 5 + 2 * Q ^ 4 := by ring
  have e3 : Q * (4 * (2 * Q)) = 8 * Q ^ 2 := by ring
  have e4 : Q * (4 * Q) = 4 * Q ^ 2 := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/- English proof (translation)
Introduce `eps he0 he1 C _`. Use `⟨0, fun cD hcD => ⟨0, fun ch hch => ?_⟩⟩` and prove the remaining obligations. Establish `hcD' : 0 ≤ cD` using `hcD`. Establish `hch' : 0 ≤ ch` using `hch`. Take `⟨x1, h1⟩` from `GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he0 he1`.

Take `⟨x2, h2⟩` from `GlobalTheory.T.scale_polynomial_quantities_comparison eps ((cD + ch + 402) * 14) 1 he0 one_pos`. Use `⟨max 100 (max x1 x2), fun D L hL hx hV => ?_⟩` and prove the remaining obligations. Establish `hx0 : 100 ≤ L.sc.x` using `(le_max_left _ _).trans hx`. Establish `hx1 : x1 ≤ L.sc.x` using `((le_max_left _ _).trans (le_max_right _ _)).trans hx`. Establish `hx2 : x2 ≤ L.sc.x` using `((le_max_right _ _).trans (le_max_right _ _)).trans hx`.

Take `⟨hf, hm, hr, hkr, -, hl, hl1, -, -, -, -, -, -, ht, hN, -, -⟩` from `h1 L.sc D.R hL hx1 hV.ranks`. Take `⟨-, -, -, hb1, hb2, -, -⟩` from `h2 L.sc hL hx2`. Establish `x1le : 1 ≤ L.sc.x` using `by linarith`. Use `set Q : ℝ := L.sc.x ^ (cD + ch + 402) with hQ`. Establish `hpow : ∀ c : ℝ, c ≤ cD + ch + 402 → L.sc.x ^ c ≤ Q` using `fun c hc => Real.rpow_le_rpow_of_exponent_le x1le hc`.

Establish `hxQ : L.sc.x ≤ Q`. Use `hpow 1 (by linarith); rwa [Real.rpow_one] at this` as an intermediate fact. Establish `hQ14 : L.sc.x ^ ((cD + ch + 402) * 14) = (Q ^ 7) ^ 2`. Rewrite using `[Real.rpow_mul (by linarith), ← pow_mul, ← hQ]`. Conclude with `Real.rpow_natCast Q 14` after adjusting the coercions.

Rewrite `hb1`, `hb2` using `[hQ14]`. Rewrite `hb2` using `[sub_self, Real.rpow_zero, one_mul]`. Establish `hQ100 : 100 ≤ Q` using `hx0.trans hxQ`. Establish `hnQ : (D.R.n : ℝ) ≤ Q`. Establish `a : (D.R.n : ℝ) ≤ D.R.f`.

Establish `: D.R.n ≤ D.R.f` using `by unfold Ranks.f; omega`. Conclude with `this` after adjusting the coercions. Conclude with `a.trans (hf.trans (hpow 3 (by linarith)))`. Establish `hkQ : (D.R.k : ℝ) ≤ Q`. Establish `a : (D.R.k : ℝ) ≤ D.R.r` using `by exact_mod_cast hkr`.

Conclude with `a.trans (hr.trans (hpow 5 (by linarith)))`. Establish `htQ : (D.R.t : ℝ) ≤ Q` using `ht.trans (hpow 401 (by linarith))`. Establish `hNQ : (D.R.N D.R.m : ℝ) ≤ Q` using `hN.trans (hpow 402 (by linarith))`. Establish `hΔ : (Delv L.sc cD : ℝ) ≤ 2 * Q`. Establish `a` using `Nat.ceil_lt_add_one (a := L.sc.x ^ cD) (by positivity)`.

Establish `b` using `hpow cD (by linarith)`. Unfold `Delv`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hh : (h0v L.sc ch : ℝ) ≤ 4 * Q`. Establish `a` using `Nat.ceil_lt_add_one (a := L.sc.x ^ ch) (by positivity)`.

Establish `b` using `hpow ch (by linarith)`. Unfold `h0v`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hSc : L.Sc = (D.R.k : ℝ) * (4 * (Delv L.sc cD : ℝ))`.

Rewrite using `[L.Sc_eq, hV.Del_eq]`. Use `push_cast`. Both sides reduce to the same expression. Take `⟨c1, c2, c3, c4, c5⟩` from `lstar_den_le (D.R.n : ℝ) D.R.t (D.R.N D.R.m) L.sc.L D.R.k D.R.m (Delv L.sc cD) (h0v L.sc ch) Q hQ100 (by positivity) (by positivity) (by positivity) (by linarith) (by positivity) (by positivity) (by positivity) (by positivity) hnQ htQ hNQ (hl.trans hxQ) hkQ (hm.trans hxQ) hΔ hh`. Rewrite `c1`, `c2` using `[← hSc]`.

Rewrite `c3` using `[← hV.eta_eq]`. Establish `hm1 : (1 : ℝ) ≤ D.R.m`. Use `D.R.two_le_m` as an intermediate fact. Conclude with `(by omega : 1 ≤ D.R.m)` after adjusting the coercions. Establish `hn0 : (0 : ℝ) < D.R.n` using `by unfold Ranks.n; positivity`.

Establish `ht0 : (0 : ℝ) < D.R.t`. Use `D.R.three_m_lt_t` as an intermediate fact. Conclude with `(by omega : 0 < D.R.t)` after adjusting the coercions. Establish `hl0 : 0 < L.sc.L` using `by linarith`. Establish `hSc0 : 0 ≤ L.Sc` using `by rw [hSc]; positivity`.

Unfold `lStar`. Conclude with `lstar_ineqs_of_le _ _ _ _ _ _ _ (Q ^ 7) hm1 (by positivity) c1 c2 c3 c4 c5 hb2 hb1`.
-/
theorem szRow_lStar : SzRow (fun _ D L => (L.sc.b' + L.Sc + L.etaSz + L.sc.b / lStar L < lStar L) ∧
    (2 * L.etaSz + D.R.t + 8 * L.sc.b / lStar L + 7 < lStar L)) := by
  intro eps he0 he1 C _
  refine ⟨0, fun cD hcD => ⟨0, fun ch hch => ?_⟩⟩
  have hcD' : 0 ≤ cD := hcD
  have hch' : 0 ≤ ch := hch
  obtain ⟨x1, h1⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he0 he1
  obtain ⟨x2, h2⟩ := GlobalTheory.T.scale_polynomial_quantities_comparison eps ((cD + ch + 402) * 14) 1 he0 one_pos
  refine ⟨max 100 (max x1 x2), fun D L hL hx hV => ?_⟩
  have hx0 : 100 ≤ L.sc.x := (le_max_left _ _).trans hx
  have hx1 : x1 ≤ L.sc.x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hx2 : x2 ≤ L.sc.x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  obtain ⟨hf, hm, hr, hkr, -, hl, hl1, -, -, -, -, -, -, ht, hN, -, -⟩ := h1 L.sc D.R hL hx1 hV.ranks
  obtain ⟨-, -, -, hb1, hb2, -, -⟩ := h2 L.sc hL hx2
  have x1le : 1 ≤ L.sc.x := by linarith
  set Q : ℝ := L.sc.x ^ (cD + ch + 402) with hQ
  have hpow : ∀ c : ℝ, c ≤ cD + ch + 402 → L.sc.x ^ c ≤ Q := fun c hc =>
    Real.rpow_le_rpow_of_exponent_le x1le hc
  have hxQ : L.sc.x ≤ Q := by
    have := hpow 1 (by linarith); rwa [Real.rpow_one] at this
  have hQ14 : L.sc.x ^ ((cD + ch + 402) * 14) = (Q ^ 7) ^ 2 := by
    rw [Real.rpow_mul (by linarith), ← pow_mul, ← hQ]
    exact_mod_cast Real.rpow_natCast Q 14
  rw [hQ14] at hb1 hb2
  rw [sub_self, Real.rpow_zero, one_mul] at hb2
  have hQ100 : 100 ≤ Q := hx0.trans hxQ
  have hnQ : (D.R.n : ℝ) ≤ Q := by
    have a : (D.R.n : ℝ) ≤ D.R.f := by
      have : D.R.n ≤ D.R.f := by unfold Ranks.f; omega
      exact_mod_cast this
    exact a.trans (hf.trans (hpow 3 (by linarith)))
  have hkQ : (D.R.k : ℝ) ≤ Q := by
    have a : (D.R.k : ℝ) ≤ D.R.r := by exact_mod_cast hkr
    exact a.trans (hr.trans (hpow 5 (by linarith)))
  have htQ : (D.R.t : ℝ) ≤ Q := ht.trans (hpow 401 (by linarith))
  have hNQ : (D.R.N D.R.m : ℝ) ≤ Q := hN.trans (hpow 402 (by linarith))
  have hΔ : (Delv L.sc cD : ℝ) ≤ 2 * Q := by
    have a := Nat.ceil_lt_add_one (a := L.sc.x ^ cD) (by positivity)
    have b := hpow cD (by linarith)
    unfold Delv; linarith
  have hh : (h0v L.sc ch : ℝ) ≤ 4 * Q := by
    have a := Nat.ceil_lt_add_one (a := L.sc.x ^ ch) (by positivity)
    have b := hpow ch (by linarith)
    unfold h0v; push_cast; linarith
  have hSc : L.Sc = (D.R.k : ℝ) * (4 * (Delv L.sc cD : ℝ)) := by
    rw [L.Sc_eq, hV.Del_eq]; push_cast; rfl
  obtain ⟨c1, c2, c3, c4, c5⟩ := lstar_den_le (D.R.n : ℝ) D.R.t (D.R.N D.R.m) L.sc.L D.R.k D.R.m
    (Delv L.sc cD) (h0v L.sc ch) Q hQ100 (by positivity) (by positivity) (by positivity) (by linarith)
    (by positivity) (by positivity) (by positivity) (by positivity) hnQ htQ hNQ (hl.trans hxQ) hkQ
    (hm.trans hxQ) hΔ hh
  rw [← hSc] at c1 c2
  rw [← hV.eta_eq] at c3
  have hm1 : (1 : ℝ) ≤ D.R.m := by
    have := D.R.two_le_m
    exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hn0 : (0 : ℝ) < D.R.n := by unfold Ranks.n; positivity
  have ht0 : (0 : ℝ) < D.R.t := by
    have := D.R.three_m_lt_t
    exact_mod_cast (by omega : 0 < D.R.t)
  have hl0 : 0 < L.sc.L := by linarith
  have hSc0 : 0 ≤ L.Sc := by rw [hSc]; positivity
  unfold lStar
  exact lstar_ineqs_of_le _ _ _ _ _ _ _ (Q ^ 7) hm1 (by positivity) c1 c2 c3 c4 c5 hb2 hb1

end GlobalTheory.EX
