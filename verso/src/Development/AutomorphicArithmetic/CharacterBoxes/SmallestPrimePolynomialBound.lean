import Development.AutomorphicArithmetic.CharacterBoxes.Supply
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.HC GlobalTheory.EX UpperTheory.Top

namespace UpperTheory.Top.PolynomialHostPrimeBound

open GlobalTheory.EX.DC

/- English proof (translation)
Take `⟨p, hp, hm, hle⟩` from `hS _ (one_lt_rPrH_mul H)`. Establish `hq : (q0H H : ℝ) ≤ p` using `by exact_mod_cast globalTwisting_le_fact H hc hp hm`. Establish `hN : 2 ≤ H.QS * H.q * H.d` using `H.hyp.2.1.one_lt.trans_le (Nat.le_mul_of_pos_left _ (Nat.mul_pos H.QS_pos H.hyp.1.pos))`. Establish `e : ((H.QS : ℝ) * H.q * H.d) = ((H.QS * H.q * H.d : ℕ) : ℝ)` using `by push_cast; ring`. Rewrite `h1`, `h2`, the goal using `[e]`.

Establish `a2 : 0 < H.pde - 1` using `Nat.sub_pos_of_lt H.pde_prime.one_lt`. Establish `a3 : 0 < H.pde' - 1` using `Nat.sub_pos_of_lt H.pde'_prime.one_lt`. Establish `hr : rPrH H ≤ 2 * (H.QS * H.q * H.d * (H.pde - 1) * (H.pde' - 1))`. Establish `hM : 0 < H.QS * H.q * H.d * (H.pde - 1) * (H.pde' - 1)` using `Nat.mul_pos (Nat.mul_pos (by omega) a2) a3`. Take `⟨r, hr, hr1, hr2⟩` from `Nat.exists_prime_lt_and_le_two_mul _ hM.ne'`.

Use `(rPrH_le H hr ?_).trans hr2` and prove the remaining obligations. Rewrite using `[hc, Ideal.absNorm_top, mul_one]`. Conclude with `Nat.not_dvd_of_pos_of_lt hM hr1`. Generalize the expression as in `H.QS * H.q * H.d = N at *`. Establish `hN' : (2 : ℝ) ≤ N` using `by exact_mod_cast hN`.

Establish `hN0 : (0 : ℝ) < N` using `by linarith`. Apply the tactic sequence `have hr' : rPrH H ≤ N * (N * H.pde * H.pde') := hr.trans (by gcongr <;> omega)`. Establish `hr'' : (rPrH H : ℝ) ≤ N * (N * H.pde * H.pde')` using `by exact_mod_cast hr'`. Establish `hb : ((rPrH H * N : ℕ) : ℝ) ≤ (N : ℝ) ^ (3 + 2 * C)`. Establish `: (N : ℝ) ^ (3 + 2 * C) = N * (N * N ^ C * N ^ C) * N`.

Rewrite using `[show 3 + 2 * C = ((3 : ℕ) : ℝ) + C + C by push_cast; ring, Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_natCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, Nat.cast_mul]`. Use `mul_le_mul_of_nonneg_right (hr''.trans ?_) hN0.le` and prove the remaining obligations. Use `gcongr`.

Rewrite using `[Real.rpow_mul hN0.le]`. Conclude with `hq.trans (hle.trans (Real.rpow_le_rpow (Nat.cast_nonneg _) hb (by linarith)))`.
-/
private theorem smallest_prime_polynomial_bound {A C : ℝ} (hA : 1 ≤ A)
    (hS : ∀ M : ℕ, 2 ≤ M → ∃ p : ℕ, p.Prime ∧ p % M = 1 ∧ (p : ℝ) ≤ (M : ℝ) ^ A)
    {R : Ranks} (H : Host R) (hc : H.ccK = ⊤) (h1 : (H.pde : ℝ) ≤ ((H.QS : ℝ) * H.q * H.d) ^ C)
    (h2 : (H.pde' : ℝ) ≤ ((H.QS : ℝ) * H.q * H.d) ^ C) :
    (q0H H : ℝ) ≤ ((H.QS : ℝ) * H.q * H.d) ^ ((3 + 2 * C) * A) := by
  obtain ⟨p, hp, hm, hle⟩ := hS _ (one_lt_rPrH_mul H)
  have hq : (q0H H : ℝ) ≤ p := by exact_mod_cast globalTwisting_le_fact H hc hp hm
  have hN : 2 ≤ H.QS * H.q * H.d :=
    H.hyp.2.1.one_lt.trans_le (Nat.le_mul_of_pos_left _ (Nat.mul_pos H.QS_pos H.hyp.1.pos))
  have e : ((H.QS : ℝ) * H.q * H.d) = ((H.QS * H.q * H.d : ℕ) : ℝ) := by push_cast; ring
  rw [e] at h1 h2 ⊢
  have a2 : 0 < H.pde - 1 := Nat.sub_pos_of_lt H.pde_prime.one_lt
  have a3 : 0 < H.pde' - 1 := Nat.sub_pos_of_lt H.pde'_prime.one_lt
  have hr : rPrH H ≤ 2 * (H.QS * H.q * H.d * (H.pde - 1) * (H.pde' - 1)) := by
    have hM : 0 < H.QS * H.q * H.d * (H.pde - 1) * (H.pde' - 1) :=
      Nat.mul_pos (Nat.mul_pos (by omega) a2) a3
    obtain ⟨r, hr, hr1, hr2⟩ := Nat.exists_prime_lt_and_le_two_mul _ hM.ne'
    refine (rPrH_le H hr ?_).trans hr2
    rw [hc, Ideal.absNorm_top, mul_one]
    exact Nat.not_dvd_of_pos_of_lt hM hr1
  generalize H.QS * H.q * H.d = N at *
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hr' : rPrH H ≤ N * (N * H.pde * H.pde') := hr.trans (by gcongr <;> omega)
  have hr'' : (rPrH H : ℝ) ≤ N * (N * H.pde * H.pde') := by exact_mod_cast hr'
  have hb : ((rPrH H * N : ℕ) : ℝ) ≤ (N : ℝ) ^ (3 + 2 * C) := by
    have : (N : ℝ) ^ (3 + 2 * C) = N * (N * N ^ C * N ^ C) * N := by
      rw [show 3 + 2 * C = ((3 : ℕ) : ℝ) + C + C by push_cast; ring, Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_natCast]
      ring
    rw [this, Nat.cast_mul]
    refine mul_le_mul_of_nonneg_right (hr''.trans ?_) hN0.le
    gcongr
  rw [Real.rpow_mul hN0.le]
  exact hq.trans (hle.trans (Real.rpow_le_rpow (Nat.cast_nonneg _) hb (by linarith)))

private noncomputable def relevel {R : Ranks} (H : Host R) (hc : H.ccK = ⊤) (q0 : ℕ) (h0 : Nat.Coprime q0 H.QS) : Host R :=
  { H with
    levelPrimes := {H.g 0, H.g 1, H.pde, H.pde', q0}
    g_level := by intro i; fin_cases i <;> simp
    pde_level := by simp
    level_coprimeS := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with h | h | h | h | h <;> rw [h]
      · exact H.level_coprimeS _ (H.g_level 0)
      · exact H.level_coprimeS _ (H.g_level 1)
      · exact H.level_coprimeS _ H.pde_level.1
      · exact H.level_coprimeS _ H.pde_level.2
      · exact h0
    ccK_coprime := fun p _ => by rw [hc, Ideal.absNorm_top]; exact Nat.coprime_one_left p }

end UpperTheory.Top.PolynomialHostPrimeBound

open GlobalTheory.EX.DC UpperTheory.Top.PolynomialHostPrimeBound in
/- English proof (translation)
Introduce `hS la G hH`. Take `⟨A, hA, hS⟩` from `hS`. Introduce `eps he he'`. Take `⟨CT2, C8, C5, c6, Cb, x0, h8, h5, h6, hb, S, hH⟩` from `hH eps he he'`. Establish `hC : C8 ≤ (3 + 2 * C8) * A` using `by nlinarith`.

Use `⟨CT2, (3 + 2 * C8) * A, C5, c6, Cb, x0, h8.trans hC, h5, h6, hb, S, fun s hs hx hm => ?_⟩` and prove the remaining obligations. Take `⟨R, H, q0, hR, hT, ⟨hv, har, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, -, -⟩, hG⟩` from `hH s hs hx hm`. Establish `hc : H.ccK = ⊤` using `hv.2.2.2.2.2.2.1`. Establish `h0 : Nat.Coprime (q0H H) H.QS`. Establish `h1 : q0H H ≡ 1 [MOD H.QS * H.q * H.d]`.

Use `mod_cond H` as an intermediate fact. Establish `h2 : 1 < H.QS * H.q * H.d`. Assume the negation of the conclusion as `h3`. Establish `h4 : H.QS * H.q * H.d = 1` using `by have := cond_pos H; omega`. Rewrite `this` using `[h4]`.

Use linear arithmetic over natural numbers and integers. Unfold `Nat.ModEq`. Rewrite using `[this, Nat.mod_eq_of_lt h2]`. Establish `h5 : Nat.Coprime (q0H H) (H.QS * H.q * H.d)`. Rewrite using `[Nat.Coprime, h1.gcd_eq]`.

Simplify using the standard rewrite rules. Conclude with `Nat.Coprime.coprime_dvd_right ((dvd_mul_right _ _).mul_right _) h5`. Establish `hv' : HostVal s ((3 + 2 * C8) * A) (relevel H hc (q0H H) h0)` using `(hv.mono hC :)`. Establish `hq` using `smallest_prime_polynomial_bound hA hS H hc hv.2.2.2.1.1 hv.2.2.2.1.2`. Establish `har' : HostArith (relevel H hc (q0H H) h0)`.

Use `⟨har.1, har.2.1, har.2.2.1, fun l hl => ?_⟩` and prove the remaining obligations. Establish `hl' : l ∈ ({H.g 0, H.g 1, H.pde, H.pde', q0H H} : Finset ℕ)` using `hl`. Use `show H.cls l = .splitK`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at hl'`. Apply the tactic sequence `rcases hl' with h | h | h | h | h <;> rw [h]`.

Conclude with `har.2.2.2 _ (H.g_level 0)`. Conclude with `har.2.2.2 _ (H.g_level 1)`. Conclude with `har.2.2.2 _ H.pde_level.1`. Conclude with `har.2.2.2 _ H.pde_level.2`. Conclude with `(GlobalTheory.HostSplit.split_of_one_mod R H _ (globalTwisting_spec_fact H).1 (mod_cond H)).2`.

Conclude with `⟨R, relevel H hc (q0H H) h0, q0H H, hR, hT, ⟨hv', har', g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, ⟨(globalTwisting_spec_fact H).1, mod_cond H, hq, q0H_ne_pde_and_ne_pde' H⟩, rfl⟩, globalTwisting_congr_fact _ rfl rfl rfl rfl rfl rfl, hG⟩`.
-/
theorem UpperTheory.Top.hostQ :
    SmallPrimeOne → ∀ (la : ℝ) (G : FReq), HostExW la G.req → DC.HostExQW la G.req := by
  intro hS la G hH
  obtain ⟨A, hA, hS⟩ := hS
  intro eps he he'
  obtain ⟨CT2, C8, C5, c6, Cb, x0, h8, h5, h6, hb, S, hH⟩ := hH eps he he'
  have hC : C8 ≤ (3 + 2 * C8) * A := by nlinarith
  refine ⟨CT2, (3 + 2 * C8) * A, C5, c6, Cb, x0, h8.trans hC, h5, h6, hb, S, fun s hs hx hm => ?_⟩
  obtain ⟨R, H, q0, hR, hT, ⟨hv, har, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, -, -⟩, hG⟩ := hH s hs hx hm
  have hc : H.ccK = ⊤ := hv.2.2.2.2.2.2.1
  have h0 : Nat.Coprime (q0H H) H.QS := by
    have h1 : q0H H ≡ 1 [MOD H.QS * H.q * H.d] := by
      have := mod_cond H
      have h2 : 1 < H.QS * H.q * H.d := by
        by_contra h3
        have h4 : H.QS * H.q * H.d = 1 := by have := cond_pos H; omega
        rw [h4] at this
        omega
      unfold Nat.ModEq
      rw [this, Nat.mod_eq_of_lt h2]
    have h5 : Nat.Coprime (q0H H) (H.QS * H.q * H.d) := by
      rw [Nat.Coprime, h1.gcd_eq]
      simp
    exact Nat.Coprime.coprime_dvd_right ((dvd_mul_right _ _).mul_right _) h5
  have hv' : HostVal s ((3 + 2 * C8) * A) (relevel H hc (q0H H) h0) := (hv.mono hC :)
  have hq := smallest_prime_polynomial_bound hA hS H hc hv.2.2.2.1.1 hv.2.2.2.1.2
  have har' : HostArith (relevel H hc (q0H H) h0) := by
    refine ⟨har.1, har.2.1, har.2.2.1, fun l hl => ?_⟩
    have hl' : l ∈ ({H.g 0, H.g 1, H.pde, H.pde', q0H H} : Finset ℕ) := hl
    show H.cls l = .splitK
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl'
    rcases hl' with h | h | h | h | h <;> rw [h]
    · exact har.2.2.2 _ (H.g_level 0)
    · exact har.2.2.2 _ (H.g_level 1)
    · exact har.2.2.2 _ H.pde_level.1
    · exact har.2.2.2 _ H.pde_level.2
    · exact (GlobalTheory.HostSplit.split_of_one_mod R H _ (globalTwisting_spec_fact H).1 (mod_cond H)).2
  exact ⟨R, relevel H hc (q0H H) h0, q0H H, hR, hT, ⟨hv', har', g1, g2, g3, g4, g5, g6, g7, g8, g9, g10,
    ⟨(globalTwisting_spec_fact H).1, mod_cond H, hq, q0H_ne_pde_and_ne_pde' H⟩, rfl⟩, globalTwisting_congr_fact _ rfl rfl rfl rfl rfl rfl, hG⟩
