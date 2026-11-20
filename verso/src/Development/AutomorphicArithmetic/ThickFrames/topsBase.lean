import Development.AutomorphicArithmetic.ThickFrames.MarkedLow
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions
import Development.AutomorphicArithmetic.ThickFrames.topsFrame

open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.GlobalTheoryTheory Classical

/- English proof (translation)
Establish `hx0 : 0 < x` using `by linarith`. Establish `hL : 0 < Real.log x` using `Real.log_pos (by linarith)`. Establish `hl2 : 4 * Real.log 2 ≤ Real.log x`. Establish `h16 : Real.log 16 = 4 * Real.log 2`. Rewrite using `[show (16:ℝ) = 2 ^ 4 by norm_num, Real.log_pow]`.

Evaluate the numerical expressions. Rewrite using `[← h16]`. Conclude with `Real.log_le_log (by norm_num) hx`. Establish `hlk : Real.log k ≤ Real.log 2 + (9 / 2 + 10 * eps) * Real.log x`. Establish `h` using `Real.log_le_log hk0 hk`.

Rewrite `h` using `[Real.log_mul (by norm_num) (by positivity), Real.log_rpow hx0]`. Conclude with `h`. Establish `hCo0 : 0 < Co` using `by linarith`. Establish `hlp : eps / (5 * Co) * Real.log x < Real.log p`. Establish `hp0 : 0 < x ^ (eps / (5 * Co))` using `by positivity`.

Establish `h` using `Real.log_lt_log hp0 hp`. Rewrite `h` using `[Real.log_rpow hx0]`. Then use the resulting hypothesis. Establish `hlp0 : 0 < Real.log p` using `lt_trans (by positivity) hlp`. Establish `hnum : Real.log ((k * x ^ (26:ℝ)) ^ 4) = 4 * Real.log k + 104 * Real.log x`. Rewrite using `[Real.log_pow, Real.log_mul hk0.ne' (by positivity), Real.log_rpow hx0]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `heL : eps * Real.log x ≤ 1 / 52 * Real.log x` using `mul_le_mul_of_nonneg_right he'.le hL.le`. Establish `h1 : 4 * Real.log k + 104 * Real.log x ≤ 124 * Real.log x` using `by nlinarith`. Establish `h2 : 124 * Real.log x = 620 * Co / eps * (eps / (5 * Co) * Real.log x)`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : 620 * Co / eps * (eps / (5 * Co) * Real.log x) ≤ 620 * Co / eps * Real.log p` using `mul_le_mul_of_nonneg_left hlp.le (by positivity)`. Rewrite using `[Real.logb, hnum, div_le_iff₀ hlp0]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem logb_le' {x eps Co k p : ℝ} (he : 0 < eps) (he' : eps < 1 / 52) (hCo : 1 ≤ Co) (hx : 16 ≤ x) (hk0 : 0 < k)
    (hk : k ≤ 2 * x ^ (9 / 2 + 10 * eps)) (hp : x ^ (eps / (5 * Co)) < p) :
    Real.logb p ((k * x ^ (26 : ℝ)) ^ 4) ≤ 620 * Co / eps := by
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hl2 : 4 * Real.log 2 ≤ Real.log x := by
    have h16 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16:ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
      norm_num
    rw [← h16]
    exact Real.log_le_log (by norm_num) hx
  have hlk : Real.log k ≤ Real.log 2 + (9 / 2 + 10 * eps) * Real.log x := by
    have h := Real.log_le_log hk0 hk
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hx0] at h
    exact h
  have hCo0 : 0 < Co := by linarith
  have hlp : eps / (5 * Co) * Real.log x < Real.log p := by
    have hp0 : 0 < x ^ (eps / (5 * Co)) := by positivity
    have h := Real.log_lt_log hp0 hp
    rwa [Real.log_rpow hx0] at h
  have hlp0 : 0 < Real.log p := lt_trans (by positivity) hlp
  have hnum : Real.log ((k * x ^ (26:ℝ)) ^ 4) = 4 * Real.log k + 104 * Real.log x := by
    rw [Real.log_pow, Real.log_mul hk0.ne' (by positivity), Real.log_rpow hx0]
    push_cast
    ring
  have heL : eps * Real.log x ≤ 1 / 52 * Real.log x := mul_le_mul_of_nonneg_right he'.le hL.le
  have h1 : 4 * Real.log k + 104 * Real.log x ≤ 124 * Real.log x := by nlinarith
  have h2 : 124 * Real.log x = 620 * Co / eps * (eps / (5 * Co) * Real.log x) := by
    field_simp
    ring
  have h3 : 620 * Co / eps * (eps / (5 * Co) * Real.log x) ≤ 620 * Co / eps * Real.log p :=
    mul_le_mul_of_nonneg_left hlp.le (by positivity)
  rw [Real.logb, hnum, div_le_iff₀ hlp0]
  linarith

/- English proof (translation)
Establish `hCo0 : 0 < Co` using `by linarith`. Establish `hb0 : 0 ≤ 620 * Co / eps` using `by positivity`. Establish `hk0 : (0:ℝ) < B.R.k`. Establish `h3` using `B.R.m_add_three_le_k`. Conclude with `(show 0 < B.R.k by omega)` after adjusting the coercions.

Establish `hmem : ∀ l ∈ {l | ∃ p, Nat.Prime p ∧ B.cls p = PrimeClass.inertClass ∧ l = B.L1 p}, l ≤ ⌊620 * Co / eps + 1⌋₊`. Introduce and unpack `l ⟨p, hpr, hc, rfl⟩`. Apply `Nat.le_floor` to reduce the goal to its premises. Establish `hlog` using `logb_le' he he' hCo hx hk0 hk (hp p hpr hc)`. Establish `hA : Scale.A = 26` using `rfl`.

Unfold `Arith.Base.L1`. Rewrite using `[hA]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `Nat.ceil_mono hlog` after adjusting the coercions. Use `_ ≤ 620 * Co / eps + 1 := (Nat.ceil_lt_add_one hb0).le`.

Establish `hs : sSup {l | ∃ p, Nat.Prime p ∧ B.cls p = PrimeClass.inertClass ∧ l = B.L1 p} ≤ ⌊620 * Co / eps + 1⌋₊` using `csSup_le' hmem`. Establish `hf : ((⌊620 * Co / eps + 1⌋₊ : ℕ) : ℝ) ≤ 620 * Co / eps + 1` using `Nat.floor_le (by positivity)`. Establish `hs' : ((sSup {l | ∃ p, Nat.Prime p ∧ B.cls p = PrimeClass.inertClass ∧ l = B.L1 p} : ℕ) : ℝ) ≤ 620 * Co / eps + 1` using `le_trans (by exact_mod_cast hs) hf`. Unfold `Arith.Base.Ltwo`. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem ltwo_le' (B : Arith.Base) {eps Co : ℝ} (he : 0 < eps) (he' : eps < 1 / 52) (hCo : 1 ≤ Co) (hx : 16 ≤ B.sc.x)
    (hk : (B.R.k : ℝ) ≤ 2 * B.sc.x ^ (9 / 2 + 10 * eps))
    (hp : ∀ p : ℕ, p.Prime → B.IsResidueClassZero p → B.sc.x ^ (eps / (5 * Co)) < p) :
    (B.Ltwo : ℝ) ≤ 2 * (620 * Co / eps + 1) := by
  have hCo0 : 0 < Co := by linarith
  have hb0 : 0 ≤ 620 * Co / eps := by positivity
  have hk0 : (0:ℝ) < B.R.k := by
    have h3 := B.R.m_add_three_le_k
    exact_mod_cast (show 0 < B.R.k by omega)
  have hmem : ∀ l ∈ {l | ∃ p, Nat.Prime p ∧ B.cls p = PrimeClass.inertClass ∧ l = B.L1 p},
      l ≤ ⌊620 * Co / eps + 1⌋₊ := by
    rintro l ⟨p, hpr, hc, rfl⟩
    apply Nat.le_floor
    have hlog := logb_le' he he' hCo hx hk0 hk (hp p hpr hc)
    have hA : Scale.A = 26 := rfl
    unfold Arith.Base.L1
    rw [hA]
    calc (⌈Real.logb p ((B.R.k * B.sc.x ^ (26:ℝ)) ^ 4)⌉₊ : ℝ) ≤ ⌈620 * Co / eps⌉₊ := by
          exact_mod_cast Nat.ceil_mono hlog
      _ ≤ 620 * Co / eps + 1 := (Nat.ceil_lt_add_one hb0).le
  have hs : sSup {l | ∃ p, Nat.Prime p ∧ B.cls p = PrimeClass.inertClass ∧ l = B.L1 p} ≤
      ⌊620 * Co / eps + 1⌋₊ := csSup_le' hmem
  have hf : ((⌊620 * Co / eps + 1⌋₊ : ℕ) : ℝ) ≤ 620 * Co / eps + 1 := Nat.floor_le (by positivity)
  have hs' : ((sSup {l | ∃ p, Nat.Prime p ∧ B.cls p = PrimeClass.inertClass ∧ l = B.L1 p} : ℕ) : ℝ) ≤
      620 * Co / eps + 1 := le_trans (by exact_mod_cast hs) hf
  unfold Arith.Base.Ltwo
  push_cast
  linarith

/- English proof (translation)
Unfold `Arith.bsH`. Use `split_ifs with hex`. Conclude with `Nat.find_spec hex`. Conclude with `⟨0, by simp⟩`.
-/
private theorem bsH_orb' {φ : Formalism.HC.Frame} (h t : φ.A) : ∃ i : ℕ, Arith.bsH h t + i • h = t := by
  unfold Arith.bsH
  split_ifs with hex
  · exact Nat.find_spec hex
  · exact ⟨0, by simp⟩

/- English proof (translation)
Introduce `eps Co he he' hCo`. Take `⟨Cb, x₀, hCb, hmain⟩` from `topsFrame eps Co (2 * (620 * Co / eps + 1)) he`. Use `⟨Cb, max x₀ 16, hCb, ?_⟩` and prove the remaining obligations. Introduce `B h hBe hx hn1 hn2 ho hk hp`. Establish `hx16 : 16 ≤ B.sc.x` using `le_trans (le_max_right _ _) hx`.

Establish `hxx : x₀ ≤ B.sc.x` using `le_trans (le_max_left _ _) hx`. Establish `hL` using `ltwo_le' B he he' hCo hx16 hk hp`. Take `⟨TT, h1, h2, h3, h4⟩` from `hmain B.sc.x hxx B.R.toFrame B.Ltwo (by simpa [hE, Ranks.n] using hn1) (by simpa [hE, Ranks.n] using hn2) ho hL Arith.bsH (fun a b => bsH_orb' a b) ((Finset.range ⌈B.sc.X'⌉₊).filter (fun p => p.Prime ∧ B.IsResidueClassZero p ∧ B.sc.x ^ (B.sc.eps / 4) ≤ (addOrderOf (h p) : ℝ))) h …`. Introduce `p hp'`. Rewrite `hp'` using `[Finset.mem_filter]`.

Rewrite using `[← hBe]`. Conclude with `hp'.2.2.2)`. Establish `hd : dE eps B.sc.x = B.sc.delta1` using `by simp [dE, Scale.delta1, hBe]`. Establish `e1 : G.KG B.sc = KE eps` using `by simp [G.KG, KE, G.hG, hE, hBe]`. Establish `e2 : G.rG B.sc = rE eps` using `by simp [G.rG, rE, e1]`.

Establish `e3 : G.hG B.sc = hE eps` using `by simp [G.hG, hE, hBe]`. Use `⟨TT, ?_, ?_, h3, ?_⟩` and prove the remaining obligations. Rewrite using `[← hd]`. Conclude with `h1`. Rewrite using `[← hd]`.

Conclude with `h2`. Use `le_trans (le_of_eq ?_) (h4.trans (le_of_eq ?_))` and prove the remaining obligations. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `p hpP`. Rewrite `hpP` using `[Finset.mem_filter]`.

Establish `hC0 : B.cls p = PrimeClass.inertClass` using `hpP.2.2.1`. Establish `hst : Arith.Loc.stepP { B with TT` using `TT } (h p) p = h p := by`. Simplify using `[Arith.Loc.stepP, Arith.Base.IsSg, hC0]`. Rewrite using `[hst]`. Establish `hS : ∀ t, Arith.Loc.Good { B with TT` using `TT } (h p) (Arith.bsH (h p) t) ↔ G.IsGoodOrbit (addOrderOf (h p)) {i | Arith.bsH (h p) t + (i : ℕ) • h p ∈ TT} B.Ltwo (KE eps) (rE eps) (dE eps B.sc.x) (hE eps) B.sc.x := by`.

Introduce `t`. Simplify using `only [Arith.Loc.Good, Arith.Loc.topsPos]`. Establish `hLt : Arith.Base.Ltwo { B with TT` using `TT } = B.Ltwo := rfl`. Rewrite using `[e1, e2, e3, hd, hLt]`. Use `congr 2`.

Rewrite using `[← Set.ncard_coe_finset, Finset.coe_filter]`. Use `congr 1`. Use extensionality with `t`. Simplify using `only [Set.mem_setOf_eq, hS t]`. Rewrite using `[hd, Ranks.n]`.
-/
theorem UpperTheory.BernoulliSumsFrobeniusOrbits.topsBase :
    ∀ eps Co : ℝ, 0 < eps → eps < 1 / 52 → 1 ≤ Co → ∃ Cb x₀ : ℝ, 0 < Cb ∧ ∀ (B : Arith.Base) (h : ℕ → B.H),
      B.sc.eps = eps → x₀ ≤ B.sc.x → B.sc.x ^ (2 + 8 * eps) / 2 ≤ (B.R.n : ℝ) → (B.R.n : ℝ) ≤ Co * B.sc.x ^ (2 + 8 * eps) →
      (B.R.toFrame.o : ℝ) ≤ Co → (B.R.k : ℝ) ≤ 2 * B.sc.x ^ (9 / 2 + 10 * eps) →
      (∀ p : ℕ, p.Prime → B.IsResidueClassZero p → B.sc.x ^ (eps / (5 * Co)) < p) →
      ∃ TT : Finset B.R.A, B.sc.delta1 * B.R.n / 2 ≤ (TT.card : ℝ) ∧ (TT.card : ℝ) ≤ 2 * B.sc.delta1 * B.R.n ∧
        B.R.toFrame.Shares TT (B.sc.x ^ (-1 + eps)) ∧
        ∑ p ∈ (Finset.range ⌈B.sc.X'⌉₊).filter (fun p => p.Prime ∧ B.IsResidueClassZero p ∧ B.sc.x ^ (B.sc.eps / 4) ≤ (addOrderOf (h p) : ℝ)),
            Real.log p / p * ((TT.filter (fun t => ¬ Arith.Loc.Good { B with TT := TT } (h p)
              (Arith.bsH (Arith.Loc.stepP { B with TT := TT } (h p) p) t))).card : ℝ) ≤
          4 * (Cb * B.sc.x ^ (-2 : ℝ)) * B.sc.delta1 * B.R.n *
            ∑ p ∈ (Finset.range ⌈B.sc.X'⌉₊).filter (fun p => p.Prime ∧ B.IsResidueClassZero p ∧ B.sc.x ^ (B.sc.eps / 4) ≤ (addOrderOf (h p) : ℝ)),
              Real.log p / p := by
  intro eps Co he he' hCo
  obtain ⟨Cb, x₀, hCb, hmain⟩ := topsFrame eps Co (2 * (620 * Co / eps + 1)) he
  refine ⟨Cb, max x₀ 16, hCb, ?_⟩
  intro B h hBe hx hn1 hn2 ho hk hp
  have hx16 : 16 ≤ B.sc.x := le_trans (le_max_right _ _) hx
  have hxx : x₀ ≤ B.sc.x := le_trans (le_max_left _ _) hx
  have hL := ltwo_le' B he he' hCo hx16 hk hp
  obtain ⟨TT, h1, h2, h3, h4⟩ := hmain B.sc.x hxx B.R.toFrame B.Ltwo
    (by simpa [hE, Ranks.n] using hn1) (by simpa [hE, Ranks.n] using hn2) ho hL Arith.bsH
    (fun a b => bsH_orb' a b)
    ((Finset.range ⌈B.sc.X'⌉₊).filter
      (fun p => p.Prime ∧ B.IsResidueClassZero p ∧ B.sc.x ^ (B.sc.eps / 4) ≤ (addOrderOf (h p) : ℝ)))
    h (fun p => Real.log p / p) (fun p => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
    (by
      intro p hp'
      rw [Finset.mem_filter] at hp'
      rw [← hBe]
      exact hp'.2.2.2)
  have hd : dE eps B.sc.x = B.sc.delta1 := by simp [dE, Scale.delta1, hBe]
  have e1 : G.KG B.sc = KE eps := by simp [G.KG, KE, G.hG, hE, hBe]
  have e2 : G.rG B.sc = rE eps := by simp [G.rG, rE, e1]
  have e3 : G.hG B.sc = hE eps := by simp [G.hG, hE, hBe]
  refine ⟨TT, ?_, ?_, h3, ?_⟩
  · rw [← hd]
    exact h1
  · rw [← hd]
    exact h2
  · refine le_trans (le_of_eq ?_) (h4.trans (le_of_eq ?_))
    · apply Finset.sum_congr rfl
      intro p hpP
      rw [Finset.mem_filter] at hpP
      have hC0 : B.cls p = PrimeClass.inertClass := hpP.2.2.1
      have hst : Arith.Loc.stepP { B with TT := TT } (h p) p = h p := by
        simp [Arith.Loc.stepP, Arith.Base.IsSg, hC0]
      rw [hst]
      have hS : ∀ t, Arith.Loc.Good { B with TT := TT } (h p) (Arith.bsH (h p) t) ↔
          G.IsGoodOrbit (addOrderOf (h p)) {i | Arith.bsH (h p) t + (i : ℕ) • h p ∈ TT} B.Ltwo (KE eps)
            (rE eps) (dE eps B.sc.x) (hE eps) B.sc.x := by
        intro t
        simp only [Arith.Loc.Good, Arith.Loc.topsPos]
        have hLt : Arith.Base.Ltwo { B with TT := TT } = B.Ltwo := rfl
        rw [e1, e2, e3, hd, hLt]
      congr 2
      rw [← Set.ncard_coe_finset, Finset.coe_filter]
      congr 1
      ext t
      simp only [Set.mem_setOf_eq, hS t]
    · rw [hd, Ranks.n]
