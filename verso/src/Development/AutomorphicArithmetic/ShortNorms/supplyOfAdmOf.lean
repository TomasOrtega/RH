import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AutomorphicArithmetic.CharacterBoxes.Imports
import Development.AutomorphicArithmetic.CharacterBoxes.WinPairs
import Development.AutomorphicArithmetic.CharacterBoxes.FieldChi
import Development.AutomorphicArithmetic.CharacterBoxes.IsChiField
import Development.AutomorphicArithmetic.CharacterBoxes.BoundedTw
import Development.AutomorphicArithmetic.CharacterBoxes.PairHyp
import Development.AutomorphicArithmetic.CharacterBoxes.EventuallyRankLeRpowOfLtOneDivFiftytwo
import Development.AutomorphicArithmetic.MeanSquareBounds.pairEx

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.HC GlobalTheory.EX UpperTheory.Top HostParam.Seam

/- English proof (translation)
Introduce `hSup ψ hV hAdm eps heps heps'`. Use `haveI := ψ.ne`. Establish `hN0 : 0 < ψ.N` using `Nat.pos_of_ne_zero (NeZero.ne _)`. Establish `heps0 : eps ≠ 0` using `heps.ne'`. Take `⟨c, e0, hc, hF⟩` from `UpperTheory.Top.fieldChi ψ`.

Take `⟨J, hJ, hwin⟩` from `UpperTheory.Top.winPairs ψ eps (c : ℝ) heps heps' (by exact_mod_cast hc) hV QH.pairEx`. Choose the witnesses or unpack the hypotheses as in `⟨C0, hC1, hCJ, hCo, hCN⟩ : ∃ C0 : ℝ, 1 ≤ C0 ∧ J ≤ C0 ∧ ((Level.cyc ψ).o : ℝ) ≤ C0 ∧ 8 * (ψ.N : ℝ) ≤ C0 := by`. Establish `h1 : (0 : ℝ) ≤ ((Level.cyc ψ).o : ℝ)` using `Nat.cast_nonneg _`. Establish `h2 : (0 : ℝ) ≤ (ψ.N : ℝ)` using `Nat.cast_nonneg _`. Conclude with `⟨J + ((Level.cyc ψ).o : ℝ) + 8 * (ψ.N : ℝ), by linarith, by linarith, by linarith, by linarith⟩`.

Take `⟨CT2, C8, c6, Cb, x0A, hC8, hc6, hCb, hA⟩` from `hSup eps C0 heps heps' hC1`. Take `⟨x0B, hB⟩` from `hAdm eps heps heps'`. Take `⟨x0T, hT⟩` from `UpperTheory.Top.eventually_rank_le_rpow_of_lt_one_div_fiftytwo eps heps heps'`. Choose the witnesses or unpack the hypotheses as in `⟨K, hK5, hK4⟩ : ∃ K : ℝ, 5 ≤ K ∧ 4 * (ψ.N : ℝ) ≤ K := by`. Establish `h2 : (0 : ℝ) ≤ (ψ.N : ℝ)` using `Nat.cast_nonneg _`.

Conclude with `⟨5 + 4 * (ψ.N : ℝ), by linarith, by linarith⟩`. Establish `hK0 : 0 ≤ K` using `by linarith`. Choose the witnesses or unpack the hypotheses as in `⟨A, hA0, hAK⟩ : ∃ A : ℝ, 0 ≤ A ∧ A ^ (eps / 5) = K := by`. Use `⟨K ^ (5 / eps), Real.rpow_nonneg hK0 _, ?_⟩` and prove the remaining obligations. Rewrite using `[← Real.rpow_mul hK0, show 5 / eps * (eps / 5) = (1 : ℝ) by field_simp, Real.rpow_one]`.

Establish `hc0 : (0 : ℝ) ≤ c` using `by positivity`. Establish `hAJ0 : 0 ≤ A ^ J` using `Real.rpow_nonneg hA0 _`. Choose the witnesses or unpack the hypotheses as in `⟨x1, h1A, h1B, h1T, h1J, h1c⟩ : ∃ x1 : ℝ, x0A ≤ x1 ∧ x0B ≤ x1 ∧ x0T ≤ x1 ∧ A ^ J ≤ x1 ∧ (c : ℝ) * 2 ^ e0 < x1 := by`. Establish `h2 : (0 : ℝ) ≤ (c : ℝ) * 2 ^ e0` using `by positivity`. Apply the tactic sequence `refine ⟨|x0A| + |x0B| + |x0T| + A ^ J + (c : ℝ) * 2 ^ e0 + 1, ?_, ?_, ?_, ?_, ?_⟩ <;>`.

Combine the linear relations using `[le_abs_self x0A, le_abs_self x0B, le_abs_self x0T, abs_nonneg x0A, abs_nonneg x0B, abs_nonneg x0T]`. Use `⟨CT2, C8, 4, c6, Cb, x1, le_trans hC1 hC8, by norm_num, hc6, hCb, ?_⟩` and prove the remaining obligations. Use `⟨⟨J, hJ, {x | ∃ Y q d e, UpperTheory.Top.WinDatum ψ eps J c x Y q d e}, hwin⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `s hs hx ⟨hsJ, Y, q, d, e, hW⟩`. Establish `hx1 : 1 < s.x` using `s.one_lt_alt`.

Establish `hJ0 : 0 < J` using `by linarith`. Establish `hYA : A ≤ Y`. Combine the equalities or inequalities in the displayed calculation. Establish `hY0 : 0 ≤ Y` using `hA0.trans hYA`. Establish `hYK : K ≤ Y ^ (eps / 5)`.

Rewrite using `[← hAK]`. Conclude with `Real.rpow_le_rpow hA0 hYA (by positivity)`. Take `⟨hHyp, hjac, -⟩` from `UpperTheory.Top.pairHyp eps Y q d hW.good.pair`. Establish `hq3 : q ≠ 3`. Introduce `hq`.

Establish `h1` using `hW.good.pair.q_lo`. Rewrite `h1` using `[hq]`. Move the coercions through the operations in `at h1`. Establish `h2 : Real.log 3 ≤ 2`. Use `Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Establish `he : e ≥ e0`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`.

Establish `h1 : (2 : ℝ) ^ e ≤ 2 ^ e0` using `pow_le_pow_right₀ (by norm_num) hlt.le`. Establish `h2 : s.x ≤ s.x ^ (2 + 8 * eps)`. Combine the equalities or inequalities in the displayed calculation. Establish `h3` using `hW.n_lo`. Combine the linear relations using `[mul_le_mul_of_nonneg_left h1 hc0]`.

Establish `h4N : 4 * ψ.N ≤ ⌊Y ^ (eps / 5)⌋₊`. Apply `Nat.le_floor` to reduce the goal to its premises. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hjacb : ∀ p : ℕ, Nat.Prime p → p ≠ 2 → p ≤ ⌊Y ^ (eps / 5)⌋₊ → jacobiSym (-(d : ℤ)) p = 1` using `fun p hp hp2 hpb => hjac p hp hp2 ((Nat.cast_le.2 hpb).trans (Nat.floor_le (Real.rpow_nonneg hY0 _)))`.

Take `⟨φ, H0, hφe, hφord, hHq, hHd, hφo, hFR, hQSdvd, hQSle, hkept, hps, hker, htw⟩` from `hF e he q d ⌊Y ^ (eps / 5)⌋₊ hHyp hq3 hW.good.coprime h4N hjacb`. Take `⟨R, h, hRV, hAdmR⟩` from `hB s φ H0 hs (h1B.trans hx) (by rw [hφord]; push_cast; exact hW.n_lo) (by rw [hφord]; push_cast; exact hW.n_up) hφo hker`. Substitute `h` using the available equality. Establish `hnlo` using `hRV.n_lo`. Rewrite `hnlo` using `[hs]`.

Establish `hQS : (H0.QS : ℝ) ≤ C0 * R.n`. Establish `hq' : (H0.QS : ℝ) ≤ 4 * ψ.N * R.toFrame.ord` using `by exact_mod_cast hQSle`. Establish `hord : (R.toFrame.ord : ℝ) = c * 2 ^ e` using `by rw [hφord]; push_cast; ring`. Establish `hn : (0 : ℝ) ≤ R.n` using `Nat.cast_nonneg _`. Establish `hN : (0 : ℝ) ≤ ψ.N` using `Nat.cast_nonneg _`.

Rewrite `hq'` using `[hord]`. Establish `h5` using `hW.n_up`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ 4 * ψ.N), mul_le_mul_of_nonneg_left hnlo (by positivity : (0 : ℝ) ≤ 8 * ψ.N), mul_le_mul_of_nonneg_right hCN hn]`. Take `⟨H, q0, hH, hCT, hGood, hSh⟩` from `hA s R H0 ψ.N Y hs (h1A.trans hx) hRV (by rw [hsJ]; exact hCJ) (by rw [hφo]; exact hCo) hQS hN0 (by have : (0 : ℝ) ≤ ψ.N := Nat.cast_nonneg _; linarith) (by rw [hφe]; exact hQSdvd) ⟨by rw [hsJ]; exact hW.lo, hW.up⟩ (by rw [hHq, hHd]; exact hW.good) hFR hAdmR`. Substitute `hH` using the available equality.

Use `⟨R, H, q0, hRV, hCT, hGood, ?_, ?_⟩` and prove the remaining obligations. Establish `hprime : ∀ l : ℕ, Nat.Prime l → l ∣ H.QS → l ∣ 2 * ψ.N`. Introduce `l hl hlQ`. Establish `h1 : l ∣ 2 ^ (e + 2) * ψ.N` using `hlQ.trans (hQSdvd.trans (Nat.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _)))`. Break down `(Nat.Prime.dvd_mul hl).1 h1 with h2 | h2` into its components or cases.

Establish `h3` using `(Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (hl.dvd_of_dvd_pow h2)`. Substitute `h3` using the available equality. Conclude with `dvd_mul_right 2 _`. Conclude with `dvd_mul_of_dvd_right h2 2`. Establish `hbd` using `UpperTheory.Top.boundedTw ψ R.toFrame H.toHostRaw eps Y s.x heps hx1.le hW.up htw hker.1 hprime (by rw [hHq, hHd]; exact hW.good)`.

Rewrite `hSh`, the goal using `[hs]`. Conclude with `⟨hφo, hkept, hps, hSh, hbd.1, hbd.2⟩`. Establish `hCF` using `UpperTheory.Top.isChiField ψ R.toFrame H.toHostRaw hker`. Rewrite `hCF` using `[hφe, hHq, hHd]`. Establish `hv` using `hW.bound H.E hCF`.

Use `hv.mono ?_ (le_of_eq ?_)` and prove the remaining obligations. Apply `Nat.le_floor` to reduce the goal to its premises. Conclude with `hT s R hs (h1T.trans hx) hRV`. Rewrite using `[Formalism.BasicNotions.Scale.b, Formalism.BasicNotions.Scale.L, hs]`.
-/
theorem UpperTheory.T3.supplyOfAdmOf :
    (∀ eps C0 : ℝ, 0 < eps → eps < 1 / 52 → 1 ≤ C0 → ∃ CT2 C8 c6 Cb x0 : ℝ, C0 ≤ C8 ∧ 0 < c6 ∧ 0 < Cb ∧
      ∀ (s : Scale) (R : Ranks) (H0 : HostAx R.toFrame) (M : ℕ) (Y : ℝ), s.eps = eps → x0 ≤ s.x → RankVal s R →
        s.J ≤ C0 → (R.o : ℝ) ≤ C0 → (H0.QS : ℝ) ≤ C0 * R.n → 0 < M → (M : ℝ) ≤ C0 → H0.QS ∣ Nat.lcm (2 ^ (R.e + 2)) M →
        PairWin s Y → PairGood M eps Y s.x H0.q H0.d → FieldRows H0.toHostRaw ⌊Y ^ (eps / 5)⌋₊ → admitted R H0 →
        ∃ (H : Host R) (q0 : ℕ), H.toHostAx = H0 ∧ H.CT2 = CT2 ∧ HostGood s C8 4 c6 Cb H q0 ∧
          R.toFrame.Shares H.TT (s.x ^ (-1 + s.eps))) → ∀ ψ : PChar, VWinAt ψ 401 →
      (∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (s : Scale) (φ : Frame) (H0 : HostAx φ), s.eps = eps → x0 ≤ s.x →
        s.x ^ (2 + 8 * eps) ≤ (φ.ord : ℝ) → (φ.ord : ℝ) ≤ 2 * s.x ^ (2 + 8 * eps) → φ.o = (Level.cyc ψ).o → KerChi ψ H0.toHostRaw →
        ∃ (R : Ranks) (h : R.toFrame = φ), RankVal s R ∧ admitted R (h ▸ H0)) →
      HostExW (3 / 2) (fun _ s R H _ => EAtH (Level.cyc ψ) H.toHostRaw H.TT s.x s.eps 4 ∧ VVle H.E R.t (Real.sqrt s.b)) := by
  intro hSup ψ hV hAdm eps heps heps'
  haveI := ψ.ne
  have hN0 : 0 < ψ.N := Nat.pos_of_ne_zero (NeZero.ne _)
  have heps0 : eps ≠ 0 := heps.ne'
  obtain ⟨c, e0, hc, hF⟩ := UpperTheory.Top.fieldChi ψ
  obtain ⟨J, hJ, hwin⟩ := UpperTheory.Top.winPairs ψ eps (c : ℝ) heps heps' (by exact_mod_cast hc) hV QH.pairEx
  obtain ⟨C0, hC1, hCJ, hCo, hCN⟩ : ∃ C0 : ℝ, 1 ≤ C0 ∧ J ≤ C0 ∧ ((Level.cyc ψ).o : ℝ) ≤ C0 ∧
      8 * (ψ.N : ℝ) ≤ C0 :=
    by
      have h1 : (0 : ℝ) ≤ ((Level.cyc ψ).o : ℝ) := Nat.cast_nonneg _
      have h2 : (0 : ℝ) ≤ (ψ.N : ℝ) := Nat.cast_nonneg _
      exact ⟨J + ((Level.cyc ψ).o : ℝ) + 8 * (ψ.N : ℝ), by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨CT2, C8, c6, Cb, x0A, hC8, hc6, hCb, hA⟩ := hSup eps C0 heps heps' hC1
  obtain ⟨x0B, hB⟩ := hAdm eps heps heps'
  obtain ⟨x0T, hT⟩ := UpperTheory.Top.eventually_rank_le_rpow_of_lt_one_div_fiftytwo eps heps heps'
  obtain ⟨K, hK5, hK4⟩ : ∃ K : ℝ, 5 ≤ K ∧ 4 * (ψ.N : ℝ) ≤ K :=
    by
      have h2 : (0 : ℝ) ≤ (ψ.N : ℝ) := Nat.cast_nonneg _
      exact ⟨5 + 4 * (ψ.N : ℝ), by linarith, by linarith⟩
  have hK0 : 0 ≤ K := by linarith
  obtain ⟨A, hA0, hAK⟩ : ∃ A : ℝ, 0 ≤ A ∧ A ^ (eps / 5) = K := by
    refine ⟨K ^ (5 / eps), Real.rpow_nonneg hK0 _, ?_⟩
    rw [← Real.rpow_mul hK0, show 5 / eps * (eps / 5) = (1 : ℝ) by field_simp, Real.rpow_one]
  have hc0 : (0 : ℝ) ≤ c := by positivity
  have hAJ0 : 0 ≤ A ^ J := Real.rpow_nonneg hA0 _
  obtain ⟨x1, h1A, h1B, h1T, h1J, h1c⟩ : ∃ x1 : ℝ, x0A ≤ x1 ∧ x0B ≤ x1 ∧ x0T ≤ x1 ∧ A ^ J ≤ x1 ∧
      (c : ℝ) * 2 ^ e0 < x1 := by
    have h2 : (0 : ℝ) ≤ (c : ℝ) * 2 ^ e0 := by positivity
    refine ⟨|x0A| + |x0B| + |x0T| + A ^ J + (c : ℝ) * 2 ^ e0 + 1, ?_, ?_, ?_, ?_, ?_⟩ <;>
      linarith [le_abs_self x0A, le_abs_self x0B, le_abs_self x0T, abs_nonneg x0A, abs_nonneg x0B,
        abs_nonneg x0T]
  refine ⟨CT2, C8, 4, c6, Cb, x1, le_trans hC1 hC8, by norm_num, hc6, hCb, ?_⟩
  refine ⟨⟨J, hJ, {x | ∃ Y q d e, UpperTheory.Top.WinDatum ψ eps J c x Y q d e}, hwin⟩, ?_⟩
  rintro s hs hx ⟨hsJ, Y, q, d, e, hW⟩
  have hx1 : 1 < s.x := s.one_lt_alt
  have hJ0 : 0 < J := by linarith
  have hYA : A ≤ Y := by
    calc A = (A ^ J) ^ (1 / J) := by rw [one_div, Real.rpow_rpow_inv hA0 hJ0.ne']
      _ ≤ s.x ^ (1 / J) := Real.rpow_le_rpow hAJ0 (h1J.trans hx) (div_nonneg zero_le_one hJ0.le)
      _ ≤ Y := hW.lo
  have hY0 : 0 ≤ Y := hA0.trans hYA
  have hYK : K ≤ Y ^ (eps / 5) := by
    rw [← hAK]
    exact Real.rpow_le_rpow hA0 hYA (by positivity)
  obtain ⟨hHyp, hjac, -⟩ := UpperTheory.Top.pairHyp eps Y q d hW.good.pair
  have hq3 : q ≠ 3 := by
    intro hq
    have h1 := hW.good.pair.q_lo
    rw [hq] at h1
    push_cast at h1
    have h2 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      linarith
    linarith
  have he : e ≥ e0 := by
    by_contra hlt
    push_neg at hlt
    have h1 : (2 : ℝ) ^ e ≤ 2 ^ e0 := pow_le_pow_right₀ (by norm_num) hlt.le
    have h2 : s.x ≤ s.x ^ (2 + 8 * eps) := by
      calc s.x = s.x ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
    have h3 := hW.n_lo
    linarith [mul_le_mul_of_nonneg_left h1 hc0]
  have h4N : 4 * ψ.N ≤ ⌊Y ^ (eps / 5)⌋₊ := by
    apply Nat.le_floor
    push_cast
    linarith
  have hjacb : ∀ p : ℕ, Nat.Prime p → p ≠ 2 → p ≤ ⌊Y ^ (eps / 5)⌋₊ → jacobiSym (-(d : ℤ)) p = 1 :=
    fun p hp hp2 hpb => hjac p hp hp2 ((Nat.cast_le.2 hpb).trans (Nat.floor_le (Real.rpow_nonneg hY0 _)))
  obtain ⟨φ, H0, hφe, hφord, hHq, hHd, hφo, hFR, hQSdvd, hQSle, hkept, hps, hker, htw⟩ :=
    hF e he q d ⌊Y ^ (eps / 5)⌋₊ hHyp hq3 hW.good.coprime h4N hjacb
  obtain ⟨R, h, hRV, hAdmR⟩ := hB s φ H0 hs (h1B.trans hx)
    (by rw [hφord]; push_cast; exact hW.n_lo) (by rw [hφord]; push_cast; exact hW.n_up) hφo hker
  subst h
  have hnlo := hRV.n_lo
  rw [hs] at hnlo
  have hQS : (H0.QS : ℝ) ≤ C0 * R.n := by
    have hq' : (H0.QS : ℝ) ≤ 4 * ψ.N * R.toFrame.ord := by exact_mod_cast hQSle
    have hord : (R.toFrame.ord : ℝ) = c * 2 ^ e := by rw [hφord]; push_cast; ring
    have hn : (0 : ℝ) ≤ R.n := Nat.cast_nonneg _
    have hN : (0 : ℝ) ≤ ψ.N := Nat.cast_nonneg _
    rw [hord] at hq'
    have h5 := hW.n_up
    nlinarith [mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ 4 * ψ.N),
      mul_le_mul_of_nonneg_left hnlo (by positivity : (0 : ℝ) ≤ 8 * ψ.N),
      mul_le_mul_of_nonneg_right hCN hn]
  obtain ⟨H, q0, hH, hCT, hGood, hSh⟩ := hA s R H0 ψ.N Y hs (h1A.trans hx) hRV
    (by rw [hsJ]; exact hCJ) (by rw [hφo]; exact hCo) hQS hN0
    (by have : (0 : ℝ) ≤ ψ.N := Nat.cast_nonneg _; linarith)
    (by rw [hφe]; exact hQSdvd) ⟨by rw [hsJ]; exact hW.lo, hW.up⟩
    (by rw [hHq, hHd]; exact hW.good) hFR hAdmR
  subst hH
  refine ⟨R, H, q0, hRV, hCT, hGood, ?_, ?_⟩
  · have hprime : ∀ l : ℕ, Nat.Prime l → l ∣ H.QS → l ∣ 2 * ψ.N := by
      intro l hl hlQ
      have h1 : l ∣ 2 ^ (e + 2) * ψ.N := hlQ.trans (hQSdvd.trans (Nat.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _)))
      rcases (Nat.Prime.dvd_mul hl).1 h1 with h2 | h2
      · have h3 := (Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (hl.dvd_of_dvd_pow h2)
        subst h3
        exact dvd_mul_right 2 _
      · exact dvd_mul_of_dvd_right h2 2
    have hbd := UpperTheory.Top.boundedTw ψ R.toFrame H.toHostRaw eps Y s.x heps hx1.le hW.up htw hker.1 hprime
      (by rw [hHq, hHd]; exact hW.good)
    rw [hs] at hSh ⊢
    exact ⟨hφo, hkept, hps, hSh, hbd.1, hbd.2⟩
  · have hCF := UpperTheory.Top.isChiField ψ R.toFrame H.toHostRaw hker
    rw [hφe, hHq, hHd] at hCF
    have hv := hW.bound H.E hCF
    refine hv.mono ?_ (le_of_eq ?_)
    · apply Nat.le_floor
      exact hT s R hs (h1T.trans hx) hRV
    · rw [Formalism.BasicNotions.Scale.b, Formalism.BasicNotions.Scale.L, hs]
