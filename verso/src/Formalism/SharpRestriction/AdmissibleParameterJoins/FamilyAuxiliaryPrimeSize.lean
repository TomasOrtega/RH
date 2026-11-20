import Formalism.SharpRestriction.Divisibility.AbsolutelyIrreducibleSpan
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.LogEightBound.ProgTwo
import Formalism.SharpRestriction.ElevenLe
import Formalism.SharpRestriction.ParConsts

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

/- English proof (translation)
Take `⟨C, hC, h⟩` from `Formalism.HermitianLattices.Ext.B4.progTwo`. Use `⟨C, hC, fun D L hN hS => ?_⟩` and prove the remaining obligations. Establish `hc4 : 4 ≤ LevelStarExponents.condE D`. Establish `h1` using `AbsolutelyIrreducibleSpan.condE_pos D`. Establish `hd : 4 ∣ LevelStarExponents.condE D`.

Unfold `LevelStarExponents.condE`. Establish `h4 : 4 ∣ D.host.QS` using `(show (4 : ℕ) ∣ 2 ^ (D.R.e + 2) from pow_dvd_pow 2 (by omega : 2 ≤ D.R.e + 2)).trans D.host.tower_dvd`. Conclude with `(h4.mul_right _).mul_right _`. Conclude with `Nat.le_of_dvd h1 hd`. Establish `hr : 1 ≤ AbsolutelyIrreducibleSpan.rPr D` using `(AbsolutelyIrreducibleSpan.rPr_mem D).1.one_lt.le`.

Establish `hM : 3 ≤ AbsolutelyIrreducibleSpan.rPr D * LevelStarExponents.condE D` using `by nlinarith`. Take `⟨p, -, -, hp, -, hp1, -, hlp, -⟩` from `h _ hM`. Establish `hgt : AbsolutelyIrreducibleSpan.rPr D * LevelStarExponents.condE D < p`. Establish `h2 : p % (AbsolutelyIrreducibleSpan.rPr D * LevelStarExponents.condE D) = 1 % (AbsolutelyIrreducibleSpan.rPr D * LevelStarExponents.condE D)` using `hp1`. Rewrite `h2` using `[Nat.mod_eq_of_lt (by omega : 1 < AbsolutelyIrreducibleSpan.rPr D * LevelStarExponents.condE D)]`.

Assume the negation of the conclusion as `hn`. Establish `hle : p ≤ AbsolutelyIrreducibleSpan.rPr D * LevelStarExponents.condE D` using `not_lt.1 hn`. Break down `Nat.lt_or_ge p (AbsolutelyIrreducibleSpan.rPr D * LevelStarExponents.condE D) with h3 | h3` into its components or cases. Rewrite `h2` using `[Nat.mod_eq_of_lt h3]`. Conclude with `hp.one_lt.ne' h2`.

Establish `: p = AbsolutelyIrreducibleSpan.rPr D * LevelStarExponents.condE D` using `le_antisymm hle h3`. Rewrite `h2` using `[this, Nat.mod_self]`. Use linear arithmetic over natural numbers and integers. Use `AbsolutelyIrreducibleSpan.auxiliary_prime_admissible_of_prime D L p hp ?_ ?_ (le_trans hlp hS)` and prove the remaining obligations. Establish `h2 : p % (AbsolutelyIrreducibleSpan.rPr D * LevelStarExponents.condE D) = 1 % (AbsolutelyIrreducibleSpan.rPr D * LevelStarExponents.condE D)` using `hp1`.

Rewrite `h2` using `[Nat.mod_eq_of_lt (by omega : 1 < AbsolutelyIrreducibleSpan.rPr D * LevelStarExponents.condE D)]`. Then use the resulting hypothesis. Introduce `hd`. Use `Nat.le_of_dvd (AbsolutelyIrreducibleSpan.absNorm_ccK_pos D) hd` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem auxiliary_prime_size_bound : ∃ C : ℝ, 0 < C ∧ ∀ (D : D7) (L : SizeData₂ D),
    Ideal.absNorm D.host.ccK ≤ AbsolutelyIrreducibleSpan.rPr D * LevelStarExponents.condE D →
    C * Real.log ((AbsolutelyIrreducibleSpan.rPr D * LevelStarExponents.condE D : ℕ) : ℝ) ^ 2 ≤ L.sc.L → AbsolutelyIrreducibleSpan.adm9 D L := by
  obtain ⟨C, hC, h⟩ := Formalism.HermitianLattices.Ext.B4.progTwo
  refine ⟨C, hC, fun D L hN hS => ?_⟩
  have hc4 : 4 ≤ LevelStarExponents.condE D := by
    have h1 := AbsolutelyIrreducibleSpan.condE_pos D
    have hd : 4 ∣ LevelStarExponents.condE D := by
      unfold LevelStarExponents.condE
      have h4 : 4 ∣ D.host.QS :=
        (show (4 : ℕ) ∣ 2 ^ (D.R.e + 2) from pow_dvd_pow 2 (by omega : 2 ≤ D.R.e + 2)).trans D.host.tower_dvd
      exact (h4.mul_right _).mul_right _
    exact Nat.le_of_dvd h1 hd
  have hr : 1 ≤ AbsolutelyIrreducibleSpan.rPr D := (AbsolutelyIrreducibleSpan.rPr_mem D).1.one_lt.le
  have hM : 3 ≤ AbsolutelyIrreducibleSpan.rPr D * LevelStarExponents.condE D := by nlinarith
  obtain ⟨p, -, -, hp, -, hp1, -, hlp, -⟩ := h _ hM
  have hgt : AbsolutelyIrreducibleSpan.rPr D * LevelStarExponents.condE D < p := by
    have h2 : p % (AbsolutelyIrreducibleSpan.rPr D * LevelStarExponents.condE D) = 1 % (AbsolutelyIrreducibleSpan.rPr D * LevelStarExponents.condE D) := hp1
    rw [Nat.mod_eq_of_lt (by omega : 1 < AbsolutelyIrreducibleSpan.rPr D * LevelStarExponents.condE D)] at h2
    by_contra hn
    have hle : p ≤ AbsolutelyIrreducibleSpan.rPr D * LevelStarExponents.condE D := not_lt.1 hn
    rcases Nat.lt_or_ge p (AbsolutelyIrreducibleSpan.rPr D * LevelStarExponents.condE D) with h3 | h3
    · rw [Nat.mod_eq_of_lt h3] at h2
      exact hp.one_lt.ne' h2
    · have : p = AbsolutelyIrreducibleSpan.rPr D * LevelStarExponents.condE D := le_antisymm hle h3
      rw [this, Nat.mod_self] at h2
      omega
  refine AbsolutelyIrreducibleSpan.auxiliary_prime_admissible_of_prime D L p hp ?_ ?_ (le_trans hlp hS)
  · have h2 : p % (AbsolutelyIrreducibleSpan.rPr D * LevelStarExponents.condE D) = 1 % (AbsolutelyIrreducibleSpan.rPr D * LevelStarExponents.condE D) := hp1
    rwa [Nat.mod_eq_of_lt (by omega : 1 < AbsolutelyIrreducibleSpan.rPr D * LevelStarExponents.condE D)] at h2
  · intro hd
    have := Nat.le_of_dvd (AbsolutelyIrreducibleSpan.absNorm_ccK_pos D) hd
    omega

def zPr (D : D7) : ℕ := LevelStarExponents.condE D * (D.host.pde - 1) * (D.host.pde' - 1) * Ideal.absNorm D.host.ccK

/- English proof (translation)
Unfold `zPr`. Establish `h1 : 0 < D.host.pde - 1` using `by have := D.host.pde_prime.two_le; omega`. Establish `h2 : 0 < D.host.pde' - 1` using `by have := D.host.pde'_prime.two_le; omega`. Establish `h3` using `AbsolutelyIrreducibleSpan.absNorm_ccK_pos D`. Use `AbsolutelyIrreducibleSpan.condE_pos D` as an intermediate fact.

Check the signs of the components of the expression.
-/
theorem zPr_pos (D : D7) : 0 < zPr D := by
  unfold zPr
  have h1 : 0 < D.host.pde - 1 := by have := D.host.pde_prime.two_le; omega
  have h2 : 0 < D.host.pde' - 1 := by have := D.host.pde'_prime.two_le; omega
  have h3 := AbsolutelyIrreducibleSpan.absNorm_ccK_pos D
  have := AbsolutelyIrreducibleSpan.condE_pos D
  positivity

/- English proof (translation)
Establish `h1 : 2 ^ Z.primeFactors.card ≤ ∏ p ∈ Z.primeFactors, p` using `Finset.pow_card_le_prod _ _ _ fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le`. Establish `h2 : ∏ p ∈ Z.primeFactors, p ≤ Z` using `Nat.le_of_dvd hZ (Nat.prod_primeFactors_dvd Z)`. Establish `h3 : ((2 : ℝ)) ^ Z.primeFactors.card ≤ (Z : ℝ)` using `by exact_mod_cast le_trans h1 h2`. Establish `h4` using `Real.log_le_log (by positivity) h3`. Rewrite `h4` using `[Real.log_pow]`. Then use the resulting hypothesis.
-/
theorem card_pf_le (Z : ℕ) (hZ : 0 < Z) : (Z.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log Z := by
  have h1 : 2 ^ Z.primeFactors.card ≤ ∏ p ∈ Z.primeFactors, p :=
    Finset.pow_card_le_prod _ _ _ fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have h2 : ∏ p ∈ Z.primeFactors, p ≤ Z := Nat.le_of_dvd hZ (Nat.prod_primeFactors_dvd Z)
  have h3 : ((2 : ℝ)) ^ Z.primeFactors.card ≤ (Z : ℝ) := by exact_mod_cast le_trans h1 h2
  have h4 := Real.log_le_log (by positivity) h3
  rwa [Real.log_pow] at h4

/- English proof (translation)
Take `⟨C, hC, h⟩` from `Formalism.HermitianLattices.Ext.SupplyAP.supplyPrimesEff`. Use `⟨C, hC, fun D => ?_⟩` and prove the remaining obligations. Take `⟨S, hS, hq⟩` from `h 1 ((zPr D).primeFactors.card + 1) le_rfl`. Establish `hex : ∃ q ∈ S, ¬ q ∣ zPr D`. Assume the negation of the conclusion as `hn`.

Establish `hsub : S ⊆ (zPr D).primeFactors` using `fun q hqS => Nat.mem_primeFactors.2 ⟨(hq q hqS).1, by_contra fun h => hn ⟨q, hqS, h⟩, (zPr_pos D).ne'⟩`. Use `Finset.card_le_card hsub` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨q, hqS, hqd⟩` from `hex`. Take `⟨hqp, -, hqle⟩` from `hq q hqS`.

Establish `hle : AbsolutelyIrreducibleSpan.rPr D ≤ q` using `Nat.sInf_le (show q ∈ {p : ℕ | p.Prime ∧ ¬ p ∣ LevelStarExponents.condE D * (D.host.pde - 1) * (D.host.pde' - 1) * Ideal.absNorm D.host.ccK} from ⟨hqp, hqd⟩)`. Establish `hr0 : (0 : ℝ) < (AbsolutelyIrreducibleSpan.rPr D : ℝ)` using `by exact_mod_cast (AbsolutelyIrreducibleSpan.rPr_mem D).1.pos`. Establish `h1 : Real.log (AbsolutelyIrreducibleSpan.rPr D : ℝ) ≤ Real.log (q : ℝ)` using `Real.log_le_log hr0 (by exact_mod_cast hle)`. Establish `hq0 : (0 : ℝ) < (q : ℝ)` using `by exact_mod_cast hqp.pos`. Establish `h2` using `Real.log_le_log hq0 hqle`.

Rewrite `h2` using `[Real.log_exp]`. Establish `e : (2 * ((1 : ℕ) : ℝ) * ((((zPr D).primeFactors.card + 1 : ℕ) : ℝ) + 2)) = 2 * (((zPr D).primeFactors.card : ℝ) + 3)` using `by push_cast; ring`. Rewrite `h2` using `[e]`. Conclude with `le_trans h1 h2`.
-/
theorem log_rPr_le : ∃ C : ℝ, 0 < C ∧ ∀ D : D7,
    Real.log (AbsolutelyIrreducibleSpan.rPr D : ℝ) ≤ C * Real.log (2 * (((zPr D).primeFactors.card : ℝ) + 3)) ^ 2 := by
  obtain ⟨C, hC, h⟩ := Formalism.HermitianLattices.Ext.SupplyAP.supplyPrimesEff
  refine ⟨C, hC, fun D => ?_⟩
  obtain ⟨S, hS, hq⟩ := h 1 ((zPr D).primeFactors.card + 1) le_rfl
  have hex : ∃ q ∈ S, ¬ q ∣ zPr D := by
    by_contra hn
    have hsub : S ⊆ (zPr D).primeFactors := fun q hqS =>
      Nat.mem_primeFactors.2 ⟨(hq q hqS).1, by_contra fun h => hn ⟨q, hqS, h⟩, (zPr_pos D).ne'⟩
    have := Finset.card_le_card hsub
    omega
  obtain ⟨q, hqS, hqd⟩ := hex
  obtain ⟨hqp, -, hqle⟩ := hq q hqS
  have hle : AbsolutelyIrreducibleSpan.rPr D ≤ q := Nat.sInf_le (show q ∈ {p : ℕ | p.Prime ∧
    ¬ p ∣ LevelStarExponents.condE D * (D.host.pde - 1) * (D.host.pde' - 1) * Ideal.absNorm D.host.ccK} from ⟨hqp, hqd⟩)
  have hr0 : (0 : ℝ) < (AbsolutelyIrreducibleSpan.rPr D : ℝ) := by exact_mod_cast (AbsolutelyIrreducibleSpan.rPr_mem D).1.pos
  have h1 : Real.log (AbsolutelyIrreducibleSpan.rPr D : ℝ) ≤ Real.log (q : ℝ) := Real.log_le_log hr0 (by exact_mod_cast hle)
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqp.pos
  have h2 := Real.log_le_log hq0 hqle
  rw [Real.log_exp] at h2
  have e : (2 * ((1 : ℕ) : ℝ) * ((((zPr D).primeFactors.card + 1 : ℕ) : ℝ) + 2)) =
      2 * (((zPr D).primeFactors.card : ℝ) + 3) := by push_cast; ring
  rw [e] at h2
  exact le_trans h1 h2

/- English proof (translation)
Take `⟨hN, -, -, -, -, -, hQD, -⟩` from `hS`. Take `⟨-, -, hq, -, hd, -, -, -⟩` from `hQD`. Unfold `Formalism.MainNotions.szTh at hq hd`. Establish `hx1` using `L.sc.one_lt_alt`. Establish `hn0 : (0 : ℝ) < (D.R.n : ℝ)`.

Establish `: 0 < D.R.n` using `by unfold Ranks.n; positivity`. Conclude with `this` after adjusting the coercions. Establish `hq0 : (0 : ℝ) < (D.host.q : ℝ)` using `by exact_mod_cast D.host.hyp.1.pos`. Establish `hd0 : (0 : ℝ) < (D.host.d : ℝ)` using `by exact_mod_cast D.host.hyp.2.1.pos`. Establish `hlogn : Real.log (D.R.n : ℝ) ≤ (2 + 8 * L.sc.eps + L.sc.eps / 100) * Real.log L.sc.x`.

Use `Real.log_le_log hn0 hN.2` as an intermediate fact. Unfold `Formalism.MainNotions.szTh at this`. Rewrite `this` using `[Real.log_rpow (by linarith)]`. Then use the resulting hypothesis. Establish `hcond : (LevelStarExponents.condE D : ℝ) = (D.host.QS : ℝ) * D.host.q * D.host.d`. Unfold `LevelStarExponents.condE`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hQ0 : (0 : ℝ) < (D.host.QS : ℝ)` using `by exact_mod_cast D.host.QS_pos`. Establish `hQ : Real.log (D.host.QS : ℝ) ≤ 2 * Real.log (D.R.n : ℝ)`. Establish `h1 : (D.host.QS : ℝ) ≤ (D.R.n : ℝ) ^ 2` using `by exact_mod_cast D.host.QS_le`.

Establish `h2` using `Real.log_le_log hQ0 h1`. Rewrite `h2` using `[Real.log_pow]`. Conclude with `h2` after adjusting the coercions. Establish `h4 : 0 ≤ Real.log 4` using `Real.log_nonneg (by norm_num)`. Rewrite using `[hcond, Real.log_mul (by positivity) hd0.ne', Real.log_mul hQ0.ne' hq0.ne']`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem log_cond_le {D : D7} (L : SizeData₂ D) (hS : Formalism.MainNotions.SizesAt L) : Real.log (LevelStarExponents.condE D : ℝ) ≤
    Real.log 4 + 2 * (2 + 8 * L.sc.eps + L.sc.eps / 100) * Real.log L.sc.x + 2 * L.sc.x ^ (L.sc.eps / 5 + L.sc.eps / 100) := by
  obtain ⟨hN, -, -, -, -, -, hQD, -⟩ := hS
  obtain ⟨-, -, hq, -, hd, -, -, -⟩ := hQD
  unfold Formalism.MainNotions.szTh at hq hd
  have hx1 := L.sc.one_lt_alt
  have hn0 : (0 : ℝ) < (D.R.n : ℝ) := by
    have : 0 < D.R.n := by unfold Ranks.n; positivity
    exact_mod_cast this
  have hq0 : (0 : ℝ) < (D.host.q : ℝ) := by exact_mod_cast D.host.hyp.1.pos
  have hd0 : (0 : ℝ) < (D.host.d : ℝ) := by exact_mod_cast D.host.hyp.2.1.pos
  have hlogn : Real.log (D.R.n : ℝ) ≤ (2 + 8 * L.sc.eps + L.sc.eps / 100) * Real.log L.sc.x := by
    have := Real.log_le_log hn0 hN.2
    unfold Formalism.MainNotions.szTh at this
    rwa [Real.log_rpow (by linarith)] at this
  have hcond : (LevelStarExponents.condE D : ℝ) = (D.host.QS : ℝ) * D.host.q * D.host.d := by
    unfold LevelStarExponents.condE; push_cast; ring
  have hQ0 : (0 : ℝ) < (D.host.QS : ℝ) := by exact_mod_cast D.host.QS_pos
  have hQ : Real.log (D.host.QS : ℝ) ≤ 2 * Real.log (D.R.n : ℝ) := by
    have h1 : (D.host.QS : ℝ) ≤ (D.R.n : ℝ) ^ 2 := by exact_mod_cast D.host.QS_le
    have h2 := Real.log_le_log hQ0 h1
    rw [Real.log_pow] at h2
    exact_mod_cast h2
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [hcond, Real.log_mul (by positivity) hd0.ne', Real.log_mul hQ0.ne' hq0.ne']
  linarith

/- English proof (translation)
Establish `hc` using `log_cond_le L hS`. Take `⟨-, -, -, -, -, -, hQD, -⟩` from `hS`. Take `⟨-, -, -, -, hd, -, -, -⟩` from `hQD`. Unfold `Formalism.MainNotions.szTh at hd`. Establish `hp` using `P.pde_log`.

Establish `hd0 : (0 : ℝ) < (D.host.d : ℝ)` using `by exact_mod_cast D.host.hyp.2.1.pos`. Establish `hcR : (0 : ℝ) < (LevelStarExponents.condE D : ℝ)` using `by exact_mod_cast AbsolutelyIrreducibleSpan.condE_pos D`. Establish `hpR : (0 : ℝ) < (D.host.pde : ℝ)` using `by exact_mod_cast D.host.pde_prime.pos`. Establish `hpR' : (0 : ℝ) < (D.host.pde' : ℝ)` using `by exact_mod_cast D.host.pde'_prime.pos`. Establish `hNR : (0 : ℝ) < (Ideal.absNorm D.host.ccK : ℝ)` using `by exact_mod_cast AbsolutelyIrreducibleSpan.absNorm_ccK_pos D`.

Establish `hNc : Real.log (Ideal.absNorm D.host.ccK : ℝ) ≤ Real.log P.CccK + L.sc.x ^ (L.sc.eps / 5 + L.sc.eps / 100)`. Use `Real.log_le_log hNR P.ccK_le` as an intermediate fact. Rewrite `this` using `[Real.log_mul P.CccK_pos.ne' hd0.ne']`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1 : zPr D ≤ LevelStarExponents.condE D * D.host.pde * D.host.pde' * Ideal.absNorm D.host.ccK` using `Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) (Nat.sub_le _ _))`.

Establish `h2 : (zPr D : ℝ) ≤ (LevelStarExponents.condE D : ℝ) * D.host.pde * D.host.pde' * Ideal.absNorm D.host.ccK` using `by exact_mod_cast h1`. Establish `hZ0 : (0 : ℝ) < (zPr D : ℝ)` using `by exact_mod_cast zPr_pos D`. Establish `h3` using `Real.log_le_log hZ0 h2`. Rewrite `h3` using `[Real.log_mul (by positivity) hNR.ne', Real.log_mul (by positivity) hpR'.ne', Real.log_mul hcR.ne' hpR.ne']`. Combine the linear relations using `[hp.1, hp.2]`.
-/
theorem log_zPr_le {D : D7} (L : SizeData₂ D) (P : ParameterChoice' D L) (hS : Formalism.MainNotions.SizesAt L) : Real.log (zPr D : ℝ) ≤
    (Real.log 4 + 2 * (2 + 8 * L.sc.eps + L.sc.eps / 100) * Real.log L.sc.x + 2 * L.sc.x ^ (L.sc.eps / 5 + L.sc.eps / 100)) +
      2 * L.sc.L + Real.log P.CccK + L.sc.x ^ (L.sc.eps / 5 + L.sc.eps / 100) := by
  have hc := log_cond_le L hS
  obtain ⟨-, -, -, -, -, -, hQD, -⟩ := hS
  obtain ⟨-, -, -, -, hd, -, -, -⟩ := hQD
  unfold Formalism.MainNotions.szTh at hd
  have hp := P.pde_log
  have hd0 : (0 : ℝ) < (D.host.d : ℝ) := by exact_mod_cast D.host.hyp.2.1.pos
  have hcR : (0 : ℝ) < (LevelStarExponents.condE D : ℝ) := by exact_mod_cast AbsolutelyIrreducibleSpan.condE_pos D
  have hpR : (0 : ℝ) < (D.host.pde : ℝ) := by exact_mod_cast D.host.pde_prime.pos
  have hpR' : (0 : ℝ) < (D.host.pde' : ℝ) := by exact_mod_cast D.host.pde'_prime.pos
  have hNR : (0 : ℝ) < (Ideal.absNorm D.host.ccK : ℝ) := by exact_mod_cast AbsolutelyIrreducibleSpan.absNorm_ccK_pos D
  have hNc : Real.log (Ideal.absNorm D.host.ccK : ℝ) ≤ Real.log P.CccK + L.sc.x ^ (L.sc.eps / 5 + L.sc.eps / 100) := by
    have := Real.log_le_log hNR P.ccK_le
    rw [Real.log_mul P.CccK_pos.ne' hd0.ne'] at this
    linarith
  have h1 : zPr D ≤ LevelStarExponents.condE D * D.host.pde * D.host.pde' * Ideal.absNorm D.host.ccK :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) (Nat.sub_le _ _))
  have h2 : (zPr D : ℝ) ≤ (LevelStarExponents.condE D : ℝ) * D.host.pde * D.host.pde' * Ideal.absNorm D.host.ccK := by exact_mod_cast h1
  have hZ0 : (0 : ℝ) < (zPr D : ℝ) := by exact_mod_cast zPr_pos D
  have h3 := Real.log_le_log hZ0 h2
  rw [Real.log_mul (by positivity) hNR.ne', Real.log_mul (by positivity) hpR'.ne', Real.log_mul hcR.ne' hpR.ne'] at h3
  linarith [hp.1, hp.2]

/- English proof (translation)
Use `set a : ℝ := 2 * (2 + 8 * ε + ε / 100) * (100 / ε) with ha`. Establish `ha0 : 0 ≤ a` using `by positivity`. Use `set E : ℝ := 2 * (8 + a + |κ|) with hE`. Establish `hE0 : 0 ≤ E` using `by positivity`. Use `set F : ℝ := 2 * E + 6 with hF`.

Establish `hF0 : 0 < F` using `by positivity`. Use `set G : ℝ := |Real.log F| + 100 with hG`. Establish `hG0 : 0 ≤ G` using `by positivity`. Use `set B : ℝ := C₁ * G ^ 2 + 5 + a with hB`. Establish `hB0 : 0 ≤ B` using `by positivity`.

Take `⟨x0, h0⟩` from `Filter.eventually_atTop.1 ((tendsto_rpow_atTop (by positivity : 0 < ε / 100)).eventually_ge_atTop (max 1 (C * B ^ 2)))`. Use `⟨x0, fun x hx hx1 ω t hω ht0 hωb ht => ?_⟩` and prove the remaining obligations. Establish `hx0 : 0 ≤ x` using `by linarith`. Use `set y : ℝ := x ^ (ε / 100) with hy`. Establish `hy1 : 1 ≤ y` using `le_trans (le_max_left _ _) (h0 x hx)`.

Establish `hyC : C * B ^ 2 ≤ y` using `le_trans (le_max_right _ _) (h0 x hx)`. Establish `hy0 : 0 < y` using `by linarith`. Establish `e21 : x ^ (ε / 5 + ε / 100) = y ^ 21`. Rewrite using `[hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e100 : x ^ ε = y ^ 100`. Rewrite using `[hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0]`. Use `congr 1`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Establish `hlogy : Real.log y ≤ y` using `Real.log_le_self hy0.le`. Establish `hlog : Real.log x ≤ 100 / ε * y`. Establish `h1 : Real.log y = ε / 100 * Real.log x` using `by rw [hy, Real.log_rpow (by linarith)]`.

Establish `h3 : Real.log x = 100 / ε * Real.log y` using `by rw [h1]; field_simp`. Rewrite using `[h3]`. Conclude with `mul_le_mul_of_nonneg_left hlogy (by positivity)`. Establish `hl4 : Real.log 4 ≤ 3`. Use `Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hy21 : y ≤ y ^ 21`. Combine the equalities or inequalities in the displayed calculation. Establish `h121 : 1 ≤ y ^ 21` using `one_le_pow₀ hy1`. Establish `h1100 : 1 ≤ y ^ 100` using `one_le_pow₀ hy1`.

Establish `h21100 : y ^ 21 ≤ y ^ 100` using `pow_le_pow_right₀ hy1 (by norm_num)`. Establish `h221 : y ^ 2 ≤ y ^ 21` using `pow_le_pow_right₀ hy1 (by norm_num)`. Rewrite `hωb`, `ht` using `[e21]`. Rewrite `hωb` using `[e100]`. Establish `hLam : Real.log 4 + 2 * (2 + 8 * ε + ε / 100) * Real.log x + 2 * y ^ 21 ≤ (5 + a) * y ^ 21`.

Establish `h1 : 2 * (2 + 8 * ε + ε / 100) * Real.log x ≤ a * y`. Rewrite using `[ha, mul_assoc (2 * (2 + 8 * ε + ε / 100))]`. Conclude with `mul_le_mul_of_nonneg_left hlog (by positivity)`. Establish `h2 : a * y ≤ a * y ^ 21` using `mul_le_mul_of_nonneg_left hy21 ha0`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hl2 : (1 : ℝ) / 2 ≤ Real.log 2`. Use `Real.log_two_gt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hωE : ω ≤ E * y ^ 100`. Establish `h1 : ω * (1 / 2) ≤ ω * Real.log 2` using `mul_le_mul_of_nonneg_left hl2 hω`.

Establish `h2 : κ ≤ |κ| * y ^ 100` using `le_trans (le_abs_self κ) (le_mul_of_one_le_right (abs_nonneg κ) h1100)`. Establish `h3 : (5 + a) * y ^ 21 ≤ (5 + a) * y ^ 100` using `mul_le_mul_of_nonneg_left h21100 (by positivity)`. Rewrite using `[hE]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlogω : Real.log (2 * (ω + 3)) ≤ G * y`.

Establish `h1 : 2 * (ω + 3) ≤ F * y ^ 100` using `by rw [hF]; linarith`. Establish `h2` using `Real.log_le_log (by positivity : (0 : ℝ) < 2 * (ω + 3)) h1`. Rewrite `h2` using `[Real.log_mul hF0.ne' (by positivity), Real.log_pow]`. Establish `h3 : Real.log F ≤ |Real.log F| * y` using `le_trans (le_abs_self _) (le_mul_of_one_le_right (abs_nonneg _) hy1)`. Rewrite using `[hG]`.

Move the coercions through the operations in `at h2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlogω0 : 0 ≤ Real.log (2 * (ω + 3))` using `Real.log_nonneg (by linarith)`. Establish `hr : C₁ * Real.log (2 * (ω + 3)) ^ 2 ≤ C₁ * G ^ 2 * y ^ 21`. Establish `h1 : Real.log (2 * (ω + 3)) ^ 2 ≤ (G * y) ^ 2` using `pow_le_pow_left₀ hlogω0 hlogω 2`.

Establish `h2 : (G * y) ^ 2 = G ^ 2 * y ^ 2` using `by ring`. Establish `h3 : G ^ 2 * y ^ 2 ≤ G ^ 2 * y ^ 21` using `mul_le_mul_of_nonneg_left h221 (by positivity)`. Combine the equalities or inequalities in the displayed calculation. Establish `hT : t ≤ B * y ^ 21` using `by rw [hB]; linarith`. Establish `hsq : t ^ 2 ≤ (B * y ^ 21) ^ 2` using `pow_le_pow_left₀ ht0 hT 2`.

Rewrite using `[e100]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem numeric_log_square_estimate (ε : ℝ) (hε : 0 < ε) (C C₁ κ : ℝ) (hC : 0 < C) (hC₁ : 0 < C₁) : ∃ x0 : ℝ, ∀ x ≥ x0, 1 < x →
    ∀ ω t : ℝ, 0 ≤ ω → 0 ≤ t →
    ω * Real.log 2 ≤ (Real.log 4 + 2 * (2 + 8 * ε + ε / 100) * Real.log x + 2 * x ^ (ε / 5 + ε / 100)) + 2 * x ^ ε + κ +
      x ^ (ε / 5 + ε / 100) →
    t ≤ C₁ * Real.log (2 * (ω + 3)) ^ 2 +
      (Real.log 4 + 2 * (2 + 8 * ε + ε / 100) * Real.log x + 2 * x ^ (ε / 5 + ε / 100)) →
    C * t ^ 2 ≤ x ^ ε := by
  set a : ℝ := 2 * (2 + 8 * ε + ε / 100) * (100 / ε) with ha
  have ha0 : 0 ≤ a := by positivity
  set E : ℝ := 2 * (8 + a + |κ|) with hE
  have hE0 : 0 ≤ E := by positivity
  set F : ℝ := 2 * E + 6 with hF
  have hF0 : 0 < F := by positivity
  set G : ℝ := |Real.log F| + 100 with hG
  have hG0 : 0 ≤ G := by positivity
  set B : ℝ := C₁ * G ^ 2 + 5 + a with hB
  have hB0 : 0 ≤ B := by positivity
  obtain ⟨x0, h0⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop (by positivity : 0 < ε / 100)).eventually_ge_atTop (max 1 (C * B ^ 2)))
  refine ⟨x0, fun x hx hx1 ω t hω ht0 hωb ht => ?_⟩
  have hx0 : 0 ≤ x := by linarith
  set y : ℝ := x ^ (ε / 100) with hy
  have hy1 : 1 ≤ y := le_trans (le_max_left _ _) (h0 x hx)
  have hyC : C * B ^ 2 ≤ y := le_trans (le_max_right _ _) (h0 x hx)
  have hy0 : 0 < y := by linarith
  have e21 : x ^ (ε / 5 + ε / 100) = y ^ 21 := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0]
    congr 1; push_cast; ring
  have e100 : x ^ ε = y ^ 100 := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0]
    congr 1; push_cast; field_simp
  have hlogy : Real.log y ≤ y := Real.log_le_self hy0.le
  have hlog : Real.log x ≤ 100 / ε * y := by
    have h1 : Real.log y = ε / 100 * Real.log x := by rw [hy, Real.log_rpow (by linarith)]
    have h3 : Real.log x = 100 / ε * Real.log y := by rw [h1]; field_simp
    rw [h3]
    exact mul_le_mul_of_nonneg_left hlogy (by positivity)
  have hl4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hy21 : y ≤ y ^ 21 := by
    calc y = y ^ 1 := (pow_one y).symm
      _ ≤ y ^ 21 := pow_le_pow_right₀ hy1 (by norm_num)
  have h121 : 1 ≤ y ^ 21 := one_le_pow₀ hy1
  have h1100 : 1 ≤ y ^ 100 := one_le_pow₀ hy1
  have h21100 : y ^ 21 ≤ y ^ 100 := pow_le_pow_right₀ hy1 (by norm_num)
  have h221 : y ^ 2 ≤ y ^ 21 := pow_le_pow_right₀ hy1 (by norm_num)
  rw [e21] at hωb ht
  rw [e100] at hωb
  have hLam : Real.log 4 + 2 * (2 + 8 * ε + ε / 100) * Real.log x + 2 * y ^ 21 ≤ (5 + a) * y ^ 21 := by
    have h1 : 2 * (2 + 8 * ε + ε / 100) * Real.log x ≤ a * y := by
      rw [ha, mul_assoc (2 * (2 + 8 * ε + ε / 100))]
      exact mul_le_mul_of_nonneg_left hlog (by positivity)
    have h2 : a * y ≤ a * y ^ 21 := mul_le_mul_of_nonneg_left hy21 ha0
    linarith
  have hl2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hωE : ω ≤ E * y ^ 100 := by
    have h1 : ω * (1 / 2) ≤ ω * Real.log 2 := mul_le_mul_of_nonneg_left hl2 hω
    have h2 : κ ≤ |κ| * y ^ 100 := le_trans (le_abs_self κ) (le_mul_of_one_le_right (abs_nonneg κ) h1100)
    have h3 : (5 + a) * y ^ 21 ≤ (5 + a) * y ^ 100 := mul_le_mul_of_nonneg_left h21100 (by positivity)
    rw [hE]
    linarith
  have hlogω : Real.log (2 * (ω + 3)) ≤ G * y := by
    have h1 : 2 * (ω + 3) ≤ F * y ^ 100 := by rw [hF]; linarith
    have h2 := Real.log_le_log (by positivity : (0 : ℝ) < 2 * (ω + 3)) h1
    rw [Real.log_mul hF0.ne' (by positivity), Real.log_pow] at h2
    have h3 : Real.log F ≤ |Real.log F| * y := le_trans (le_abs_self _) (le_mul_of_one_le_right (abs_nonneg _) hy1)
    rw [hG]
    push_cast at h2
    linarith
  have hlogω0 : 0 ≤ Real.log (2 * (ω + 3)) := Real.log_nonneg (by linarith)
  have hr : C₁ * Real.log (2 * (ω + 3)) ^ 2 ≤ C₁ * G ^ 2 * y ^ 21 := by
    have h1 : Real.log (2 * (ω + 3)) ^ 2 ≤ (G * y) ^ 2 := pow_le_pow_left₀ hlogω0 hlogω 2
    have h2 : (G * y) ^ 2 = G ^ 2 * y ^ 2 := by ring
    have h3 : G ^ 2 * y ^ 2 ≤ G ^ 2 * y ^ 21 := mul_le_mul_of_nonneg_left h221 (by positivity)
    calc C₁ * Real.log (2 * (ω + 3)) ^ 2 ≤ C₁ * (G ^ 2 * y ^ 21) :=
          mul_le_mul_of_nonneg_left (by linarith) hC₁.le
      _ = C₁ * G ^ 2 * y ^ 21 := by ring
  have hT : t ≤ B * y ^ 21 := by rw [hB]; linarith
  have hsq : t ^ 2 ≤ (B * y ^ 21) ^ 2 := pow_le_pow_left₀ ht0 hT 2
  rw [e100]
  calc C * t ^ 2 ≤ C * (B * y ^ 21) ^ 2 := mul_le_mul_of_nonneg_left hsq hC.le
    _ = (C * B ^ 2) * y ^ 42 := by ring
    _ ≤ y * y ^ 42 := mul_le_mul_of_nonneg_right hyC (by positivity)
    _ = y ^ 43 := by ring
    _ ≤ y ^ 100 := pow_le_pow_right₀ hy1 (by norm_num)

/- English proof (translation)
Establish `heps : 0 < eps`. Take `⟨i0⟩` from `Fm.Ix_zero`. Use `(Fm.L 0 i0).sc.eps_pos` as an intermediate fact. Rewrite `this` using `[Fm.L_eps]`. Then use the resulting hypothesis. Take `⟨C, hC, h9⟩` from `auxiliary_prime_size_bound`.

Take `⟨C₁, hC₁, hr'⟩` from `log_rPr_le`. Use `set K0 : ℝ := Fm.PK.getD 21 0 with hK0`. Establish `hK : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), (Fm.params x hx i).CccK = K0`. Introduce `x hx i`. Rewrite using `[hK0, ← Fm.params_K x hx i]`.

Both sides reduce to the same expression. Take `⟨x0, h0⟩` from `numeric_log_square_estimate eps heps C C₁ (Real.log K0) hC hC₁`. Establish `hez : 0 < Fm.ez` using `div_pos heps (lt_of_lt_of_le one_pos Fm.one_le_J)`. Take `⟨x2, h2⟩` from `Filter.eventually_atTop.1 ((tendsto_rpow_atTop (by positivity : 0 < Fm.ez / 6)).eventually_ge_atTop (Real.log K0))`. Use `⟨max x0 x2, fun x hx hx1 i => ?_⟩` and prove the remaining obligations.

Establish `hxa : x0 ≤ x` using `le_trans (le_max_left _ _) hx`. Establish `hxb : x2 ≤ x` using `le_trans (le_max_right _ _) hx`. Establish `hLx` using `Fm.L_x x i hx1`. Establish `hLe` using `Fm.L_eps x i`. Establish `hS` using `Fm.sizes x hx1 i`.

Establish `hone : 1 < x` using `by rw [← hLx]; exact (Fm.L x i).sc.one_lt_alt`. Establish `hLL : (Fm.L x i).sc.L = x ^ eps` using `by unfold Scale.L; rw [hLx, hLe]`. Use `h9 (Fm.D x i) (Fm.L x i) ?_ ?_` and prove the remaining obligations. Take `⟨-, -, -, -, -, -, hQD, -⟩` from `hS`. Establish `hq1` using `hQD.1`.

Rewrite `hq1` using `[hLx, Fm.L_ez x i]`. Establish `hq0 : (0 : ℝ) < ((Fm.D x i).host.q : ℝ)` using `by exact_mod_cast (Fm.D x i).host.hyp.1.pos`. Establish `hd0 : (0 : ℝ) < ((Fm.D x i).host.d : ℝ)` using `by exact_mod_cast (Fm.D x i).host.hyp.2.1.pos`. Establish `hKpos : 0 < K0` using `by rw [← hK x hx1 i]; exact (Fm.params x hx1 i).CccK_pos`. Establish `hKq : K0 ≤ ((Fm.D x i).host.q : ℝ)` using `(Real.log_le_log_iff hKpos hq0).1 (le_trans (h2 x hxb) hq1)`.

Establish `hN` using `(Fm.params x hx1 i).ccK_le`. Rewrite `hN` using `[hK x hx1 i]`. Establish `hr : (1 : ℝ) ≤ (AbsolutelyIrreducibleSpan.rPr (Fm.D x i) : ℝ)` using `by exact_mod_cast (AbsolutelyIrreducibleSpan.rPr_mem (Fm.D x i)).1.one_lt.le`. Establish `hn : (1 : ℝ) ≤ ((Fm.D x i).host.QS : ℝ)` using `by exact_mod_cast (Fm.D x i).host.QS_pos`. Establish `h3 : (Ideal.absNorm (Fm.D x i).host.ccK : ℝ) ≤ ((AbsolutelyIrreducibleSpan.rPr (Fm.D x i) * LevelStarExponents.condE (Fm.D x i) : ℕ) : ℝ)`.

Unfold `LevelStarExponents.condE`. Use `push_cast`. Establish `h4 : K0 * ((Fm.D x i).host.d : ℝ) ≤ ((Fm.D x i).host.q : ℝ) * (Fm.D x i).host.d` using `mul_le_mul_of_nonneg_right hKq hd0.le`. Establish `h5 : ((Fm.D x i).host.q : ℝ) * (Fm.D x i).host.d ≤ (AbsolutelyIrreducibleSpan.rPr (Fm.D x i) : ℝ) * (((Fm.D x i).host.QS : ℝ) * (Fm.D x i).host.q * (Fm.D x i).host.d)`. Establish `h6 : (1 : ℝ) ≤ (AbsolutelyIrreducibleSpan.rPr (Fm.D x i) : ℝ) * ((Fm.D x i).host.QS : ℝ)` using `by nlinarith`.

Establish `h7 : 0 < ((Fm.D x i).host.q : ℝ) * (Fm.D x i).host.d` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `h3` after adjusting the coercions. Establish `hc` using `log_cond_le (Fm.L x i) hS`.

Establish `hz` using `log_zPr_le (Fm.L x i) (Fm.params x hx1 i) hS`. Rewrite `hc` using `[hLx, hLe]`. Rewrite `hz` using `[hLL, hLx, hLe, hK x hx1 i]`. Establish `hω` using `card_pf_le (zPr (Fm.D x i)) (zPr_pos (Fm.D x i))`. Establish `hr0 : (0 : ℝ) < (AbsolutelyIrreducibleSpan.rPr (Fm.D x i) : ℝ)` using `by exact_mod_cast (AbsolutelyIrreducibleSpan.rPr_mem (Fm.D x i)).1.pos`.

Establish `hc0 : (0 : ℝ) < (LevelStarExponents.condE (Fm.D x i) : ℝ)` using `by exact_mod_cast AbsolutelyIrreducibleSpan.condE_pos (Fm.D x i)`. Establish `hM : Real.log ((AbsolutelyIrreducibleSpan.rPr (Fm.D x i) * LevelStarExponents.condE (Fm.D x i) : ℕ) : ℝ) = Real.log (AbsolutelyIrreducibleSpan.rPr (Fm.D x i) : ℝ) + Real.log (LevelStarExponents.condE (Fm.D x i) : ℝ)`. Use `push_cast`. Conclude with `Real.log_mul hr0.ne' hc0.ne'`. Establish `hM1 : (1 : ℝ) ≤ ((AbsolutelyIrreducibleSpan.rPr (Fm.D x i) * LevelStarExponents.condE (Fm.D x i) : ℕ) : ℝ)`.

Establish `: 1 ≤ AbsolutelyIrreducibleSpan.rPr (Fm.D x i) * LevelStarExponents.condE (Fm.D x i)` using `Nat.succ_le_of_lt (Nat.mul_pos (AbsolutelyIrreducibleSpan.rPr_mem (Fm.D x i)).1.pos (AbsolutelyIrreducibleSpan.condE_pos (Fm.D x i)))`. Conclude with `this` after adjusting the coercions. Rewrite using `[hLL]`. Use `h0 x hxa hone ((zPr (Fm.D x i)).primeFactors.card : ℝ) _ (Nat.cast_nonneg _) (Real.log_nonneg hM1) (le_trans hω hz) ?_` and prove the remaining obligations. Rewrite using `[hM]`.

Conclude with `add_le_add (hr' (Fm.D x i)) hc`.
-/
theorem family_auxiliary_prime_size {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (_ : Fm.x1 < x) (i : Fm.Ix x), AbsolutelyIrreducibleSpan.adm9 (Fm.D x i) (Fm.L x i) := by
  have heps : 0 < eps := by
    obtain ⟨i0⟩ := Fm.Ix_zero
    have := (Fm.L 0 i0).sc.eps_pos
    rwa [Fm.L_eps] at this
  obtain ⟨C, hC, h9⟩ := auxiliary_prime_size_bound
  obtain ⟨C₁, hC₁, hr'⟩ := log_rPr_le
  set K0 : ℝ := Fm.PK.getD 21 0 with hK0
  have hK : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), (Fm.params x hx i).CccK = K0 := by
    intro x hx i
    rw [hK0, ← Fm.params_K x hx i]
    rfl
  obtain ⟨x0, h0⟩ := numeric_log_square_estimate eps heps C C₁ (Real.log K0) hC hC₁
  have hez : 0 < Fm.ez := div_pos heps (lt_of_lt_of_le one_pos Fm.one_le_J)
  obtain ⟨x2, h2⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop (by positivity : 0 < Fm.ez / 6)).eventually_ge_atTop (Real.log K0))
  refine ⟨max x0 x2, fun x hx hx1 i => ?_⟩
  have hxa : x0 ≤ x := le_trans (le_max_left _ _) hx
  have hxb : x2 ≤ x := le_trans (le_max_right _ _) hx
  have hLx := Fm.L_x x i hx1
  have hLe := Fm.L_eps x i
  have hS := Fm.sizes x hx1 i
  have hone : 1 < x := by rw [← hLx]; exact (Fm.L x i).sc.one_lt_alt
  have hLL : (Fm.L x i).sc.L = x ^ eps := by unfold Scale.L; rw [hLx, hLe]
  refine h9 (Fm.D x i) (Fm.L x i) ?_ ?_
  · obtain ⟨-, -, -, -, -, -, hQD, -⟩ := hS
    have hq1 := hQD.1
    rw [hLx, Fm.L_ez x i] at hq1
    have hq0 : (0 : ℝ) < ((Fm.D x i).host.q : ℝ) := by exact_mod_cast (Fm.D x i).host.hyp.1.pos
    have hd0 : (0 : ℝ) < ((Fm.D x i).host.d : ℝ) := by exact_mod_cast (Fm.D x i).host.hyp.2.1.pos
    have hKpos : 0 < K0 := by rw [← hK x hx1 i]; exact (Fm.params x hx1 i).CccK_pos
    have hKq : K0 ≤ ((Fm.D x i).host.q : ℝ) :=
      (Real.log_le_log_iff hKpos hq0).1 (le_trans (h2 x hxb) hq1)
    have hN := (Fm.params x hx1 i).ccK_le
    rw [hK x hx1 i] at hN
    have hr : (1 : ℝ) ≤ (AbsolutelyIrreducibleSpan.rPr (Fm.D x i) : ℝ) := by exact_mod_cast (AbsolutelyIrreducibleSpan.rPr_mem (Fm.D x i)).1.one_lt.le
    have hn : (1 : ℝ) ≤ ((Fm.D x i).host.QS : ℝ) := by exact_mod_cast (Fm.D x i).host.QS_pos
    have h3 : (Ideal.absNorm (Fm.D x i).host.ccK : ℝ) ≤
        ((AbsolutelyIrreducibleSpan.rPr (Fm.D x i) * LevelStarExponents.condE (Fm.D x i) : ℕ) : ℝ) := by
      unfold LevelStarExponents.condE
      push_cast
      have h4 : K0 * ((Fm.D x i).host.d : ℝ) ≤ ((Fm.D x i).host.q : ℝ) * (Fm.D x i).host.d :=
        mul_le_mul_of_nonneg_right hKq hd0.le
      have h5 : ((Fm.D x i).host.q : ℝ) * (Fm.D x i).host.d ≤
          (AbsolutelyIrreducibleSpan.rPr (Fm.D x i) : ℝ) * (((Fm.D x i).host.QS : ℝ) * (Fm.D x i).host.q * (Fm.D x i).host.d) := by
        have h6 : (1 : ℝ) ≤ (AbsolutelyIrreducibleSpan.rPr (Fm.D x i) : ℝ) * ((Fm.D x i).host.QS : ℝ) := by nlinarith
        have h7 : 0 < ((Fm.D x i).host.q : ℝ) * (Fm.D x i).host.d := by positivity
        nlinarith
      linarith
    exact_mod_cast h3
  · have hc := log_cond_le (Fm.L x i) hS
    have hz := log_zPr_le (Fm.L x i) (Fm.params x hx1 i) hS
    rw [hLx, hLe] at hc
    rw [hLL, hLx, hLe, hK x hx1 i] at hz
    have hω := card_pf_le (zPr (Fm.D x i)) (zPr_pos (Fm.D x i))
    have hr0 : (0 : ℝ) < (AbsolutelyIrreducibleSpan.rPr (Fm.D x i) : ℝ) := by exact_mod_cast (AbsolutelyIrreducibleSpan.rPr_mem (Fm.D x i)).1.pos
    have hc0 : (0 : ℝ) < (LevelStarExponents.condE (Fm.D x i) : ℝ) := by exact_mod_cast AbsolutelyIrreducibleSpan.condE_pos (Fm.D x i)
    have hM : Real.log ((AbsolutelyIrreducibleSpan.rPr (Fm.D x i) * LevelStarExponents.condE (Fm.D x i) : ℕ) : ℝ) =
        Real.log (AbsolutelyIrreducibleSpan.rPr (Fm.D x i) : ℝ) + Real.log (LevelStarExponents.condE (Fm.D x i) : ℝ) := by
      push_cast
      exact Real.log_mul hr0.ne' hc0.ne'
    have hM1 : (1 : ℝ) ≤ ((AbsolutelyIrreducibleSpan.rPr (Fm.D x i) * LevelStarExponents.condE (Fm.D x i) : ℕ) : ℝ) := by
      have : 1 ≤ AbsolutelyIrreducibleSpan.rPr (Fm.D x i) * LevelStarExponents.condE (Fm.D x i) :=
        Nat.succ_le_of_lt (Nat.mul_pos (AbsolutelyIrreducibleSpan.rPr_mem (Fm.D x i)).1.pos (AbsolutelyIrreducibleSpan.condE_pos (Fm.D x i)))
      exact_mod_cast this
    rw [hLL]
    refine h0 x hxa hone ((zPr (Fm.D x i)).primeFactors.card : ℝ) _ (Nat.cast_nonneg _) (Real.log_nonneg hM1)
      (le_trans hω hz) ?_
    rw [hM]
    exact add_le_add (hr' (Fm.D x i)) hc

end Formalism.MainNotions.J

end
