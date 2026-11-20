import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.AdmissibleSignatures
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NumericalConditionsTheoremTLargePrimeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxFrobeniusOrbitLengthDiffBoundsZmodStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowSmulDescentPhiMemLatticeOfOrbitBoundStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowSmulPhiMemLatticeOfMemFiltrationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLpowEisensteinPowTwistedDecompStatement
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.ZetaDenominator

/- English proof (translation)
Introduce `O K _ _ _ _ _ l e a ι _ _ _ _ _ _ _ N η H Sig U hA D hT y' hy' m hm hMon`. Use `haveI : CompleteSpace K := by haveI := TameDescentExponentData.finite (K := K) (l := l) (e := e) (a := a)`. Conclude with `FiniteDimensional.complete ℚ_[l] K`. Establish `hl : l.Prime` using `Fact.out`. Establish `ha : 1 ≤ a` using `NeZero.one_le`.

Take `⟨hr1, hrN, hrper⟩` from `GlobalTheory.T.maxFrobeniusOrbitLengthDiff_bounds_zmod l e a hl ha (TameDescentExponentData.succ_eq (K := K)) Sig N hA.frob_mem hA.zero_mem_Sig hA.card_Sig hA.two_le`. Take `⟨-, n2, n3, -, -, n6⟩` from `GlobalTheory.T.numerical_conditions_theorem_T_large_prime l H N η (maxPeriod l Sig) hA.two_le hA.one_le hA.lt hrN hA.large`. Establish `hl2 : l ≠ 2` using `by have := hA.lt; have := hA.one_le; omega`. Establish `hφm` using `GlobalTheory.T.prime_pow_smul_descent_phi_mem_lattice_of_orbit_bound O K l e a ι η H D (maxPeriod l Sig) hr1 (fun τ c hc => hrper c (hT.chars_subset τ hc)) n6 hl2 m hm`. Take `⟨P0, hP0, F0, hF0, hQF, hdec⟩` from `GlobalTheory.T.breuilKisin_lpow_eisensteinPow_twisted_decomp O K l e a ι η H D (η * (maxPeriod l Sig + 1)) hA.one_le hA.lt (by have := hA.one_le; omega) (by omega) y' hy' m hm hφm`.

Use `show (l : K) ^ (η * (maxPeriod l Sig + 1)) • D.zeta (y' + D.phi m) ∈ D.MM`. Use `set c₁ := η * (maxPeriod l Sig + 1)`. Use `set y := y' + D.phi m`. Use `set w := E K l e • D.zeta y - D.EN y with hw_def`. Establish `hw : w ∈ D.Man`.

Establish `h : D.EN y - E K l e • D.zeta y ∈ D.Man` using `(D.cls_eq_zero_iff).1 (by rw [← PhiMod.Mon_apply]; exact hMon)`. Use `D.Man.neg_mem h` as an intermediate fact. Rewrite `this` using `[neg_sub]`. Then use the resulting hypothesis. Take `⟨c, hc, hcE⟩` from `exists_mul_frob_E (O := O) (K := K) l e`. Establish `hζ : D.zeta y = c • D.phi w`.

Establish `h1 : w = E K l e • (D.zeta y - D.conn y)` using `by simp only [hw_def, PhiMod.EN_apply, smul_sub]`. Rewrite using `[h1, PhiMod.phi_smul, smul_smul, hcE]`. Use `conv_lhs => rw [PhiMod.zeta_eq, PhiMod.lphi_apply]`. Simplify using `only [Nat.cast_smul_eq_nsmul]`. Establish `hE1 : E K l e ^ (2 * H) * Ezpow K l e (-(2 * H : ℤ)) = 1`.

Use `E_pow_mul_Ezpow_neg (K := K) l e (2 * H)` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`. Use `set Q := Ezpow K l e (-(2 * H : ℤ)) • (((l : K) ^ (3 * H))⁻¹ • F0) with hQ_def`. Use `set X0 := Ezpow K l e (-(2 * H : ℤ)) • P0 with hX0_def`.

Establish `hsplit : (l : K) ^ c₁ • w = X0 + Q`. Establish `h : (l : K) ^ c₁ • w = Ezpow K l e (-(2 * H : ℤ)) • (E K l e ^ (2 * H) • ((l : K) ^ c₁ • w))`. Rewrite using `[smul_smul, mul_comm, hE1, one_smul]`. Rewrite using `[h, smul_comm (E K l e ^ (2 * H)) ((l : K) ^ c₁) w, hdec, smul_add]`. Establish `hQ : Q ∈ D.Man`.

Rewrite using `[hQ_def, smul_comm]`. Conclude with `D.Man.smul_mem _ hQF`. Establish `hX0 : X0 ∈ D.Man`. Establish `: X0 = (l : K) ^ c₁ • w - Q` using `by rw [hsplit, add_sub_cancel_right]`. Rewrite using `[this]`.

Conclude with `D.Man.sub_mem (D.Man.smul_mem _ hw) hQ`. Establish `hX0E : X0 ∈ D.EM (2 * H + η)`. Rewrite using `[mem_divE, hX0_def, smul_smul, pow_add, mul_right_comm, hE1, one_mul]`. Conclude with `D.upper _ hP0`. Establish `hX0M : X0 ∈ D.M` using `PhiMod.mem_M_of_mem_Man _ hX0E hX0`.

Establish `hφX0 : D.phi X0 ∈ D.MM` using `PhiMod.ext_mono _ (A_le_S l e) (D.phi_mem_L hX0M)`. Take `⟨v', hv', hv'eq⟩` from `GlobalTheory.T.prime_pow_smul_phi_mem_lattice_of_mem_filtration O K l e a ι η H D (10 * H) (by omega) F0 hF0`. Establish `hl0 : (l : K) ≠ 0` using `l_ne_zero (K := K) l`. Establish `hF : D.phi F0 = (l : K) ^ (3 * H) • ((l : K) ^ (2 * H) • ((l : K) ^ (5 * H - η) • v'))`. Apply `smul_right_injective _ (pow_ne_zero η hl0)` to reduce the goal to its premises.

Rewrite `hv'eq` using `[show 10 * H = η + (3 * H + (2 * H + (5 * H - η))) by have := hA.lt; omega]`. Simplify `hv'eq` using `only [pow_add, mul_smul]`. Establish `hfr : (l : K⟦X⟧) ^ (2 * H) * frob K l (Ezpow K l e (-(2 * H : ℤ))) = c ^ (2 * H)`. Rewrite using `[← hcE, mul_pow, ← map_pow, mul_assoc, ← map_mul, hE1, map_one, mul_one]`. Establish `hcast : ∀ (n : ℕ) (x : Vec K a ι), (l : K) ^ n • x = (l : K⟦X⟧) ^ n • x`.

Introduce `n x`. Rewrite using `[← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]`. Establish `hφQ' : D.phi Q = c ^ (2 * H) • ((l : K) ^ (5 * H - η) • v')`. Rewrite using `[hQ_def, PhiMod.phi_smul, map_smul, hF, inv_smul_smul₀ (pow_ne_zero _ hl0), hcast (2 * H), smul_smul, mul_comm (frob K l _), hfr]`. Establish `hφQ : D.phi Q ∈ D.MM`.

Rewrite using `[hφQ']`. Use `D.MM.smul_mem ⟨c ^ (2 * H), pow_mem hc _⟩ ?_` and prove the remaining obligations. Rewrite using `[← Nat.cast_pow, Nat.cast_smul_eq_nsmul]`. Conclude with `nsmul_mem hv' _`. Establish `key : (l : K) ^ c₁ • D.zeta y = c • (D.phi X0 + D.phi Q)`.

Rewrite using `[← map_add, ← hsplit, map_smul, hζ, smul_comm]`. Rewrite using `[key]`. Conclude with `D.MM.smul_mem ⟨c, hc⟩ (add_mem hφX0 hφQ)`.
-/
theorem zetaBound : GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.ZetaBound := by
  intro O K _ _ _ _ _ l e a ι _ _ _ _ _ _ _ N η H Sig U hA D hT y' hy' m hm hMon
  haveI : CompleteSpace K := by
    haveI := TameDescentExponentData.finite (K := K) (l := l) (e := e) (a := a)
    exact FiniteDimensional.complete ℚ_[l] K
  have hl : l.Prime := Fact.out
  have ha : 1 ≤ a := NeZero.one_le
  obtain ⟨hr1, hrN, hrper⟩ := GlobalTheory.T.maxFrobeniusOrbitLengthDiff_bounds_zmod l e a hl ha (TameDescentExponentData.succ_eq (K := K)) Sig N
    hA.frob_mem hA.zero_mem_Sig hA.card_Sig hA.two_le
  obtain ⟨-, n2, n3, -, -, n6⟩ := GlobalTheory.T.numerical_conditions_theorem_T_large_prime l H N η (maxPeriod l Sig) hA.two_le hA.one_le hA.lt hrN hA.large
  have hl2 : l ≠ 2 := by have := hA.lt; have := hA.one_le; omega
  have hφm := GlobalTheory.T.prime_pow_smul_descent_phi_mem_lattice_of_orbit_bound O K l e a ι η H D (maxPeriod l Sig) hr1
    (fun τ c hc => hrper c (hT.chars_subset τ hc)) n6 hl2 m hm
  obtain ⟨P0, hP0, F0, hF0, hQF, hdec⟩ := GlobalTheory.T.breuilKisin_lpow_eisensteinPow_twisted_decomp O K l e a ι η H D (η * (maxPeriod l Sig + 1)) hA.one_le hA.lt
    (by have := hA.one_le; omega) (by omega) y' hy' m hm hφm
  show (l : K) ^ (η * (maxPeriod l Sig + 1)) • D.zeta (y' + D.phi m) ∈ D.MM
  set c₁ := η * (maxPeriod l Sig + 1)
  set y := y' + D.phi m
  set w := E K l e • D.zeta y - D.EN y with hw_def
  have hw : w ∈ D.Man := by
    have h : D.EN y - E K l e • D.zeta y ∈ D.Man := (D.cls_eq_zero_iff).1 (by rw [← PhiMod.Mon_apply]; exact hMon)
    have := D.Man.neg_mem h
    rwa [neg_sub] at this
  obtain ⟨c, hc, hcE⟩ := exists_mul_frob_E (O := O) (K := K) l e
  have hζ : D.zeta y = c • D.phi w := by
    have h1 : w = E K l e • (D.zeta y - D.conn y) := by simp only [hw_def, PhiMod.EN_apply, smul_sub]
    rw [h1, PhiMod.phi_smul, smul_smul, hcE]
    conv_lhs => rw [PhiMod.zeta_eq, PhiMod.lphi_apply]
    simp only [Nat.cast_smul_eq_nsmul]
  have hE1 : E K l e ^ (2 * H) * Ezpow K l e (-(2 * H : ℤ)) = 1 := by
    have := E_pow_mul_Ezpow_neg (K := K) l e (2 * H)
    push_cast at this
    exact this
  set Q := Ezpow K l e (-(2 * H : ℤ)) • (((l : K) ^ (3 * H))⁻¹ • F0) with hQ_def
  set X0 := Ezpow K l e (-(2 * H : ℤ)) • P0 with hX0_def
  have hsplit : (l : K) ^ c₁ • w = X0 + Q := by
    have h : (l : K) ^ c₁ • w = Ezpow K l e (-(2 * H : ℤ)) • (E K l e ^ (2 * H) • ((l : K) ^ c₁ • w)) := by
      rw [smul_smul, mul_comm, hE1, one_smul]
    rw [h, smul_comm (E K l e ^ (2 * H)) ((l : K) ^ c₁) w, hdec, smul_add]
  have hQ : Q ∈ D.Man := by
    rw [hQ_def, smul_comm]
    exact D.Man.smul_mem _ hQF
  have hX0 : X0 ∈ D.Man := by
    have : X0 = (l : K) ^ c₁ • w - Q := by rw [hsplit, add_sub_cancel_right]
    rw [this]
    exact D.Man.sub_mem (D.Man.smul_mem _ hw) hQ
  have hX0E : X0 ∈ D.EM (2 * H + η) := by
    rw [mem_divE, hX0_def, smul_smul, pow_add, mul_right_comm, hE1, one_mul]
    exact D.upper _ hP0
  have hX0M : X0 ∈ D.M := PhiMod.mem_M_of_mem_Man _ hX0E hX0
  have hφX0 : D.phi X0 ∈ D.MM := PhiMod.ext_mono _ (A_le_S l e) (D.phi_mem_L hX0M)
  obtain ⟨v', hv', hv'eq⟩ := GlobalTheory.T.prime_pow_smul_phi_mem_lattice_of_mem_filtration O K l e a ι η H D (10 * H) (by omega) F0 hF0
  have hl0 : (l : K) ≠ 0 := l_ne_zero (K := K) l
  have hF : D.phi F0 = (l : K) ^ (3 * H) • ((l : K) ^ (2 * H) • ((l : K) ^ (5 * H - η) • v')) := by
    apply smul_right_injective _ (pow_ne_zero η hl0)
    rw [show 10 * H = η + (3 * H + (2 * H + (5 * H - η))) by have := hA.lt; omega] at hv'eq
    simpa only [pow_add, mul_smul] using hv'eq
  have hfr : (l : K⟦X⟧) ^ (2 * H) * frob K l (Ezpow K l e (-(2 * H : ℤ))) = c ^ (2 * H) := by
    rw [← hcE, mul_pow, ← map_pow, mul_assoc, ← map_mul, hE1, map_one, mul_one]
  have hcast : ∀ (n : ℕ) (x : Vec K a ι), (l : K) ^ n • x = (l : K⟦X⟧) ^ n • x := by
    intro n x
    rw [← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  have hφQ' : D.phi Q = c ^ (2 * H) • ((l : K) ^ (5 * H - η) • v') := by
    rw [hQ_def, PhiMod.phi_smul, map_smul, hF, inv_smul_smul₀ (pow_ne_zero _ hl0), hcast (2 * H), smul_smul, mul_comm (frob K l _), hfr]
  have hφQ : D.phi Q ∈ D.MM := by
    rw [hφQ']
    refine D.MM.smul_mem ⟨c ^ (2 * H), pow_mem hc _⟩ ?_
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    exact nsmul_mem hv' _
  have key : (l : K) ^ c₁ • D.zeta y = c • (D.phi X0 + D.phi Q) := by
    rw [← map_add, ← hsplit, map_smul, hζ, smul_comm]
  rw [key]
  exact D.MM.smul_mem ⟨c, hc⟩ (add_mem hφX0 hφQ)

end GlobalTheory.ZetaDenominator
