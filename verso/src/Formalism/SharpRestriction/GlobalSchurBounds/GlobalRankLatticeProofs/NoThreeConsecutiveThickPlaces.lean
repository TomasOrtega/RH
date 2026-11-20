import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.SecondPropositionEveryLocalisation
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts

noncomputable section

namespace Formalism.MainNotions.UnusedSlot33

open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.TwoAdicCyclotomicDecomposition Ideal
open Formalism.MainNotions.UnusedSlot33.SlopeTestRemainingChoices

def InertPart (D : D7) : Prop :=
  ∀ φ₀ : G0, (φ₀ = c0 ∨ φ₀ = sgc0) → ∀ h : HH D,
    (∀ p : ℕ, p.Prime → (span {(p : ℤ)}).ramificationIdxIn (𝓞 D.host.E) = 1 →
      frob D p = gOf D φ₀ h →
      ∀ 𝔭 : Ideal (𝓞 D.host.F), 𝔭.IsPrime → 𝔭.LiesOver (span {(p : ℤ)}) →
        (Inert D 𝔭 ↔ φ₀ = c0 ∧ Odd (addOrderOf h)))

/- English proof (translation)
Use `show φ.chD (φ.tau1 t) = 1`. Both sides reduce to the same expression.
-/
theorem tau_one_mem_orbit_set (φ : Formalism.HC.Frame) (t : φ.A) : φ.tau1 t ∈ φ.Psi := by
  show φ.chD (φ.tau1 t) = 1
  rfl

/- English proof (translation)
Break down `Int.units_eq_one_or x with hx | hx` into its components or cases. Conclude with `absurd hx h`. Conclude with `hx`.
-/
private theorem neg_one_of_ne {x : ℤˣ} (h : x ≠ 1) : x = -1 := by
  rcases Int.units_eq_one_or x with hx | hx
  · exact absurd hx h
  · exact hx

/- English proof (translation)
Establish `key : ∀ (y : R.GG), (Formalism.HC.Frame.placeOf y).1.1 = -1 → (Formalism.HC.Frame.placeOf (φ * y)).1.1 = -1 → φ.1.1 = -1`. Introduce `y h0 h1`. Establish `hφ2 : φ.1.2 = -1` using `neg_one_of_ne hφ`. Simplify using `only [Formalism.HC.Frame.placeOf] at h0 h1`. Break down `Int.units_eq_one_or y.1.2 with hy | hy` into its components or cases.

Rewrite `h0` using `[if_pos hy]`. Establish `hm : (φ * y).1.2 = -1`. Simplify using `[Prod.fst_mul, Prod.snd_mul, hφ2, hy]`. Rewrite `h1` using `[if_neg (by rw [hm]; decide)]`. Simplify `h1` using `[Formalism.HC.Frame.cc, c0, Prod.fst_mul, Prod.snd_mul, h0]`.

Rewrite `h0` using `[if_neg (by rw [hy]; decide)]`. Establish `hm : (φ * y).1.2 = 1`. Simplify using `[Prod.fst_mul, Prod.snd_mul, hφ2, hy]`. Rewrite `h1` using `[if_pos hm]`. Establish `h0' : y.1.1 = 1`.

Simplify `h0` using `[Formalism.HC.Frame.cc, c0, Prod.fst_mul, Prod.snd_mul]`. Simplify `h1` using `[Prod.fst_mul, h0']`. Establish `hφ2 : φ.1.2 = -1` using `neg_one_of_ne hφ`. Take `⟨s1, hs1, e1⟩` from `h0`. Take `⟨s2, hs2, e2⟩` from `h1`.

Take `⟨s3, hs3, e3⟩` from `h2`. Establish `hφ1 : φ.1.1 = -1` using `key (φ ^ i * τ) (by rw [e1]; rfl) (by rw [← mul_assoc, ← pow_succ', e2]; rfl)`. Establish `E : ∀ (k s : ℕ), Formalism.HC.Frame.placeOf (φ ^ k * τ) = R.tau2 (R.dig s + u0) → k • R.iotaInv φ.2 + R.iotaInv τ.2 = R.dig s + u0`. Introduce `k s hk`. Establish `this : R.iotaInv (Formalism.HC.Frame.placeOf (φ ^ k * τ)).2 = R.iotaInv (R.tau2 (R.dig s + u0)).2`.

Rewrite using `[hk]`. Rewrite `this` using `[Formalism.HC.Frame.placeOf_snd, Prod.snd_mul, Prod.pow_snd, Formalism.HC.Frame.iotaInv_mul, Formalism.HC.Frame.iotaInv_pow]`. Express the relevant statement in the definitionally equal form `_ = R.iotaInv (R.iota _) at this`. Rewrite `this` using `[Formalism.HC.Frame.iotaInv_iota]`. Conclude with `this`.

Establish `E1` using `E i s1 e1`. Establish `E2` using `E (i + 1) s2 e2`. Establish `E3` using `E (i + 2) s3 e3`. Use `set x := R.iotaInv φ.2 with hxdef`. Use `set T0 := R.iotaInv τ.2`.

Establish `hx1 : R.dig s2 - R.dig s1 = x`. Establish `a : R.dig s2 = ((i + 1) • x + T0) - u0` using `by rw [E2]; abel`. Establish `b : R.dig s1 = (i • x + T0) - u0` using `by rw [E1]; abel`. Rewrite using `[a, b, succ_nsmul]`. Normalize the expressions using the abelian group laws.

Establish `hx2 : R.dig s3 - R.dig s2 = x`. Establish `a : R.dig s3 = ((i + 2) • x + T0) - u0` using `by rw [E3]; abel`. Establish `b : R.dig s2 = ((i + 1) • x + T0) - u0` using `by rw [E2]; abel`. Rewrite using `[a, b, show i + 2 = (i + 1) + 1 from rfl, succ_nsmul]`. Normalize the expressions using the abelian group laws.

Establish `hx0 : x ≠ 0`. Introduce `h0`. Apply `hφc` to reduce the goal to its premises. Establish `h2 : φ.2 = 1` using `(R.iotaInv_eq_zero_iff _).1 h0`. Conclude with `Prod.ext (Prod.ext hφ1 hφ2) h2`.

Establish `hzero : ((s1 : ℤ) + s3 - s2 - s2) • R.a0 = 0`. Rewrite using `[sub_zsmul, sub_zsmul, add_zsmul, natCast_zsmul, natCast_zsmul, natCast_zsmul]`. Express the relevant statement in the definitionally equal form `R.dig s1 + R.dig s3 + -R.dig s2 + -R.dig s2 = 0`. Establish `: R.dig s1 + R.dig s3 + -R.dig s2 + -R.dig s2 = (R.dig s3 - R.dig s2) - (R.dig s2 - R.dig s1)` using `by abel`. Rewrite using `[this, hx1, hx2, sub_self]`.

Establish `hdvd : (R.n0 : ℤ) ∣ (s1 : ℤ) + s3 - s2 - s2` using `addOrderOf_dvd_iff_zsmul_eq_zero.2 hzero`. Establish `b1` using `hTr s1 hs1`. Establish `b2` using `hTr s2 hs2`. Establish `b3` using `hTr s3 hs3`. Establish `c1 : 12 * s1 ≤ 4 * L * s1` using `Nat.mul_le_mul_right s1 (by omega)`.

Establish `c2 : 12 * s2 ≤ 4 * L * s2` using `Nat.mul_le_mul_right s2 (by omega)`. Establish `c3 : 12 * s3 ≤ 4 * L * s3` using `Nat.mul_le_mul_right s3 (by omega)`. Establish `habs : |(s1 : ℤ) + s3 - s2 - s2| < R.n0` using `abs_lt.2 ⟨by omega, by omega⟩`. Establish `hrel : (s1 : ℤ) + s3 - s2 - s2 = 0` using `Int.eq_zero_of_abs_lt_dvd hdvd habs`. Establish `n12 : s1 ≠ s2`.

Introduce and unpack `rfl`. Conclude with `hx0 (by rw [← hx1, sub_self])`. Establish `n23 : s2 ≠ s3`. Introduce and unpack `rfl`. Conclude with `hx0 (by rw [← hx2, sub_self])`.

Establish `n13 : s1 ≠ s3`. Introduce and unpack `rfl`. Apply `n12` to reduce the goal to its premises. Use linear arithmetic over natural numbers and integers. Apply `hTn s1 hs1 s2 hs2 s3 hs3 n12 n13 n23 1 2 (by norm_num) (by norm_num; omega) (by norm_num) (by norm_num; omega) (by norm_num)` to reduce the goal to its premises.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem no_three (R : Formalism.HC.Frame) {L : ℕ} (T : Finset ℕ) (hTr : ∀ s ∈ T, 4 * L * s < R.n0)
    (hTn : NoRel T L) (u0 : R.A) (hL : 3 ≤ L) (φ : R.GG) (hφ : φ ∉ R.Psi) (hφc : φ ≠ R.cc)
    (τ : R.GG) (hτ : τ ∈ R.Psi) (i : ℕ)
    (h0 : ∃ s ∈ T, Formalism.HC.Frame.placeOf (φ ^ i * τ) = R.tau2 (R.dig s + u0))
    (h1 : ∃ s ∈ T, Formalism.HC.Frame.placeOf (φ ^ (i + 1) * τ) = R.tau2 (R.dig s + u0))
    (h2 : ∃ s ∈ T, Formalism.HC.Frame.placeOf (φ ^ (i + 2) * τ) = R.tau2 (R.dig s + u0)) : False := by
  have key : ∀ (y : R.GG), (Formalism.HC.Frame.placeOf y).1.1 = -1 →
      (Formalism.HC.Frame.placeOf (φ * y)).1.1 = -1 → φ.1.1 = -1 := by
    intro y h0 h1
    have hφ2 : φ.1.2 = -1 := neg_one_of_ne hφ
    simp only [Formalism.HC.Frame.placeOf] at h0 h1
    rcases Int.units_eq_one_or y.1.2 with hy | hy
    · rw [if_pos hy] at h0
      have hm : (φ * y).1.2 = -1 := by
        simp [Prod.fst_mul, Prod.snd_mul, hφ2, hy]
      rw [if_neg (by rw [hm]; decide)] at h1
      simpa [Formalism.HC.Frame.cc, c0, Prod.fst_mul, Prod.snd_mul, h0] using h1
    · rw [if_neg (by rw [hy]; decide)] at h0
      have hm : (φ * y).1.2 = 1 := by
        simp [Prod.fst_mul, Prod.snd_mul, hφ2, hy]
      rw [if_pos hm] at h1
      have h0' : y.1.1 = 1 := by
        simpa [Formalism.HC.Frame.cc, c0, Prod.fst_mul, Prod.snd_mul] using h0
      simpa [Prod.fst_mul, h0'] using h1
  have hφ2 : φ.1.2 = -1 := neg_one_of_ne hφ
  obtain ⟨s1, hs1, e1⟩ := h0
  obtain ⟨s2, hs2, e2⟩ := h1
  obtain ⟨s3, hs3, e3⟩ := h2
  have hφ1 : φ.1.1 = -1 := key (φ ^ i * τ) (by rw [e1]; rfl)
    (by rw [← mul_assoc, ← pow_succ', e2]; rfl)
  have E : ∀ (k s : ℕ), Formalism.HC.Frame.placeOf (φ ^ k * τ) = R.tau2 (R.dig s + u0) →
      k • R.iotaInv φ.2 + R.iotaInv τ.2 = R.dig s + u0 := by
    intro k s hk
    have this : R.iotaInv (Formalism.HC.Frame.placeOf (φ ^ k * τ)).2 = R.iotaInv (R.tau2 (R.dig s + u0)).2 := by
      rw [hk]
    rw [Formalism.HC.Frame.placeOf_snd, Prod.snd_mul, Prod.pow_snd, Formalism.HC.Frame.iotaInv_mul,
      Formalism.HC.Frame.iotaInv_pow] at this
    change _ = R.iotaInv (R.iota _) at this
    rw [Formalism.HC.Frame.iotaInv_iota] at this
    exact this
  have E1 := E i s1 e1
  have E2 := E (i + 1) s2 e2
  have E3 := E (i + 2) s3 e3
  set x := R.iotaInv φ.2 with hxdef
  set T0 := R.iotaInv τ.2
  have hx1 : R.dig s2 - R.dig s1 = x := by
    have a : R.dig s2 = ((i + 1) • x + T0) - u0 := by rw [E2]; abel
    have b : R.dig s1 = (i • x + T0) - u0 := by rw [E1]; abel
    rw [a, b, succ_nsmul]
    abel
  have hx2 : R.dig s3 - R.dig s2 = x := by
    have a : R.dig s3 = ((i + 2) • x + T0) - u0 := by rw [E3]; abel
    have b : R.dig s2 = ((i + 1) • x + T0) - u0 := by rw [E2]; abel
    rw [a, b, show i + 2 = (i + 1) + 1 from rfl, succ_nsmul]
    abel
  have hx0 : x ≠ 0 := by
    intro h0
    apply hφc
    have h2 : φ.2 = 1 := (R.iotaInv_eq_zero_iff _).1 h0
    exact Prod.ext (Prod.ext hφ1 hφ2) h2
  have hzero : ((s1 : ℤ) + s3 - s2 - s2) • R.a0 = 0 := by
    rw [sub_zsmul, sub_zsmul, add_zsmul, natCast_zsmul, natCast_zsmul, natCast_zsmul]
    change R.dig s1 + R.dig s3 + -R.dig s2 + -R.dig s2 = 0
    have : R.dig s1 + R.dig s3 + -R.dig s2 + -R.dig s2 =
        (R.dig s3 - R.dig s2) - (R.dig s2 - R.dig s1) := by abel
    rw [this, hx1, hx2, sub_self]
  have hdvd : (R.n0 : ℤ) ∣ (s1 : ℤ) + s3 - s2 - s2 := addOrderOf_dvd_iff_zsmul_eq_zero.2 hzero
  have b1 := hTr s1 hs1
  have b2 := hTr s2 hs2
  have b3 := hTr s3 hs3
  have c1 : 12 * s1 ≤ 4 * L * s1 := Nat.mul_le_mul_right s1 (by omega)
  have c2 : 12 * s2 ≤ 4 * L * s2 := Nat.mul_le_mul_right s2 (by omega)
  have c3 : 12 * s3 ≤ 4 * L * s3 := Nat.mul_le_mul_right s3 (by omega)
  have habs : |(s1 : ℤ) + s3 - s2 - s2| < R.n0 := abs_lt.2 ⟨by omega, by omega⟩
  have hrel : (s1 : ℤ) + s3 - s2 - s2 = 0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
  have n12 : s1 ≠ s2 := by
    rintro rfl
    exact hx0 (by rw [← hx1, sub_self])
  have n23 : s2 ≠ s3 := by
    rintro rfl
    exact hx0 (by rw [← hx2, sub_self])
  have n13 : s1 ≠ s3 := by
    rintro rfl
    apply n12
    omega
  apply hTn s1 hs1 s2 hs2 s3 hs3 n12 n13 n23 1 2 (by norm_num) (by norm_num; omega) (by norm_num)
    (by norm_num; omega) (by norm_num)
  linarith

/- English proof (translation)
Establish `h1 : addOrderOf (D.R.h h) ∣ addOrderOf h` using `addOrderOf_map_dvd D.R.h h`. Establish `h2 : addOrderOf (D.R.h h) ∣ 2 ^ D.R.e`. Use `D.R.orderOf_H_dvd (Additive.toMul (D.R.h h))` as an intermediate fact. Rewrite `this` using `[← addOrderOf_ofMul_eq_orderOf, ofMul_toMul]`. Then use the resulting hypothesis. Establish `h3 : addOrderOf (D.R.h h) ≠ 1`.

Introduce `hx`. Apply `hh` to reduce the goal to its premises. Use `addOrderOf_nsmul_eq_zero (D.R.h h)` as an intermediate fact. Rewrite `this` using `[hx, one_nsmul]`. Then use the resulting hypothesis. Take `⟨k, hk, hk'⟩` from `(Nat.dvd_prime_pow Nat.prime_two).1 h2`.

Establish `hk0 : k ≠ 0`. Introduce and unpack `rfl`. Conclude with `h3 (by simpa using hk')`. Rewrite using `[even_iff_two_dvd]`. Use `dvd_trans ?_ h1` and prove the remaining obligations.

Rewrite using `[hk']`. Conclude with `dvd_pow_self 2 hk0`.
-/
theorem even_addOrderOf_of_h_ne_zero (D : D7) {h : D.R.A} (hh : D.R.h h ≠ 0) : Even (addOrderOf h) := by
  have h1 : addOrderOf (D.R.h h) ∣ addOrderOf h := addOrderOf_map_dvd D.R.h h
  have h2 : addOrderOf (D.R.h h) ∣ 2 ^ D.R.e := by
    have := D.R.orderOf_H_dvd (Additive.toMul (D.R.h h))
    rwa [← addOrderOf_ofMul_eq_orderOf, ofMul_toMul] at this
  have h3 : addOrderOf (D.R.h h) ≠ 1 := by
    intro hx
    apply hh
    have := addOrderOf_nsmul_eq_zero (D.R.h h)
    rwa [hx, one_nsmul] at this
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact h3 (by simpa using hk')
  rw [even_iff_two_dvd]
  refine dvd_trans ?_ h1
  rw [hk']
  exact dvd_pow_self 2 hk0

/- English proof (translation)
Establish `hu : ∀ (u : ℤˣ) (k : ℤ), u ^ k = -1 → u = -1 ∧ Odd k`. Introduce `u k huk`. Break down `Int.units_eq_one_or u with rfl | rfl` into its components or cases. Rewrite `huk` using `[one_zpow]`. Conclude with `absurd huk (by decide)`.

Use `⟨rfl, ?_⟩` and prove the remaining obligations. Break down `Int.even_or_odd k with he | ho` into its components or cases. Rewrite `huk` using `[he.neg_one_zpow]`. Conclude with `absurd huk (by decide)`. Conclude with `ho`.

Establish `hc0sq : c0 ^ 2 = 1`. Apply the tactic sequence `ext <;> simp [c0]`. Rewrite using `[Subgroup.mem_zpowers_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk⟩`.

Establish `e1 : φ₀ ^ k = c0` using `congrArg Prod.fst hk`. Establish `e2 : (Multiplicative.ofAdd h) ^ k = 1` using `congrArg Prod.snd hk`. Establish `e2' : k • h = 0`. Use `congrArg Multiplicative.toAdd e2` as an intermediate fact. Simplify using `using this`.

Establish `a1` using `hu _ _ (congrArg Prod.fst e1)`. Establish `a2` using `hu _ _ (congrArg Prod.snd e1)`. Use `⟨Prod.ext a1.1 a2.1, ?_⟩` and prove the remaining obligations. Establish `hd : (addOrderOf h : ℤ) ∣ k` using `addOrderOf_dvd_iff_zsmul_eq_zero.2 e2'`. Establish `hd' : addOrderOf h ∣ k.natAbs` using `Int.natCast_dvd.1 hd`.

Conclude with `Odd.of_dvd_nat (Int.natAbs_odd.2 a1.2) hd'`. Introduce and unpack `⟨rfl, hodd⟩`. Use `⟨(addOrderOf h : ℤ), ?_⟩` and prove the remaining obligations. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `c0 ^ ((addOrderOf h : ℕ) : ℤ) = c0`.

Rewrite using `[zpow_natCast]`. Take `⟨m, hm⟩` from `hodd`. Rewrite using `[hm, pow_succ, pow_mul, hc0sq, one_pow, one_mul]`. Express the relevant statement in the definitionally equal form `(Multiplicative.ofAdd h) ^ ((addOrderOf h : ℕ) : ℤ) = 1`. Rewrite using `[zpow_natCast, ← ofAdd_nsmul, addOrderOf_nsmul_eq_zero, ofAdd_zero]`.
-/
theorem cc_mem_zpowers_gOf (D : D7) (φ₀ : G0) (h : HH D) :
    D.R.cc ∈ Subgroup.zpowers (gOf D φ₀ h) ↔ φ₀ = c0 ∧ Odd (addOrderOf h) := by
  have hu : ∀ (u : ℤˣ) (k : ℤ), u ^ k = -1 → u = -1 ∧ Odd k := by
    intro u k huk
    rcases Int.units_eq_one_or u with rfl | rfl
    · rw [one_zpow] at huk
      exact absurd huk (by decide)
    · refine ⟨rfl, ?_⟩
      rcases Int.even_or_odd k with he | ho
      · rw [he.neg_one_zpow] at huk
        exact absurd huk (by decide)
      · exact ho
  have hc0sq : c0 ^ 2 = 1 := by
    ext <;> simp [c0]
  rw [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    have e1 : φ₀ ^ k = c0 := congrArg Prod.fst hk
    have e2 : (Multiplicative.ofAdd h) ^ k = 1 := congrArg Prod.snd hk
    have e2' : k • h = 0 := by
      have := congrArg Multiplicative.toAdd e2
      simpa using this
    have a1 := hu _ _ (congrArg Prod.fst e1)
    have a2 := hu _ _ (congrArg Prod.snd e1)
    refine ⟨Prod.ext a1.1 a2.1, ?_⟩
    have hd : (addOrderOf h : ℤ) ∣ k := addOrderOf_dvd_iff_zsmul_eq_zero.2 e2'
    have hd' : addOrderOf h ∣ k.natAbs := Int.natCast_dvd.1 hd
    exact Odd.of_dvd_nat (Int.natAbs_odd.2 a1.2) hd'
  · rintro ⟨rfl, hodd⟩
    refine ⟨(addOrderOf h : ℤ), ?_⟩
    refine Prod.ext ?_ ?_
    · change c0 ^ ((addOrderOf h : ℕ) : ℤ) = c0
      rw [zpow_natCast]
      obtain ⟨m, hm⟩ := hodd
      rw [hm, pow_succ, pow_mul, hc0sq, one_pow, one_mul]
    · change (Multiplicative.ofAdd h) ^ ((addOrderOf h : ℕ) : ℤ) = 1
      rw [zpow_natCast, ← ofAdd_nsmul, addOrderOf_nsmul_eq_zero, ofAdd_zero]

/- English proof (translation)
Introduce `φ₀ hφ₀ h`. Establish `hg1 : (gOf D φ₀ h).1 = φ₀` using `rfl`. Establish `hsg : sgc0 = ((1 : ℤˣ), (-1 : ℤˣ))`. Apply the tactic sequence `ext <;> simp [sgc0, c0]`. Establish `hg : (gOf D φ₀ h).1 = c0 ∨ (gOf D φ₀ h).1 = ((1 : ℤˣ), (-1 : ℤˣ))`.

Rewrite using `[hg1, ← hsg]`. Conclude with `hφ₀`. Establish `hchg : D.R.chD (gOf D φ₀ h) = -1`. Express the relevant statement in the definitionally equal form `φ₀.2 = -1`. Break down `hφ₀ with rfl | rfl` into its components or cases.

Both sides reduce to the same expression. Rewrite using `[hsg]`. Establish `hcc : D.R.chD D.R.cc = -1` using `rfl`. Use `⟨?_, ?_, ?_, ?_, cc_mem_zpowers_gOf D φ₀ h, hI φ₀ hφ₀ h, ?_⟩` and prove the remaining obligations. Introduce `τ hτ i`.

Establish `hτ' : D.R.chD τ = 1` using `hτ`. Prove the components needed by the constructor for the conclusion. Introduce `he show D.R.chD _ = 1`. Rewrite using `[map_mul, map_pow, hchg, hτ', he.neg_one_pow, one_mul]`. Introduce `ho`.

Use `⟨D.R.cc * ((gOf D φ₀ h) ^ i * τ), ?_, ?_⟩` and prove the remaining obligations. Use `show D.R.chD _ = 1`. Rewrite using `[map_mul, map_mul, map_pow, hchg, hτ', ho.neg_one_pow, hcc]`. Evaluate the decidable proposition. Rewrite using `[← mul_assoc, cc_mul_cc, one_mul]`.

Introduce `t i`. Use `(Formalism.HC.Frame.hostOrbitsPlaces (φ := D.R.toFrame) _ hg (D.R.tau1 t) (tau_one_mem_orbit_set D.R.toFrame t) i).1` as an intermediate fact. Use `show D.R.iotaInv (Formalism.HC.Frame.placeOf _).2 = _`. Rewrite using `[this, Formalism.HC.Frame.iotaInv_mul, Formalism.HC.Frame.iotaInv_pow]`. Express the relevant statement in the definitionally equal form `i • D.R.iotaInv (D.R.iota h) + D.R.iotaInv (D.R.iota t) = t + i • h`.

Rewrite using `[Formalism.HC.Frame.iotaInv_iota, Formalism.HC.Frame.iotaInv_iota, add_comm]`. Introduce `hc t i`. Use `(Formalism.HC.Frame.hostOrbitsPlaces (φ := D.R.toFrame) _ hg (D.R.tau1 t) (tau_one_mem_orbit_set D.R.toFrame t) i).2.1 (by rw [hg1]; exact hc)` as an intermediate fact. Rewrite using `[this]`. Both sides reduce to the same expression.

Introduce `hs t i`. Use `(Formalism.HC.Frame.hostOrbitsPlaces (φ := D.R.toFrame) _ hg (D.R.tau1 t) (tau_one_mem_orbit_set D.R.toFrame t) i).2.2 (by rw [hg1, hs, hsg])` as an intermediate fact. Rewrite using `[this]`. Conclude with `mul_one _`. Introduce `hc τ hτ`.

Use `⟨?_, even_addOrderOf_of_h_ne_zero D⟩` and prove the remaining obligations. Rewrite using `[Formalism.HC.Frame.hostOrbitCount (φ := D.R.toFrame) _ (by rw [hg1]; exact hc) τ hτ]`. Conclude with `orderOf_ofAdd_eq_addOrderOf h`.
-/
theorem lemma_one_three_of_inert (D : D7) (hI : InertPart D) : PointsLemma D := by
  intro φ₀ hφ₀ h
  have hg1 : (gOf D φ₀ h).1 = φ₀ := rfl
  have hsg : sgc0 = ((1 : ℤˣ), (-1 : ℤˣ)) := by
    ext <;> simp [sgc0, c0]
  have hg : (gOf D φ₀ h).1 = c0 ∨ (gOf D φ₀ h).1 = ((1 : ℤˣ), (-1 : ℤˣ)) := by
    rw [hg1, ← hsg]
    exact hφ₀
  have hchg : D.R.chD (gOf D φ₀ h) = -1 := by
    change φ₀.2 = -1
    rcases hφ₀ with rfl | rfl
    · rfl
    · rw [hsg]
  have hcc : D.R.chD D.R.cc = -1 := rfl
  refine ⟨?_, ?_, ?_, ?_, cc_mem_zpowers_gOf D φ₀ h, hI φ₀ hφ₀ h, ?_⟩
  · intro τ hτ i
    have hτ' : D.R.chD τ = 1 := hτ
    constructor
    · intro he
      show D.R.chD _ = 1
      rw [map_mul, map_pow, hchg, hτ', he.neg_one_pow, one_mul]
    · intro ho
      refine ⟨D.R.cc * ((gOf D φ₀ h) ^ i * τ), ?_, ?_⟩
      · show D.R.chD _ = 1
        rw [map_mul, map_mul, map_pow, hchg, hτ', ho.neg_one_pow, hcc]
        decide
      · rw [← mul_assoc, cc_mul_cc, one_mul]
  · intro t i
    have := (Formalism.HC.Frame.hostOrbitsPlaces (φ := D.R.toFrame) _ hg (D.R.tau1 t) (tau_one_mem_orbit_set D.R.toFrame t) i).1
    show D.R.iotaInv (Formalism.HC.Frame.placeOf _).2 = _
    rw [this, Formalism.HC.Frame.iotaInv_mul, Formalism.HC.Frame.iotaInv_pow]
    change i • D.R.iotaInv (D.R.iota h) + D.R.iotaInv (D.R.iota t) = t + i • h
    rw [Formalism.HC.Frame.iotaInv_iota, Formalism.HC.Frame.iotaInv_iota, add_comm]
  · intro hc t i
    have := (Formalism.HC.Frame.hostOrbitsPlaces (φ := D.R.toFrame) _ hg (D.R.tau1 t) (tau_one_mem_orbit_set D.R.toFrame t) i).2.1
      (by rw [hg1]; exact hc)
    rw [this]
    rfl
  · intro hs t i
    have := (Formalism.HC.Frame.hostOrbitsPlaces (φ := D.R.toFrame) _ hg (D.R.tau1 t) (tau_one_mem_orbit_set D.R.toFrame t) i).2.2
      (by rw [hg1, hs, hsg])
    rw [this]
    exact mul_one _
  · intro hc τ hτ
    refine ⟨?_, even_addOrderOf_of_h_ne_zero D⟩
    rw [Formalism.HC.Frame.hostOrbitCount (φ := D.R.toFrame) _ (by rw [hg1]; exact hc) τ hτ]
    exact orderOf_ofAdd_eq_addOrderOf h

/- English proof (translation)
Introduce `hL φ hφ hφc τ hτ i ⟨h0, h1, h2⟩`. Establish `mem : ∀ g : D.R.GG, g ∈ thick D → ∃ s ∈ D.host.T2, g = D.R.tau2 (D.R.dig s + D.host.u0)`. Introduce `g hg`. Take `⟨s, hs, he⟩` from `Finset.mem_image.1 hg`. Conclude with `⟨s, hs, he.symm⟩`.

Conclude with `no_three D.R.toFrame D.host.T2 D.host.second_set_range D.host.second_set_no_relation D.host.u0 hL φ hφ hφc τ hτ i (mem _ h0) (mem _ h1) (mem _ h2)`.
-/
theorem no_three_consecutive_thick_places (D : D7) : TorusPairsWithVariant D := by
  intro hL φ hφ hφc τ hτ i ⟨h0, h1, h2⟩
  have mem : ∀ g : D.R.GG, g ∈ thick D → ∃ s ∈ D.host.T2, g = D.R.tau2 (D.R.dig s + D.host.u0) := by
    intro g hg
    obtain ⟨s, hs, he⟩ := Finset.mem_image.1 hg
    exact ⟨s, hs, he.symm⟩
  exact no_three D.R.toFrame D.host.T2 D.host.second_set_range D.host.second_set_no_relation D.host.u0 hL φ hφ hφc τ hτ i
    (mem _ h0) (mem _ h1) (mem _ h2)

end Formalism.MainNotions.UnusedSlot33

end
