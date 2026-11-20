import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NormRepCountSplitOne
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NormRepCountPowSuccInert
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.EulerFacMulConjInvSplit

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace C2

/- English proof (translation)
Proceed by induction on `k, hk using Nat.le_induction with`. Consider the case `base => simp`. Consider the case `succ n hn ih`. Rewrite using `[h n hn, ih, show n + 1 - 1 = (n - 1) + 1 by omega, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem geom_of_step (c : ℕ → ℕ) (a : ℕ) (h : ∀ k, 1 ≤ k → c (k + 1) = a * c k) (k : ℕ)
    (hk : 1 ≤ k) : c k = a ^ (k - 1) * c 1 := by
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [h n hn, ih, show n + 1 - 1 = (n - 1) + 1 by omega, pow_succ]
    ring

/- English proof (translation)
Take `⟨j, rfl⟩ : ∃ j, k = j + 1` from `⟨k - 1, by omega⟩`. Rewrite using `[geom_of_step c (q ^ N) h (j + 1) hk]`. Use `push_cast`. Rewrite using `[h1]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cast_geom (c : ℕ → ℕ) (q N : ℕ) (X : ℝ) (h : ∀ k, 1 ≤ k → c (k + 1) = q ^ N * c k)
    (h1 : (c 1 : ℝ) = (q : ℝ) ^ N * X) (k : ℕ) (hk : 1 ≤ k) :
    (c k : ℝ) = (q : ℝ) ^ (N * k) * X := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [geom_of_step c (q ^ N) h (j + 1) hk]
  push_cast
  rw [h1]
  ring

/- English proof (translation)
Take `⟨j, rfl⟩ : ∃ j, M = j + 1` from `⟨M - 1, by omega⟩`. Rewrite using `[show 2 * (j + 1) - 1 = 2 * j + 1 by omega, Nat.add_sub_cancel, zpow_neg]`. Rewrite using `[show ((j + 1 : ℕ) : ℤ) = ((j + 1 : ℕ) : ℤ) from rfl, zpow_natCast]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem inert_alg (q : ℝ) (hq : q ≠ 0) (M : ℕ) (hM : 1 ≤ M) :
    q ^ (M - 1) * (q ^ M - (-1) ^ M) = q ^ (2 * M - 1) * (1 - (-1 : ℝ) ^ M * q ^ (-(M : ℤ))) := by
  obtain ⟨j, rfl⟩ : ∃ j, M = j + 1 := ⟨M - 1, by omega⟩
  rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega, Nat.add_sub_cancel, zpow_neg]
  rw [show ((j + 1 : ℕ) : ℤ) = ((j + 1 : ℕ) : ℤ) from rfl, zpow_natCast]
  field_simp
  ring

/- English proof (translation)
Take `⟨j, rfl⟩ : ∃ j, M = j + 1` from `⟨M - 1, by omega⟩`. Rewrite using `[show 2 * (j + 1) - 1 = 2 * j + 1 by omega, Nat.add_sub_cancel, zpow_neg]`. Rewrite using `[show ((j + 1 : ℕ) : ℤ) = ((j + 1 : ℕ) : ℤ) from rfl, zpow_natCast]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem split_alg (q : ℝ) (hq : q ≠ 0) (M : ℕ) (hM : 1 ≤ M) :
    q ^ (2 * M - 1) - q ^ (M - 1) = q ^ (2 * M - 1) * (1 - q ^ (-(M : ℤ))) := by
  obtain ⟨j, rfl⟩ : ∃ j, M = j + 1 := ⟨M - 1, by omega⟩
  rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega, Nat.add_sub_cancel, zpow_neg]
  rw [show ((j + 1 : ℕ) : ℤ) = ((j + 1 : ℕ) : ℤ) from rfl, zpow_natCast]
  field_simp
  ring

end C2

/- English proof (translation)
Introduce `K _ _ _ hK P hP M k hM hk n hn hnP`. Establish `hPbot : P ≠ ⊥` using `Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)`. Establish `hN0 : Ideal.absNorm P ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `hPbot`.

Prove the components needed by the constructor for the conclusion. Introduce `hc`. Take `⟨q, hq⟩` from `exists_sq_absNorm_of_inert hK hP hc`. Establish `hq0 : (q : ℝ) ≠ 0`. Introduce `h0`.

Establish `h1 : q = 0` using `by exact_mod_cast h0`. Rewrite `hq` using `[h1]`. Conclude with `hN0 (by simpa using hq)`. Establish `hsq : Real.sqrt (Ideal.absNorm P : ℝ) = q`. Rewrite using `[hq]`.

Use `push_cast`. Conclude with `Real.sqrt_sq (Nat.cast_nonneg q)`. Rewrite using `[hsq]`. Establish `h1 : ((normRepCount K (P ^ 1) M n : ℕ) : ℝ) = (q : ℝ) ^ (2 * M - 1) * (1 - (-1 : ℝ) ^ M * (q : ℝ) ^ (-(M : ℤ)))`. Rewrite using `[pow_one]`.

Establish `h3` using `normRepCount_inert_one hK hP hc M hM n hn hnP q hq`. Establish `h2 : ((normRepCount K P M n : ℕ) : ℝ) = (q : ℝ) ^ (M - 1) * ((q : ℝ) ^ M - (-1) ^ M)`. Conclude with `h3` after adjusting the coercions. Rewrite using `[h2, C2.inert_alg _ hq0 M hM]`. Conclude with `C2.cast_geom (fun j => normRepCount K (P ^ j) M n) q (2 * M - 1) _ (fun j hj => normRepCount_pow_succ_inert hK hP hc M j hM hj n hn hnP q hq) h1 k hk`.

Introduce `hc`. Establish `hN : ((Ideal.absNorm P : ℕ) : ℝ) ≠ 0` using `by exact_mod_cast hN0`. Establish `h1 : ((normRepCount K ((P * Formalism.HermitianLatticesTheory.conjIdeal (K` using `K) P) ^ 1) M n : ℕ) : ℝ) = (Ideal.absNorm P : ℝ) ^ (2 * M - 1) * (1 - (Ideal.absNorm P : ℝ) ^ (-(M : ℤ))) := by`. Rewrite using `[pow_one]`. Establish `h3` using `normRepCount_split_one hK hP hc M hM n hn hnP`.

Establish `h2 : ((normRepCount K (P * Formalism.HermitianLatticesTheory.conjIdeal (K` using `K) P) M n : ℕ) : ℝ) = (Ideal.absNorm P : ℝ) ^ (2 * M - 1) - (Ideal.absNorm P : ℝ) ^ (M - 1) := by`. Conclude with `h3` after adjusting the coercions. Rewrite using `[h2, C2.split_alg _ hN M hM]`. Conclude with `C2.cast_geom (fun j => normRepCount K ((P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ^ j) M n) (Ideal.absNorm P) (2 * M - 1) _ (fun j hj => normRepCount_pow_succ_split hK hP hc M j hM hj n hn hnP) h1 k hk`.
-/
theorem localDensity : LocalDensity := by
  intro K _ _ _ hK P hP M k hM hk n hn hnP
  have hPbot : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)
  have hN0 : Ideal.absNorm P ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hPbot
  constructor
  · intro hc
    obtain ⟨q, hq⟩ := exists_sq_absNorm_of_inert hK hP hc
    have hq0 : (q : ℝ) ≠ 0 := by
      intro h0
      have h1 : q = 0 := by exact_mod_cast h0
      rw [h1] at hq
      exact hN0 (by simpa using hq)
    have hsq : Real.sqrt (Ideal.absNorm P : ℝ) = q := by
      rw [hq]
      push_cast
      exact Real.sqrt_sq (Nat.cast_nonneg q)
    rw [hsq]
    have h1 : ((normRepCount K (P ^ 1) M n : ℕ) : ℝ) =
        (q : ℝ) ^ (2 * M - 1) * (1 - (-1 : ℝ) ^ M * (q : ℝ) ^ (-(M : ℤ))) := by
      rw [pow_one]
      have h3 := normRepCount_inert_one hK hP hc M hM n hn hnP q hq
      have h2 : ((normRepCount K P M n : ℕ) : ℝ) = (q : ℝ) ^ (M - 1) * ((q : ℝ) ^ M - (-1) ^ M) := by
        exact_mod_cast h3
      rw [h2, C2.inert_alg _ hq0 M hM]
    exact C2.cast_geom (fun j => normRepCount K (P ^ j) M n) q (2 * M - 1) _
      (fun j hj => normRepCount_pow_succ_inert hK hP hc M j hM hj n hn hnP q hq) h1 k hk
  · intro hc
    have hN : ((Ideal.absNorm P : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hN0
    have h1 : ((normRepCount K ((P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ^ 1) M n : ℕ) : ℝ) =
        (Ideal.absNorm P : ℝ) ^ (2 * M - 1) * (1 - (Ideal.absNorm P : ℝ) ^ (-(M : ℤ))) := by
      rw [pow_one]
      have h3 := normRepCount_split_one hK hP hc M hM n hn hnP
      have h2 : ((normRepCount K (P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) M n : ℕ) : ℝ) =
          (Ideal.absNorm P : ℝ) ^ (2 * M - 1) - (Ideal.absNorm P : ℝ) ^ (M - 1) := by
        exact_mod_cast h3
      rw [h2, C2.split_alg _ hN M hM]
    exact C2.cast_geom (fun j => normRepCount K ((P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ^ j) M n)
      (Ideal.absNorm P) (2 * M - 1) _
      (fun j hj => normRepCount_pow_succ_split hK hP hc M j hM hj n hn hnP) h1 k hk

variable {K : Type} [Field K] [NumberField K] [StarRing K]

/- English proof (translation)
Rewrite using `[(localDensity K hK P hP M k hM hk n hn hnP).1 hc, Formalism.HermitianLatticesTheory.eulerFac, if_pos hc, inv_inv]`.
-/
theorem normRepCount_eq_eulerFac_inert (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) (M k : ℕ) (hM : 1 ≤ M)
    (hk : 1 ≤ k) (n : 𝓞 K) (hn : conjO K n = n) (hnP : n ∉ P) :
    (normRepCount K (P ^ k) M n : ℝ) =
      Real.sqrt (Ideal.absNorm P : ℝ) ^ ((2 * M - 1) * k) * (Formalism.HermitianLatticesTheory.eulerFac K M P)⁻¹ := by
  rw [(localDensity K hK P hP M k hM hk n hn hnP).1 hc, Formalism.HermitianLatticesTheory.eulerFac, if_pos hc, inv_inv]

/- English proof (translation)
Establish `hc' : Formalism.HermitianLatticesTheory.conjIdeal (K` using `K) (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ≠ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := fun h => hc ((conjIdeal_conjIdeal hK P).symm.trans h).symm`. Establish `hPbot : P ≠ ⊥` using `Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)`. Establish `hN0 : Ideal.absNorm P ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `hPbot`.

Establish `hN1 : Ideal.absNorm P ≠ 1`. Rewrite using `[Ne, Ideal.absNorm_eq_one_iff]`. Conclude with `hP.ne_top`. Establish `hN2 : (1 : ℝ) < (Ideal.absNorm P : ℝ)`. Establish `: 2 ≤ Ideal.absNorm P` using `by omega`.

Conclude with `(by omega : 1 < Ideal.absNorm P)` after adjusting the coercions. Establish `hx : 0 < 1 - (Ideal.absNorm P : ℝ) ^ (-(M : ℤ))`. Rewrite using `[zpow_neg, zpow_natCast, sub_pos]`. Conclude with `inv_lt_one_of_one_lt₀ (one_lt_pow₀ hN2 (by omega))`. Rewrite using `[(localDensity K hK P hP M k hM hk n hn hnP).2 hc, Formalism.HermitianLatticesTheory.eulerFac, Formalism.HermitianLatticesTheory.eulerFac, if_neg hc, if_neg hc', absNorm_conjIdeal hK, ← Real.rpow_add hx, show (-(1 : ℝ) / 2 + -(1 : ℝ) / 2) = -1 by norm_num, Real.rpow_neg_one, inv_ …`.
-/
theorem normRepCount_eq_eulerFac_split (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) (M k : ℕ) (hM : 1 ≤ M)
    (hk : 1 ≤ k) (n : 𝓞 K) (hn : conjO K n = n) (hnP : n ∉ P) :
    (normRepCount K ((P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ^ k) M n : ℝ) =
      (Ideal.absNorm P : ℝ) ^ ((2 * M - 1) * k) *
        (Formalism.HermitianLatticesTheory.eulerFac K M P * Formalism.HermitianLatticesTheory.eulerFac K M (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P))⁻¹ := by
  have hc' : Formalism.HermitianLatticesTheory.conjIdeal (K := K) (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ≠ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P :=
    fun h => hc ((conjIdeal_conjIdeal hK P).symm.trans h).symm
  have hPbot : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)
  have hN0 : Ideal.absNorm P ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hPbot
  have hN1 : Ideal.absNorm P ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact hP.ne_top
  have hN2 : (1 : ℝ) < (Ideal.absNorm P : ℝ) := by
    have : 2 ≤ Ideal.absNorm P := by omega
    exact_mod_cast (by omega : 1 < Ideal.absNorm P)
  have hx : 0 < 1 - (Ideal.absNorm P : ℝ) ^ (-(M : ℤ)) := by
    rw [zpow_neg, zpow_natCast, sub_pos]
    exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ hN2 (by omega))
  rw [(localDensity K hK P hP M k hM hk n hn hnP).2 hc, Formalism.HermitianLatticesTheory.eulerFac, Formalism.HermitianLatticesTheory.eulerFac, if_neg hc,
    if_neg hc', absNorm_conjIdeal hK, ← Real.rpow_add hx,
    show (-(1 : ℝ) / 2 + -(1 : ℝ) / 2) = -1 by norm_num, Real.rpow_neg_one, inv_inv]

end Formalism.HermitianLattices.Ext.L3
