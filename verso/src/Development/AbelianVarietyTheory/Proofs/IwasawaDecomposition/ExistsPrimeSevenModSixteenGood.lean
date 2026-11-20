import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplZeta
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplChi
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LogDerOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ZeroCount
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsExcRat
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.PageThm
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Jutila
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BadCharsCountOfDensity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GChiApproximationSumStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardPrimesResidueGeRpow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultiplicativeWeightPrimeSumStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KroneckerTwoNegEqJacobiSymTwo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfEqOnCoprime
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.SplitPrimeChoice

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Establish `hB0 : (0 : ℝ) ≤ B.card` using `Nat.cast_nonneg _`. Establish `hP : (0 : ℝ) < P.card` using `by linarith`. Rewrite `hf`, `hg` using `[div_le_iff₀ hP]`. Establish `h1 : ∀ d ∈ P \ B, T ^ 2 ≤ f d ^ 2 + g d ^ 2`.

Introduce `d hd`. Take `⟨hdP, hdB⟩` from `mem_sdiff.1 hd`. Distinguish the cases in `h : f d ≤ T`. Establish `h' : T < g d`. Assume the negation of the conclusion as `h'`.

Conclude with `hcon ⟨d, hdP, hdB, h, not_lt.1 h'⟩`. Use polynomial arithmetic with `[sq_nonneg (f d)]`. Establish `h'` using `not_le.1 h`. Use polynomial arithmetic with `[sq_nonneg (g d)]`. Establish `h2` using `sum_le_sum h1`.

Rewrite `h2` using `[sum_const, nsmul_eq_mul]`. Establish `h3 : ∑ d ∈ P \ B, (f d ^ 2 + g d ^ 2) ≤ ∑ d ∈ P, (f d ^ 2 + g d ^ 2)` using `sum_le_sum_of_subset_of_nonneg sdiff_subset (fun d _ _ => by positivity)`. Rewrite `h3` using `[sum_add_distrib (s := P)]`. Establish `h4 : (P.card : ℝ) ≤ (P \ B).card + B.card`. Conclude with `card_le_card_sdiff_add_card` after adjusting the coercions.

Establish `h5 : (P.card : ℝ) < 2 * (P \ B).card` using `by linarith`. Establish `h6` using `mul_lt_mul_of_pos_right h5 (pow_pos hT 2)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem exists_small_pair (P B : Finset ℕ) (f g : ℕ → ℝ) (A T : ℝ) (hT : 0 < T)
    (hB : 2 * (B.card : ℝ) < P.card)
    (hf : (∑ p ∈ P, f p ^ 2) / P.card ≤ A) (hg : (∑ p ∈ P, g p ^ 2) / P.card ≤ A)
    (hA : 4 * A ≤ T ^ 2) : ∃ d ∈ P, d ∉ B ∧ f d ≤ T ∧ g d ≤ T := by
  by_contra hcon
  have hB0 : (0 : ℝ) ≤ B.card := Nat.cast_nonneg _
  have hP : (0 : ℝ) < P.card := by linarith
  rw [div_le_iff₀ hP] at hf hg
  have h1 : ∀ d ∈ P \ B, T ^ 2 ≤ f d ^ 2 + g d ^ 2 := by
    intro d hd
    obtain ⟨hdP, hdB⟩ := mem_sdiff.1 hd
    by_cases h : f d ≤ T
    · have h' : T < g d := by
        by_contra h'
        exact hcon ⟨d, hdP, hdB, h, not_lt.1 h'⟩
      nlinarith [sq_nonneg (f d)]
    · have h' := not_le.1 h
      nlinarith [sq_nonneg (g d)]
  have h2 := sum_le_sum h1
  rw [sum_const, nsmul_eq_mul] at h2
  have h3 : ∑ d ∈ P \ B, (f d ^ 2 + g d ^ 2) ≤ ∑ d ∈ P, (f d ^ 2 + g d ^ 2) :=
    sum_le_sum_of_subset_of_nonneg sdiff_subset (fun d _ _ => by positivity)
  rw [sum_add_distrib (s := P)] at h3
  have h4 : (P.card : ℝ) ≤ (P \ B).card + B.card := by
    exact_mod_cast card_le_card_sdiff_add_card
  have h5 : (P.card : ℝ) < 2 * (P \ B).card := by linarith
  have h6 := mul_lt_mul_of_pos_right h5 (pow_pos hT 2)
  nlinarith

/- English proof (translation)
Use `set S := (range (n + 1)).filter (fun p => p.Prime ∧ p ≠ 2) with hS`. Use `⟨q * ∏ p ∈ S, p, ?_, dvd_mul_right _ _, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite `hq2`, the goal using `[← Nat.odd_iff]`. Use `hq2.mul (Finset.prod_induction _ Odd (fun a b => Odd.mul) odd_one ?_)` and prove the remaining obligations. Introduce `p hp`.

Take `⟨-, h1, h2⟩` from `mem_filter.1 hp`. Conclude with `h1.odd_of_ne_two h2`. Introduce `p hp h2 hn`. Conclude with `(dvd_prod_of_mem (fun p => p) (mem_filter.2 ⟨mem_range.2 (by omega), hp, h2⟩)).mul_left q`. Introduce `p hp hd`.

Break down `(Nat.Prime.dvd_mul hp).1 hd with h | h` into its components or cases. Conclude with `Or.inr ((Nat.prime_dvd_prime_iff_eq hp hq).1 h)`. Take `⟨r, hr, hpr⟩` from `(Prime.dvd_finsetProd_iff hp.prime _).1 h`. Take `⟨h0, h1, -⟩` from `mem_filter.1 hr`. Use `(Nat.prime_dvd_prime_iff_eq hp h1).1 hpr` as an intermediate fact.

Use `mem_range.1 h0` as an intermediate fact. Conclude with `Or.inl (by omega)`. Use `Nat.mul_le_mul_left q (le_trans ?_ (primorial_le_four_pow n))` and prove the remaining obligations. Use `Nat.le_of_dvd (primorial_pos n) (prod_dvd_prod_of_subset _ _ _ ?_)` and prove the remaining obligations. Introduce `p hp`.

Take `⟨h0, h1, -⟩` from `mem_filter.1 hp`. Conclude with `mem_filter.2 ⟨h0, h1⟩`.
-/
theorem exists_modulus (n q : ℕ) (hq : q.Prime) (hq2 : q % 2 = 1) :
    ∃ M : ℕ, M % 2 = 1 ∧ q ∣ M ∧ (∀ p : ℕ, p.Prime → p ≠ 2 → p ≤ n → p ∣ M) ∧
      (∀ p : ℕ, p.Prime → p ∣ M → p ≤ n ∨ p = q) ∧ M ≤ q * 4 ^ n := by
  set S := (range (n + 1)).filter (fun p => p.Prime ∧ p ≠ 2) with hS
  refine ⟨q * ∏ p ∈ S, p, ?_, dvd_mul_right _ _, ?_, ?_, ?_⟩
  · rw [← Nat.odd_iff] at hq2 ⊢
    refine hq2.mul (Finset.prod_induction _ Odd (fun a b => Odd.mul) odd_one ?_)
    intro p hp
    obtain ⟨-, h1, h2⟩ := mem_filter.1 hp
    exact h1.odd_of_ne_two h2
  · intro p hp h2 hn
    exact (dvd_prod_of_mem (fun p => p) (mem_filter.2 ⟨mem_range.2 (by omega), hp, h2⟩)).mul_left q
  · intro p hp hd
    rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp hq).1 h)
    · obtain ⟨r, hr, hpr⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 h
      obtain ⟨h0, h1, -⟩ := mem_filter.1 hr
      have := (Nat.prime_dvd_prime_iff_eq hp h1).1 hpr
      have := mem_range.1 h0
      exact Or.inl (by omega)
  · refine Nat.mul_le_mul_left q (le_trans ?_ (primorial_le_four_pow n))
    refine Nat.le_of_dvd (primorial_pos n) (prod_dvd_prod_of_subset _ _ _ ?_)
    intro p hp
    obtain ⟨h0, h1, -⟩ := mem_filter.1 hp
    exact mem_filter.2 ⟨h0, h1⟩

/- English proof (translation)
Unfold `GlobalTheoryTheory.kronSym`. Establish `h0 : p.factorization 2 = 0` using `Nat.factorization_eq_zero_of_not_dvd (by omega)`. Rewrite using `[h0, pow_zero, pow_zero, Nat.div_one, mul_one]`. Establish `h1 : (-(d : ℤ)) % p = 1 % p`. Apply `Int.modEq_iff_dvd.2` to reduce the goal to its premises.

Establish `: (p : ℤ) ∣ ((d + 1 : ℕ) : ℤ)` using `Int.natCast_dvd_natCast.2 h`. Establish `e : (1 : ℤ) - -(d : ℤ) = ((d + 1 : ℕ) : ℤ)` using `by push_cast; ring`. Rewrite using `[e]` and apply the resulting hypothesis. Rewrite using `[jacobiSym.mod_left' h1, jacobiSym.one_left]`.
-/
theorem kronSym_eq_one_of_dvd (d p : ℕ) (hp : p % 2 = 1) (h : p ∣ d + 1) :
    GlobalTheoryTheory.kronSym (-(d : ℤ)) p = 1 := by
  unfold GlobalTheoryTheory.kronSym
  have h0 : p.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by omega)
  rw [h0, pow_zero, pow_zero, Nat.div_one, mul_one]
  have h1 : (-(d : ℤ)) % p = 1 % p := by
    apply Int.modEq_iff_dvd.2
    have : (p : ℤ) ∣ ((d + 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.2 h
    have e : (1 : ℤ) - -(d : ℤ) = ((d + 1 : ℕ) : ℤ) := by push_cast; ring
    rwa [e]
  rw [jacobiSym.mod_left' h1, jacobiSym.one_left]

/- English proof (translation)
Unfold `GlobalTheoryTheory.kronSym GlobalTheoryTheory.kron2`. Rewrite using `[Nat.prime_two.factorization_self]`. Evaluate the numerical expressions. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem kronSym_two_eq_one (d : ℕ) (h : d % 8 = 7) : GlobalTheoryTheory.kronSym (-(d : ℤ)) 2 = 1 := by
  unfold GlobalTheoryTheory.kronSym GlobalTheoryTheory.kron2
  rw [Nat.prime_two.factorization_self]
  norm_num
  split_ifs <;> omega

/- English proof (translation)
Establish `key : ∀ (c r s : ℝ), 0 < s → ∀ᶠ x : ℝ in atTop, c * Real.log x ^ r ≤ x ^ s`. Introduce `c r s hs`. Establish `h` using `((isLittleO_log_rpow_rpow_atTop r hs).const_mul_left c).bound one_pos`. Use `filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with x hx hx0`. Rewrite `hx` using `[one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0 s)]`.

Conclude with `(le_abs_self _).trans hx`. Establish `h5 : 0 < eps / 5` using `by positivity`. Use `filter_upwards [eventually_ge_atTop (4 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 2, (tendsto_rpow_atTop h5).eventually_ge_atTop 3, key 800 1 _ h5, key 2 2 (eps / 20) (by positivity), key (16 * C) 1 (2 * eps) (by positivity), (tendsto_rpow_atTop h5).eventually_ge_atTop (8 * …`. Rewrite `h4`, `h7` using `[Real.rpow_one]`. Rewrite `h6` using `[Real.rpow_two]`.

Conclude with `⟨h1, h2, h3, h4, h6, h7, h8⟩`.
-/
theorem sizes (eps C C₁ : ℝ) (he : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, 4 ≤ x ∧ 2 ≤ Real.log x ∧ 3 ≤ x ^ (eps / 5) ∧ 800 * Real.log x ≤ x ^ (eps / 5) ∧
      2 * Real.log x ^ 2 ≤ x ^ (eps / 20) ∧ 16 * C * Real.log x ≤ x ^ (2 * eps) ∧ 8 * C₁ ≤ x ^ (eps / 5) := by
  have key : ∀ (c r s : ℝ), 0 < s → ∀ᶠ x : ℝ in atTop, c * Real.log x ^ r ≤ x ^ s := by
    intro c r s hs
    have h := ((isLittleO_log_rpow_rpow_atTop r hs).const_mul_left c).bound one_pos
    filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with x hx hx0
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0 s)] at hx
    exact (le_abs_self _).trans hx
  have h5 : 0 < eps / 5 := by positivity
  filter_upwards [eventually_ge_atTop (4 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 2,
    (tendsto_rpow_atTop h5).eventually_ge_atTop 3, key 800 1 _ h5,
    key 2 2 (eps / 20) (by positivity), key (16 * C) 1 (2 * eps) (by positivity),
    (tendsto_rpow_atTop h5).eventually_ge_atTop (8 * C₁)] with x h1 h2 h3 h4 h6 h7 h8
  rw [Real.rpow_one] at h4 h7
  rw [Real.rpow_two] at h6
  exact ⟨h1, h2, h3, h4, h6, h7, h8⟩

/- English proof (translation)
Establish `hfin : (Formalism.HermitianLattices.GL2PrimeSums.BadChars Q).Finite`. Rewrite using `[← Set.encard_ne_top_iff]`. Introduce `h`. Rewrite `hQ` using `[h]`. Simplify using `at hQ`.

Establish `hcard : (hfin.toFinset.card : ℝ) ≤ K`. Rewrite `hQ` using `[hfin.encard_eq_coe_toFinset_card]`. Establish `h : ENNReal.ofReal (hfin.toFinset.card : ℝ) ≤ ENNReal.ofReal K`. Rewrite using `[ENNReal.ofReal_natCast]`. Conclude with `hQ` after adjusting the coercions.

Conclude with `(ENNReal.ofReal_le_ofReal_iff hK).1 h`. Use `⟨(univ : Finset (Fin 2 × Fin 2)).biUnion (fun ik => hfin.toFinset.image (fun c => (c.1 + 1) / (8 ^ ik.2.1 * q ^ ik.1.1))), ?_, ?_⟩` and prove the remaining obligations. Establish `h : ((univ : Finset (Fin 2 × Fin 2)).biUnion (fun ik => hfin.toFinset.image (fun c => (c.1 + 1) / (8 ^ ik.2.1 * q ^ ik.1.1)))).card ≤ 4 * hfin.toFinset.card`. Use `(card_biUnion_le_card_mul _ _ hfin.toFinset.card (fun _ _ => card_image_le)).trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.

Establish `h'` using `(Nat.cast_le (α := ℝ)).2 h`. Rewrite `h'` using `[Nat.cast_mul, Nat.cast_ofNat]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `d hd hd4 hqd hle hdB i k N _ χ hχ`. Take `⟨hN, hsq, hne, hre, -⟩` from `GlobalTheory.QuadPrim.main q d hq hd hq4 hd4 hqd i 1 k (by simp) N χ (by simpa using hχ)`.

Establish `hNQ : (N : ℝ) ≤ Q`. Use `le_trans ?_ hle` and prove the remaining obligations. Establish `h8 : 8 ^ k.1 ≤ 8 ^ 1` using `Nat.pow_le_pow_right (by norm_num) (by omega)`. Establish `hqq : q ^ i.1 ≤ q ^ 1` using `Nat.pow_le_pow_right hq.pos (by omega)`. Establish `: N ≤ 8 * q * d`.

Rewrite using `[hN]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `this` after adjusting the coercions. Use `⟨hχ.1, hre, hNQ, fun s hs hi hz => hdB ?_⟩` and prove the remaining obligations. Take `⟨n, rfl⟩` from `Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)`.

Use `mem_biUnion.2 ⟨(i, k), mem_univ _, mem_image.2 ⟨⟨n, χ⟩, hfin.mem_toFinset.2 ⟨hNQ, hχ.1, hsq, fun hg => hg s hs hi ?_⟩, ?_⟩⟩` and prove the remaining obligations. Conclude with `⟨Or.inl hne, hz⟩`. Apply `Nat.div_eq_of_eq_mul_right (by have := hq.pos; positivity)` to reduce the goal to its premises. Establish `: n + 1 = _` using `hN`. Simplify using `only [this]`.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_bad_set (Q K : ℝ) (hK : 0 ≤ K)
    (hQ : (((Formalism.HermitianLattices.GL2PrimeSums.BadChars Q).encard : ℕ∞) : ENNReal) ≤ ENNReal.ofReal K)
    (q : ℕ) (hq : q.Prime) (hq4 : q % 4 = 3) :
    ∃ B : Finset ℕ, (B.card : ℝ) ≤ 4 * K ∧ ∀ d : ℕ, d.Prime → d % 4 = 3 → q ≠ d →
      8 * (q : ℝ) * d ≤ Q → d ∉ B → ∀ i k : Fin 2,
        GoodAllFor Q (fun a => GlobalTheoryTheory.chi8 a ^ k.1 * GlobalTheoryTheory.chDir d a * GlobalTheoryTheory.psDir q a ^ i.1) (8 * q * d) := by
  classical
  have hfin : (Formalism.HermitianLattices.GL2PrimeSums.BadChars Q).Finite := by
    rw [← Set.encard_ne_top_iff]
    intro h
    rw [h] at hQ
    simp at hQ
  have hcard : (hfin.toFinset.card : ℝ) ≤ K := by
    rw [hfin.encard_eq_coe_toFinset_card] at hQ
    have h : ENNReal.ofReal (hfin.toFinset.card : ℝ) ≤ ENNReal.ofReal K := by
      rw [ENNReal.ofReal_natCast]; exact_mod_cast hQ
    exact (ENNReal.ofReal_le_ofReal_iff hK).1 h
  refine ⟨(univ : Finset (Fin 2 × Fin 2)).biUnion (fun ik => hfin.toFinset.image
    (fun c => (c.1 + 1) / (8 ^ ik.2.1 * q ^ ik.1.1))), ?_, ?_⟩
  · have h : ((univ : Finset (Fin 2 × Fin 2)).biUnion (fun ik => hfin.toFinset.image
        (fun c => (c.1 + 1) / (8 ^ ik.2.1 * q ^ ik.1.1)))).card ≤ 4 * hfin.toFinset.card := by
      refine (card_biUnion_le_card_mul _ _ hfin.toFinset.card (fun _ _ => card_image_le)).trans ?_
      simp
    have h' := (Nat.cast_le (α := ℝ)).2 h
    rw [Nat.cast_mul, Nat.cast_ofNat] at h'
    linarith
  · intro d hd hd4 hqd hle hdB i k N _ χ hχ
    obtain ⟨hN, hsq, hne, hre, -⟩ := GlobalTheory.QuadPrim.main q d hq hd hq4 hd4 hqd i 1 k (by simp) N χ
      (by simpa using hχ)
    have hNQ : (N : ℝ) ≤ Q := by
      refine le_trans ?_ hle
      have h8 : 8 ^ k.1 ≤ 8 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hqq : q ^ i.1 ≤ q ^ 1 := Nat.pow_le_pow_right hq.pos (by omega)
      have : N ≤ 8 * q * d := by
        rw [hN]
        calc _ ≤ 8 ^ 1 * d ^ (1 : Fin 2).1 * q ^ 1 := by gcongr
          _ = _ := by simp; ring
      exact_mod_cast this
    refine ⟨hχ.1, hre, hNQ, fun s hs hi hz => hdB ?_⟩
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
    refine mem_biUnion.2 ⟨(i, k), mem_univ _, mem_image.2 ⟨⟨n, χ⟩, hfin.mem_toFinset.2
      ⟨hNQ, hχ.1, hsq, fun hg => hg s hs hi ?_⟩, ?_⟩⟩
    · exact ⟨Or.inl hne, hz⟩
    · apply Nat.div_eq_of_eq_mul_right (by have := hq.pos; positivity)
      have : n + 1 = _ := hN
      simp only [this]
      simp; ring

/- English proof (translation)
Introduce `N _ χ hχ`. Establish `hχ' : GlobalTheoryTheory.Induces χ (fun a => GlobalTheoryTheory.chi8 a ^ (0 : Fin 2).1 * GlobalTheoryTheory.chDir d a * GlobalTheoryTheory.psDir q a ^ i.1) (8 * q * d)` using `⟨hχ.1, fun a ha => by rw [hχ.2 a ha, hf]; simp⟩`. Take `⟨-, -, hne, -, hval⟩` from `GlobalTheory.QuadPrim.main q d hq hd hq4 hd4 hqd i 1 0 (by simp) N χ (by simpa using hχ')`. Take `⟨h1, h2⟩` from `htail N χ hne (hgood N χ hχ')`. Use `⟨?_, h2⟩` and prove the remaining obligations.

Establish `e : ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, (GlobalTheoryTheory.cn x n : ℂ) * χ (n : ZMod N) = Formalism.HermitianLattices.GL2PrimeSums.sqSum x (fun n => ((jacobiSym (n : ℤ) q : ℤ) : ℂ) ^ i.1) d`. Use `sum_congr rfl fun n hn => ?_` and prove the remaining obligations. Establish `hn0 : 0 < n` using `(mem_Icc.1 hn).1`. Rewrite using `[hval n hn0 rfl, GlobalTheoryTheory.chDir, GlobalTheoryTheory.psDir, GlobalTheoryTheory.kron, GlobalTheoryTheory.kron, GlobalTheory.kronSym_neg_eq_jacobiSym_and_two.1 d n hd4 hn0, GlobalTheory.kronSym_neg_eq_jacobiSym_and_two.1 q n hq4 hn0]`. Establish `: GlobalTheoryTheory.cn x n = Formalism.HermitianLattices.GL2PrimeSums.cn x n` using `rfl`.

Rewrite using `[this]`. Simplify using `only [Fin.val_one, pow_one]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[e]`. Establish `h3` using `norm_sub_le (GlobalTheoryTheory.gChi χ x + Formalism.HermitianLattices.GL2PrimeSums.sqSum x (fun n => ((jacobiSym (n : ℤ) q : ℤ) : ℂ) ^ i.1) d) (Formalism.HermitianLattices.GL2PrimeSums.sqSum x (fun n => ((jacobiSym (n : ℤ) q : ℤ) : ℂ) ^ i.1) d)`.

Rewrite `h3` using `[add_sub_cancel_right]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem boundsAtX_of_good (x eps C Q : ℝ) (q d : ℕ) (hq : q.Prime) (hd : d.Prime) (hq4 : q % 4 = 3)
    (hd4 : d % 4 = 3) (hqd : q ≠ d) (i : Fin 2) (f : ℕ → ℂ)
    (hf : ∀ a, f a = GlobalTheoryTheory.chDir d a * GlobalTheoryTheory.psDir q a ^ i.1)
    (hx : x ^ eps ≤ x ^ ((1 : ℝ) / 2 + eps) / 2)
    (hgood : GoodAllFor Q
      (fun a => GlobalTheoryTheory.chi8 a ^ (0 : Fin 2).1 * GlobalTheoryTheory.chDir d a * GlobalTheoryTheory.psDir q a ^ i.1) (8 * q * d))
    (htail : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → GlobalTheoryTheory.GoodFor Q χ →
      ‖GlobalTheoryTheory.gChi χ x + ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, (GlobalTheoryTheory.cn x n : ℂ) * χ (n : ZMod N)‖ ≤ x ^ eps ∧
        ‖GlobalTheoryTheory.logDerivativeAtOne χ‖ ≤ C * Real.log x)
    (hs : ‖Formalism.HermitianLattices.GL2PrimeSums.sqSum x (fun n => ((jacobiSym (n : ℤ) q : ℤ) : ℂ) ^ i.1) d‖ ≤
      x ^ ((1 : ℝ) / 2 + eps) / 2) :
    BoundsAtX x eps C f (8 * q * d) := by
  intro N _ χ hχ
  have hχ' : GlobalTheoryTheory.Induces χ
      (fun a => GlobalTheoryTheory.chi8 a ^ (0 : Fin 2).1 * GlobalTheoryTheory.chDir d a * GlobalTheoryTheory.psDir q a ^ i.1) (8 * q * d) :=
    ⟨hχ.1, fun a ha => by rw [hχ.2 a ha, hf]; simp⟩
  obtain ⟨-, -, hne, -, hval⟩ := GlobalTheory.QuadPrim.main q d hq hd hq4 hd4 hqd i 1 0 (by simp) N χ
    (by simpa using hχ')
  obtain ⟨h1, h2⟩ := htail N χ hne (hgood N χ hχ')
  refine ⟨?_, h2⟩
  have e : ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, (GlobalTheoryTheory.cn x n : ℂ) * χ (n : ZMod N) =
      Formalism.HermitianLattices.GL2PrimeSums.sqSum x (fun n => ((jacobiSym (n : ℤ) q : ℤ) : ℂ) ^ i.1) d := by
    refine sum_congr rfl fun n hn => ?_
    have hn0 : 0 < n := (mem_Icc.1 hn).1
    rw [hval n hn0 rfl, GlobalTheoryTheory.chDir, GlobalTheoryTheory.psDir, GlobalTheoryTheory.kron, GlobalTheoryTheory.kron,
      GlobalTheory.kronSym_neg_eq_jacobiSym_and_two.1 d n hd4 hn0,
      GlobalTheory.kronSym_neg_eq_jacobiSym_and_two.1 q n hq4 hn0]
    have : GlobalTheoryTheory.cn x n = Formalism.HermitianLattices.GL2PrimeSums.cn x n := rfl
    rw [this]
    simp only [Fin.val_one, pow_one]
    ring
  rw [e] at h1
  have h3 := norm_sub_le (GlobalTheoryTheory.gChi χ x +
    Formalism.HermitianLattices.GL2PrimeSums.sqSum x (fun n => ((jacobiSym (n : ℤ) q : ℤ) : ℂ) ^ i.1) d)
    (Formalism.HermitianLattices.GL2PrimeSums.sqSum x (fun n => ((jacobiSym (n : ℤ) q : ℤ) : ℂ) ^ i.1) d)
  rw [add_sub_cancel_right] at h3
  linarith

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `p1 p2 p3 p4 p5 p6 p7 p8 eps he he'`. Take `⟨C₁, hC₁, Hbad⟩` from `GlobalTheory.FewBadChars.badChars_count_of_density p8`. Take `⟨x₁, C, hC, Htail⟩` from `GlobalTheory.T.g_chi_approximation_sum p1 p2 p3 p4 p5 eps he he'`. Take `⟨x₂, Hcard⟩` from `GlobalTheory.Mem.An.card_primes_residue_ge_rpow p6 eps he he'`. Take `⟨x₃, C₃, Hms⟩` from `GlobalTheory.T.multiplicative_weight_prime_sum p6 p7 p5 eps he he'`.

Take `⟨x₀, H₀⟩` from `eventually_atTop.1 ((sizes eps C₃ C₁ he).and ((eventually_ge_atTop x₁).and ((eventually_ge_atTop x₂).and (eventually_ge_atTop x₃))))`. Use `⟨x₀, C, hC, fun x hx q hq hq8 hq1 hq2 => ?_⟩` and prove the remaining obligations. Take `⟨⟨s1, s2, s3, s4, s5, s6, s7⟩, hx1, hx2, hx3⟩` from `H₀ x hx`. Establish `hx0 : 0 < x` using `by linarith`. Establish `hx1' : 1 ≤ x` using `by linarith`.

Establish `hq4 : q % 4 = 3` using `by omega`. Establish `hq0 : (0 : ℝ) < q` using `by exact_mod_cast hq.pos`. Establish `h65 : x ^ (eps / 6) ≤ x ^ (eps / 5)` using `Real.rpow_le_rpow_of_exponent_le hx1' (by linarith)`. Establish `h4 : x ^ (eps / 4) = x ^ (eps / 5) * x ^ (eps / 20)`. Rewrite using `[← Real.rpow_add hx0]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Unfold `GlobalTheoryTheory.X1 at hq1 hq2`. Unfold `GlobalTheoryTheory.X1 GlobalTheoryTheory.X2`. Rewrite `hq1` using `[← Real.exp_half]`.

Use `set y := x ^ (eps / 5) with hy`. Use `set L := Real.log x with hL`. Establish `hL2 : 4 ≤ L ^ 2` using `by nlinarith`. Establish `hyL : 4 * y ≤ y * L ^ 2` using `by nlinarith`. Establish `hl2` using `Real.log_two_lt_d9`.

Establish `hl2'` using `Real.log_two_gt_d9`. Establish `hl8 : Real.log 8 = 3 * Real.log 2`. Rewrite using `[show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num`. Establish `hl16 : Real.log 16 = 4 * Real.log 2`. Rewrite using `[show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num`.

Establish `hl4 : Real.log 4 = 2 * Real.log 2`. Rewrite using `[show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num`. Take `⟨M, hM2, hMq, hMp, hMd, hMle⟩` from `exists_modulus ⌊y⌋₊ q hq (by omega)`. Establish `hM0 : 0 < M` using `by omega`. Establish `hM0' : (0 : ℝ) < M` using `by exact_mod_cast hM0`.

Establish `hcop : Nat.Coprime (8 * M - 1) (16 * M)`. Establish `h1 : Nat.Coprime (8 * M - 1) (8 * M)`. Establish `: 8 * M = (8 * M - 1) + 1` using `by omega`. Use `conv_rhs => rw [this]`. Simplify using the standard rewrite rules.

Establish `h2 : Nat.Coprime (8 * M - 1) 2` using `Nat.coprime_two_right.2 (Nat.odd_iff.2 (by omega))`. Use `Nat.Coprime.mul_right h2 h1` as an intermediate fact. Rewrite `this` using `[← mul_assoc]`. Then use the resulting hypothesis. Establish `hqz : x ^ (400 : ℝ) < q`. Use `lt_of_le_of_lt ?_ hq1` and prove the remaining obligations.

Rewrite using `[Real.rpow_def_of_pos hx0]`. Conclude with `Real.exp_le_exp.2 (by linarith)`. Establish `hprimes : ∀ p : ℕ, p.Prime → p ∣ 16 * M → (p : ℝ) ≤ y ∨ x ^ (400 : ℝ) < p`. Introduce `p hp hd`. Break down `(Nat.Prime.dvd_mul hp).1 hd with h | h` into its components or cases.

Establish `h' : p ∣ 2` using `hp.dvd_of_dvd_pow (show p ∣ 2 ^ 4 from h)`. Establish `: (p : ℝ) ≤ 2` using `by exact_mod_cast Nat.le_of_dvd two_pos h'`. Conclude with `Or.inl (by linarith)`. Break down `hMd p hp h with h' | rfl` into its components or cases. Conclude with `Or.inl ((Nat.le_floor_iff (by linarith)).1 h')`.

Conclude with `Or.inr hqz`. Establish `hlogm : (1 / 4) * L ^ 2 * Real.log ((16 * M : ℕ) : ℝ) ≤ Real.log (Real.exp (y * L ^ 2))`. Establish `h1 : (M : ℝ) ≤ q * 4 ^ ⌊y⌋₊` using `by exact_mod_cast hMle`. Establish `h2` using `Real.log_le_log hM0' h1`. Rewrite `h2` using `[Real.log_mul hq0.ne' (by positivity), Real.log_pow]`.

Establish `h3 : Real.log q ≤ y` using `(Real.log_le_iff_le_exp hq0).2 hq2`. Establish `h5 : (⌊y⌋₊ : ℝ) ≤ y` using `Nat.floor_le (by linarith)`. Establish `h6 : (⌊y⌋₊ : ℝ) * Real.log 4 ≤ y * 1.4` using `mul_le_mul h5 (by linarith) (by linarith) (by linarith)`. Rewrite using `[Real.log_exp, Nat.cast_mul, Real.log_mul (by norm_num) hM0'.ne', Nat.cast_ofNat]`. Establish `h7 : Real.log 16 + Real.log M ≤ 4 * y` using `by linarith`.

Establish `h8` using `mul_le_mul_of_nonneg_left h7 (sq_nonneg L)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlogX : x ^ (eps / 6) ≤ Real.log (Real.exp (y * L ^ 2))`. Rewrite using `[Real.log_exp]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hP` using `Hcard x hx2 (16 * M) (8 * M - 1) (by omega) hcop _ (Real.exp_pos _) hlogm hlogX`. Establish `hms` using `fun i : Fin 2 => Hms x hx3 (16 * M) (8 * M - 1) (Dvd.intro (2 * M) (by ring)) (by omega) hcop (by omega) hprimes _ (Real.exp_pos _) hlogm hlogX (fun n => ((jacobiSym (n : ℤ) q : ℤ) : ℂ) ^ i.1) (by simp) (fun m n => by rw [Nat.cast_mul, jacobiSym.mul_left, Int.cast_mul, mul_pow]) …`. Rewrite using `[norm_pow]`. Use `pow_le_one₀ (norm_nonneg _) ?_` and prove the remaining obligations. Apply the tactic sequence `rcases jacobiSym.trichotomy (n : ℤ) q with h | h | h <;> simp [h])`.

Use `set Q := 8 * Real.exp y * Real.exp (y * L ^ 2) with hQ`. Establish `hQ0 : 0 < Q` using `by positivity`. Establish `hlogQ : Real.log Q = Real.log 8 + y + y * L ^ 2`. Rewrite using `[hQ, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_exp]`. Establish `hQ3 : 3 ≤ Q`.

Use `Real.log_le_sub_one_of_pos hQ0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨B, hB, HB⟩` from `exists_bad_set Q _ (by positivity) (Hbad Q hQ3) q hq hq4`. Establish `hBP : 2 * (B.card : ℝ) < (Formalism.HermitianLattices.GL2PrimeSums.PP (16 * M) (8 * M - 1) (Real.exp (y * L ^ 2))).card`. Use `lt_of_lt_of_le ?_ hP` and prove the remaining obligations.

Establish `h1 : 8 * C₁ < Real.exp y`. Use `Real.add_one_le_exp y` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : 0 < Q ^ ((1 : ℝ) / 4)` using `by positivity`. Establish `h3 : Real.exp y * Q ^ ((1 : ℝ) / 4) ≤ Real.exp (y * L ^ 2) ^ ((9 : ℝ) / 10)`.

Rewrite using `[Real.rpow_def_of_pos hQ0, ← Real.exp_mul, ← Real.exp_add, hlogQ]`. Conclude with `Real.exp_le_exp.2 (by linarith)`. Establish `h5` using `mul_lt_mul_of_pos_right h1 h2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hT : 4 * (C₃ * x * L) ≤ (x ^ ((1 : ℝ) / 2 + eps) / 2) ^ 2`.

Establish `h1 : (x ^ ((1 : ℝ) / 2 + eps)) ^ 2 = x * x ^ (2 * eps)`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hx0.le, mul_comm x, ← Real.rpow_add_one hx0.ne']`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `h2` using `mul_le_mul_of_nonneg_left s6 hx0.le`. Rewrite using `[div_pow, h1]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨d, hdP, hdB, hd0, hd1⟩` from `exists_small_pair _ B _ _ _ _ (by positivity) hBP (hms 0) (hms 1) hT`. Take `⟨hdI, hd, hdm⟩` from `mem_filter.1 hdP`.

Take `⟨hdl, hdu⟩` from `mem_Ioc.1 hdI`. Establish `hdl' : Real.sqrt (Real.exp (y * L ^ 2)) < d` using `(Nat.floor_lt (Real.sqrt_nonneg _)).1 hdl`. Establish `hdu' : (d : ℝ) ≤ Real.exp (y * L ^ 2)` using `(Nat.le_floor_iff (Real.exp_pos _).le).1 hdu`. Establish `hd16 : d % 16 = 7`. Establish `: d % 16 = (8 * M - 1) % 16` using `hdm.of_mul_right M`.

Use linear arithmetic over natural numbers and integers. Establish `hMdvd : M ∣ d + 1`. Establish `h1 : d + 1 ≡ 8 * M - 1 + 1 [MOD M]` using `(hdm.of_mul_left 16).add_right 1`. Rewrite `h1` using `[show 8 * M - 1 + 1 = 8 * M by omega]`. Conclude with `(Nat.modEq_zero_iff_dvd.1 (h1.trans (Nat.modEq_zero_iff_dvd.2 (dvd_mul_left M 8))))`.

Establish `hqd : q ≠ d`. Introduce and unpack `rfl`. Rewrite `hdl'` using `[← Real.exp_half]`. Use `Real.exp_lt_exp.1 (hdl'.trans_le hq2)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hgood` using `HB d hd (by omega) hqd (by rw [hQ]; gcongr) hdB`. Establish `hxe : x ^ eps ≤ x ^ ((1 : ℝ) / 2 + eps) / 2`. Rewrite using `[Real.rpow_add hx0, ← Real.sqrt_eq_rpow]`. Establish `h1 : 2 ≤ Real.sqrt x` using `Real.le_sqrt_of_sq_le (by linarith)`. Establish `h2 : 0 < x ^ eps` using `by positivity`.

Establish `h3` using `mul_le_mul_of_nonneg_right h1 h2.le`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `htail` using `fun (N : ℕ) (_ : NeZero N) (χ : DirichletCharacter ℂ N) => Htail x hx1 Q N χ hQ0 (by linarith) (by`. Establish `h1` using `mul_le_mul_of_nonneg_left s5 (show 0 ≤ y by linarith)`. Rewrite using `[h4, hlogQ]`.

Use the proof step `linarith)`. Use `⟨d, hd, hd16, hdl', hdu', kronSym_eq_one_of_dvd d q (by omega) (hMq.trans hMdvd), ?_, hgood, boundsAtX_of_good x eps C Q q d hq hd hq4 (by omega) hqd 0 _ (by simp) hxe (hgood 0 0) htail hd0, boundsAtX_of_good x eps C Q q d hq hd hq4 (by omega) hqd 1 _ (by simp) hxe (hgood 1 0) ht …` and prove the remaining obligations. Introduce `p hp hpy`. Distinguish the cases in `h2 : p = 2`. Substitute `h2` using the available equality.

Conclude with `kronSym_two_eq_one d (by omega)`. Conclude with `kronSym_eq_one_of_dvd d p (Nat.odd_iff.1 (hp.odd_of_ne_two h2)) ((hMp p hp h2 (Nat.le_floor hpy)).trans hMdvd)`.
-/
theorem exists_prime_split_good_bounds : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → GlobalTheory.Mem.An.TZRat → GlobalTheory.Mem.An.PageThm → GlobalTheory.Mem.An.Jutila → ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ C : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x → ∀ q : ℕ, q.Prime → q % 8 = 3 → Real.sqrt (GlobalTheoryTheory.X1 x eps) < q → (q : ℝ) ≤ GlobalTheoryTheory.X1 x eps → ∃ d : ℕ, d.Prime ∧ d % 16 = 7 ∧ Real.sqrt (GlobalTheoryTheory.X2 x eps) < d ∧ (d : ℝ) ≤ GlobalTheoryTheory.X2 x eps ∧ GlobalTheoryTheory.kronSym (-(d : ℤ)) q = 1 ∧ (∀ p : ℕ, p.Prime → (p : ℝ) ≤ x ^ (eps / 5) → GlobalTheoryTheory.kronSym (-(d : ℤ)) p = 1) ∧ (∀ i k : Fin 2, GoodAllFor (8 * GlobalTheoryTheory.X1 x eps * GlobalTheoryTheory.X2 x eps) (fun a => GlobalTheoryTheory.chi8 a ^ k.1 * GlobalTheoryTheory.chDir d a * GlobalTheoryTheory.psDir q a ^ i.1) (8 * q * d)) ∧ BoundsAtX x eps C (GlobalTheoryTheory.chDir d) (8 * q * d) ∧ BoundsAtX x eps C (fun a => GlobalTheoryTheory.chDir d a * GlobalTheoryTheory.psDir q a) (8 * q * d) := by
  intro p1 p2 p3 p4 p5 p6 p7 p8 eps he he'
  obtain ⟨C₁, hC₁, Hbad⟩ := GlobalTheory.FewBadChars.badChars_count_of_density p8
  obtain ⟨x₁, C, hC, Htail⟩ := GlobalTheory.T.g_chi_approximation_sum p1 p2 p3 p4 p5 eps he he'
  obtain ⟨x₂, Hcard⟩ := GlobalTheory.Mem.An.card_primes_residue_ge_rpow p6 eps he he'
  obtain ⟨x₃, C₃, Hms⟩ := GlobalTheory.T.multiplicative_weight_prime_sum p6 p7 p5 eps he he'
  obtain ⟨x₀, H₀⟩ := eventually_atTop.1 ((sizes eps C₃ C₁ he).and ((eventually_ge_atTop x₁).and
    ((eventually_ge_atTop x₂).and (eventually_ge_atTop x₃))))
  refine ⟨x₀, C, hC, fun x hx q hq hq8 hq1 hq2 => ?_⟩
  obtain ⟨⟨s1, s2, s3, s4, s5, s6, s7⟩, hx1, hx2, hx3⟩ := H₀ x hx
  have hx0 : 0 < x := by linarith
  have hx1' : 1 ≤ x := by linarith
  have hq4 : q % 4 = 3 := by omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have h65 : x ^ (eps / 6) ≤ x ^ (eps / 5) := Real.rpow_le_rpow_of_exponent_le hx1' (by linarith)
  have h4 : x ^ (eps / 4) = x ^ (eps / 5) * x ^ (eps / 20) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  unfold GlobalTheoryTheory.X1 at hq1 hq2
  unfold GlobalTheoryTheory.X1 GlobalTheoryTheory.X2
  rw [← Real.exp_half] at hq1
  set y := x ^ (eps / 5) with hy
  set L := Real.log x with hL
  have hL2 : 4 ≤ L ^ 2 := by nlinarith
  have hyL : 4 * y ≤ y * L ^ 2 := by nlinarith
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have hl8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have hl16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num

  obtain ⟨M, hM2, hMq, hMp, hMd, hMle⟩ := exists_modulus ⌊y⌋₊ q hq (by omega)
  have hM0 : 0 < M := by omega
  have hM0' : (0 : ℝ) < M := by exact_mod_cast hM0
  have hcop : Nat.Coprime (8 * M - 1) (16 * M) := by
    have h1 : Nat.Coprime (8 * M - 1) (8 * M) := by
      have : 8 * M = (8 * M - 1) + 1 := by omega
      conv_rhs => rw [this]
      simp
    have h2 : Nat.Coprime (8 * M - 1) 2 := Nat.coprime_two_right.2 (Nat.odd_iff.2 (by omega))
    have := Nat.Coprime.mul_right h2 h1
    rwa [← mul_assoc] at this
  have hqz : x ^ (400 : ℝ) < q := by
    refine lt_of_le_of_lt ?_ hq1
    rw [Real.rpow_def_of_pos hx0]
    exact Real.exp_le_exp.2 (by linarith)
  have hprimes : ∀ p : ℕ, p.Prime → p ∣ 16 * M → (p : ℝ) ≤ y ∨ x ^ (400 : ℝ) < p := by
    intro p hp hd
    rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
    · have h' : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 4 from h)
      have : (p : ℝ) ≤ 2 := by exact_mod_cast Nat.le_of_dvd two_pos h'
      exact Or.inl (by linarith)
    · rcases hMd p hp h with h' | rfl
      · exact Or.inl ((Nat.le_floor_iff (by linarith)).1 h')
      · exact Or.inr hqz
  have hlogm : (1 / 4) * L ^ 2 * Real.log ((16 * M : ℕ) : ℝ) ≤ Real.log (Real.exp (y * L ^ 2)) := by
    have h1 : (M : ℝ) ≤ q * 4 ^ ⌊y⌋₊ := by exact_mod_cast hMle
    have h2 := Real.log_le_log hM0' h1
    rw [Real.log_mul hq0.ne' (by positivity), Real.log_pow] at h2
    have h3 : Real.log q ≤ y := (Real.log_le_iff_le_exp hq0).2 hq2
    have h5 : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le (by linarith)
    have h6 : (⌊y⌋₊ : ℝ) * Real.log 4 ≤ y * 1.4 :=
      mul_le_mul h5 (by linarith) (by linarith) (by linarith)
    rw [Real.log_exp, Nat.cast_mul, Real.log_mul (by norm_num) hM0'.ne', Nat.cast_ofNat]
    have h7 : Real.log 16 + Real.log M ≤ 4 * y := by linarith
    have h8 := mul_le_mul_of_nonneg_left h7 (sq_nonneg L)
    linarith
  have hlogX : x ^ (eps / 6) ≤ Real.log (Real.exp (y * L ^ 2)) := by
    rw [Real.log_exp]; linarith
  have hP := Hcard x hx2 (16 * M) (8 * M - 1) (by omega) hcop _ (Real.exp_pos _) hlogm hlogX
  have hms := fun i : Fin 2 => Hms x hx3 (16 * M) (8 * M - 1) (Dvd.intro (2 * M) (by ring)) (by omega) hcop
    (by omega) hprimes _ (Real.exp_pos _) hlogm hlogX (fun n => ((jacobiSym (n : ℤ) q : ℤ) : ℂ) ^ i.1)
    (by simp) (fun m n => by rw [Nat.cast_mul, jacobiSym.mul_left, Int.cast_mul, mul_pow])
    (fun n => by
      rw [norm_pow]
      refine pow_le_one₀ (norm_nonneg _) ?_
      rcases jacobiSym.trichotomy (n : ℤ) q with h | h | h <;> simp [h])

  set Q := 8 * Real.exp y * Real.exp (y * L ^ 2) with hQ
  have hQ0 : 0 < Q := by positivity
  have hlogQ : Real.log Q = Real.log 8 + y + y * L ^ 2 := by
    rw [hQ, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_exp, Real.log_exp]
  have hQ3 : 3 ≤ Q := by
    have := Real.log_le_sub_one_of_pos hQ0
    linarith
  obtain ⟨B, hB, HB⟩ := exists_bad_set Q _ (by positivity) (Hbad Q hQ3) q hq hq4
  have hBP : 2 * (B.card : ℝ) < (Formalism.HermitianLattices.GL2PrimeSums.PP (16 * M) (8 * M - 1) (Real.exp (y * L ^ 2))).card := by
    refine lt_of_lt_of_le ?_ hP
    have h1 : 8 * C₁ < Real.exp y := by
      have := Real.add_one_le_exp y
      linarith
    have h2 : 0 < Q ^ ((1 : ℝ) / 4) := by positivity
    have h3 : Real.exp y * Q ^ ((1 : ℝ) / 4) ≤ Real.exp (y * L ^ 2) ^ ((9 : ℝ) / 10) := by
      rw [Real.rpow_def_of_pos hQ0, ← Real.exp_mul, ← Real.exp_add, hlogQ]
      exact Real.exp_le_exp.2 (by linarith)
    have h5 := mul_lt_mul_of_pos_right h1 h2
    linarith
  have hT : 4 * (C₃ * x * L) ≤ (x ^ ((1 : ℝ) / 2 + eps) / 2) ^ 2 := by
    have h1 : (x ^ ((1 : ℝ) / 2 + eps)) ^ 2 = x * x ^ (2 * eps) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, mul_comm x, ← Real.rpow_add_one hx0.ne']
      congr 1; push_cast; ring
    have h2 := mul_le_mul_of_nonneg_left s6 hx0.le
    rw [div_pow, h1]
    linarith
  obtain ⟨d, hdP, hdB, hd0, hd1⟩ := exists_small_pair _ B _ _ _ _ (by positivity) hBP (hms 0) (hms 1) hT
  obtain ⟨hdI, hd, hdm⟩ := mem_filter.1 hdP
  obtain ⟨hdl, hdu⟩ := mem_Ioc.1 hdI
  have hdl' : Real.sqrt (Real.exp (y * L ^ 2)) < d := (Nat.floor_lt (Real.sqrt_nonneg _)).1 hdl
  have hdu' : (d : ℝ) ≤ Real.exp (y * L ^ 2) := (Nat.le_floor_iff (Real.exp_pos _).le).1 hdu
  have hd16 : d % 16 = 7 := by
    have : d % 16 = (8 * M - 1) % 16 := hdm.of_mul_right M
    omega
  have hMdvd : M ∣ d + 1 := by
    have h1 : d + 1 ≡ 8 * M - 1 + 1 [MOD M] := (hdm.of_mul_left 16).add_right 1
    rw [show 8 * M - 1 + 1 = 8 * M by omega] at h1
    exact (Nat.modEq_zero_iff_dvd.1 (h1.trans (Nat.modEq_zero_iff_dvd.2 (dvd_mul_left M 8))))
  have hqd : q ≠ d := by
    rintro rfl
    rw [← Real.exp_half] at hdl'
    have := Real.exp_lt_exp.1 (hdl'.trans_le hq2)
    linarith
  have hgood := HB d hd (by omega) hqd (by rw [hQ]; gcongr) hdB
  have hxe : x ^ eps ≤ x ^ ((1 : ℝ) / 2 + eps) / 2 := by
    rw [Real.rpow_add hx0, ← Real.sqrt_eq_rpow]
    have h1 : 2 ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by linarith)
    have h2 : 0 < x ^ eps := by positivity
    have h3 := mul_le_mul_of_nonneg_right h1 h2.le
    linarith
  have htail := fun (N : ℕ) (_ : NeZero N) (χ : DirichletCharacter ℂ N) =>
    Htail x hx1 Q N χ hQ0 (by linarith) (by
      have h1 := mul_le_mul_of_nonneg_left s5 (show 0 ≤ y by linarith)
      rw [h4, hlogQ]; linarith)
  refine ⟨d, hd, hd16, hdl', hdu', kronSym_eq_one_of_dvd d q (by omega) (hMq.trans hMdvd), ?_, hgood,
    boundsAtX_of_good x eps C Q q d hq hd hq4 (by omega) hqd 0 _ (by simp) hxe (hgood 0 0) htail hd0,
    boundsAtX_of_good x eps C Q q d hq hd hq4 (by omega) hqd 1 _ (by simp) hxe (hgood 1 0) htail hd1⟩
  intro p hp hpy
  by_cases h2 : p = 2
  · subst h2
    exact kronSym_two_eq_one d (by omega)
  · exact kronSym_eq_one_of_dvd d p (Nat.odd_iff.1 (hp.odd_of_ne_two h2))
      ((hMp p hp h2 (Nat.le_floor hpy)).trans hMdvd)

end GlobalTheory.SplitPrimeChoice
