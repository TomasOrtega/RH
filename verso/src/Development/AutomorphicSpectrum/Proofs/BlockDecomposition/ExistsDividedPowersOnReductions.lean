import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerQuotientExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineFiltrationMultiplicativeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationDividedPowerStructuresStatement

set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PerfFil

/- English proof (translation)
Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Simplify using the standard rewrite rules. Take `⟨x', rfl⟩` from `Ideal.mem_span_singleton'.1 hx`. Use `haveI := Fact.mk hl`. Take `⟨v, m, hlm, hm⟩` from `Nat.exists_eq_pow_mul_and_not_dvd k.factorial_ne_zero l hl.ne_one`.

Establish `hv : v < k`. Establish `h1 : v ≤ padicValNat l k.factorial` using `(padicValNat_dvd_iff_le k.factorial_ne_zero).1 ⟨m, hm⟩`. Establish `h2` using `sub_one_mul_padicValNat_factorial_lt_of_ne_zero (p := l) hk`. Establish `h3 : 1 ≤ l - 1` using `Nat.le_sub_of_add_le hl.two_le`. Use the polynomial consequences of the given equalities and inequalities.

Choose the witnesses or unpack the hypotheses as in `⟨t, ht⟩ : ∃ t, n * k = n + v + t := by`. Take `⟨k', rfl⟩` from `Nat.exists_eq_succ_of_ne_zero hk`. Use `⟨n * k' - v, ?_⟩` and prove the remaining obligations. Establish `: v ≤ n * k'` using `by nlinarith [Nat.lt_succ_iff.1 hv]`. Rewrite using `[Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one]`.

Use linear arithmetic over natural numbers and integers. Establish `hfac : (k.factorial : S) = (l : S) ^ v * (m : S)` using `by rw [hm]; push_cast; rfl`. Establish `e2 : (l : S) ^ v * ((m : S) * y) = (l : S) ^ v * ((l : S) ^ n * ((l : S) ^ t * x' ^ k))`. Rewrite using `[← mul_assoc, ← hfac, e, mul_pow, ← pow_mul, ht, pow_add, pow_add]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hr : (l : S) ^ v ∈ nonZeroDivisors S` using `pow_mem (hS l hl.ne_zero) v`. Establish `e3 : (m : S) * y = (l : S) ^ n * ((l : S) ^ t * x' ^ k)`. Establish `h0 : (l : S) ^ v * ((m : S) * y - (l : S) ^ n * ((l : S) ^ t * x' ^ k)) = 0`. Rewrite using `[mul_sub, e2, sub_self]`. Conclude with `sub_eq_zero.1 ((mem_nonZeroDivisors_iff_right.1 hr) _ (by rwa [mul_comm] at h0))`.

Establish `hc : IsCoprime (m : ℤ) ((l : ℤ) ^ n)`. Apply `IsCoprime.pow_right` to reduce the goal to its premises. Rewrite using `[Nat.isCoprime_iff_coprime]`. Conclude with `((Nat.Prime.coprime_iff_not_dvd hl).2 hlm).symm`. Take `⟨a, b, hab⟩` from `hc`.

Establish `hab' : (a : S) * (m : S) + (b : S) * (l : S) ^ n = 1`. Conclude with `congrArg (Int.cast : ℤ → S) hab` after adjusting the coercions. Establish `hy : y = ((a : S) * ((l : S) ^ t * x' ^ k) + (b : S) * y) * (l : S) ^ n`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hy]`.

Conclude with `Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)`.
-/
theorem mem_span_pow_of_factorial_mul_eq {S : Type} [CommRing S] (hS : R.TF S) {l : ℕ}
    (hl : l.Prime) (n : ℕ) {x : S} (hx : x ∈ Ideal.span {(l : S) ^ n}) {k : ℕ} (hk : k ≠ 0)
    {y : S} (e : (k.factorial : S) * y = x ^ k) : y ∈ Ideal.span {(l : S) ^ n} := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  obtain ⟨x', rfl⟩ := Ideal.mem_span_singleton'.1 hx
  haveI := Fact.mk hl
  obtain ⟨v, m, hlm, hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd k.factorial_ne_zero l hl.ne_one
  have hv : v < k := by
    have h1 : v ≤ padicValNat l k.factorial :=
      (padicValNat_dvd_iff_le k.factorial_ne_zero).1 ⟨m, hm⟩
    have h2 := sub_one_mul_padicValNat_factorial_lt_of_ne_zero (p := l) hk
    have h3 : 1 ≤ l - 1 := Nat.le_sub_of_add_le hl.two_le
    nlinarith
  obtain ⟨t, ht⟩ : ∃ t, n * k = n + v + t := by
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    refine ⟨n * k' - v, ?_⟩
    have : v ≤ n * k' := by nlinarith [Nat.lt_succ_iff.1 hv]
    rw [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one]
    omega
  have hfac : (k.factorial : S) = (l : S) ^ v * (m : S) := by rw [hm]; push_cast; rfl
  have e2 : (l : S) ^ v * ((m : S) * y) = (l : S) ^ v * ((l : S) ^ n * ((l : S) ^ t * x' ^ k)) := by
    rw [← mul_assoc, ← hfac, e, mul_pow, ← pow_mul, ht, pow_add, pow_add]
    ring
  have hr : (l : S) ^ v ∈ nonZeroDivisors S := pow_mem (hS l hl.ne_zero) v
  have e3 : (m : S) * y = (l : S) ^ n * ((l : S) ^ t * x' ^ k) := by
    have h0 : (l : S) ^ v * ((m : S) * y - (l : S) ^ n * ((l : S) ^ t * x' ^ k)) = 0 := by
      rw [mul_sub, e2, sub_self]
    exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff_right.1 hr) _ (by rwa [mul_comm] at h0))
  have hc : IsCoprime (m : ℤ) ((l : ℤ) ^ n) := by
    apply IsCoprime.pow_right
    rw [Nat.isCoprime_iff_coprime]
    exact ((Nat.Prime.coprime_iff_not_dvd hl).2 hlm).symm
  obtain ⟨a, b, hab⟩ := hc
  have hab' : (a : S) * (m : S) + (b : S) * (l : S) ^ n = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → S) hab
  have hy : y = ((a : S) * ((l : S) ^ t * x' ^ k) + (b : S) * y) * (l : S) ^ n := by
    calc y = ((a : S) * (m : S) + (b : S) * (l : S) ^ n) * y := by rw [hab', one_mul]
      _ = (a : S) * ((m : S) * y) + (b : S) * (l : S) ^ n * y := by ring
      _ = _ := by rw [e3]; ring
  rw [hy]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

/- English proof (translation)
Substitute `hK` using the available equality. Conclude with `GlobalTheory.CompanionTheory.PdTF.exists_dividedPowers_map_quotient A.acris_torsion_free I (Ideal.span {(l : A.Acr0) ^ n}) hI fun x _ hx k hk y e => mem_span_pow_of_factorial_mul_eq A.acris_torsion_free hl.out n hx hk e`.
-/
theorem exists_dividedPowers_map_mkAcr {l : ℕ} [hl : Fact l.Prime] (A : PAlg l) (n : ℕ)
    (I : Ideal A.Acr0) (hI : R.PdI I) (K : Ideal (A.Acr n)) (hK : K = I.map (A.mkAcr n)) :
    ∃ δ : DividedPowers K, R.IsPd (A.mkAcr n) I δ := by
  subst hK
  exact GlobalTheory.CompanionTheory.PdTF.exists_dividedPowers_map_quotient A.acris_torsion_free I
    (Ideal.span {(l : A.Acr0) ^ n}) hI
    fun x _ hx k hk y e => mem_span_pow_of_factorial_mul_eq A.acris_torsion_free hl.out n hx hk e

/- English proof (translation)
Introduce `l _ A n`. Take `⟨-, -, -, -, h1, h2, -⟩` from `GlobalTheory.T.crystalline_filtration_multiplicative A`. Take `⟨p1, p2, -⟩` from `GlobalTheory.T.filtration_divided_power_structures A`. Conclude with `⟨exists_dividedPowers_map_mkAcr A n _ p1 _ (h1 n 1), exists_dividedPowers_map_mkAcr A n _ p2 _ (h2 n)⟩`.
-/
theorem exists_dividedPowers_fil_pfil : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ),
    (∃ δ : DividedPowers (A.Fil n 1), R.IsPd (A.mkAcr n) (A.Fil0 1) δ) ∧
      ∃ δ : DividedPowers (A.PFil n), R.IsPd (A.mkAcr n) A.PFil0 δ := by
  intro l _ A n
  obtain ⟨-, -, -, -, h1, h2, -⟩ := GlobalTheory.T.crystalline_filtration_multiplicative A
  obtain ⟨p1, p2, -⟩ := GlobalTheory.T.filtration_divided_power_structures A
  exact ⟨exists_dividedPowers_map_mkAcr A n _ p1 _ (h1 n 1),
    exists_dividedPowers_map_mkAcr A n _ p2 _ (h2 n)⟩

end GlobalTheory.CompanionTheory.PerfFil
