import Formalism.PadicSubsetSums.CentralIdempotents.EigenbasisOfDistinctRoots

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih`. Take `⟨ih1, ih2⟩` from `ih fun l hl => hf l (Finset.mem_insert_of_mem hl)`. Establish `hfa : 2 ≤ f a` using `hf a (Finset.mem_insert_self a s)`.

Rewrite using `[Finset.sum_insert ha, Finset.prod_insert ha]`. Use `⟨?_, by nlinarith⟩` and prove the remaining obligations. Break down `s.eq_empty_or_nonempty with hs | ⟨b, hb⟩` into its components or cases. Substitute `hs` using the available equality. Simplify using the standard rewrite rules.

Establish `hP2 : 2 ≤ ∏ l ∈ s, f l` using `(hf b (Finset.mem_insert_of_mem hb)).trans (Finset.single_le_prod' (fun l hl => by`. Use `hf l (Finset.mem_insert_of_mem hl)` as an intermediate fact. Use the proof step `omega) hb)`. Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem sum_le_prod_of_two_le (s : Finset ℕ) (f : ℕ → ℕ) (hf : ∀ l ∈ s, 2 ≤ f l) :
    ∑ l ∈ s, f l ≤ ∏ l ∈ s, f l ∧ 1 ≤ ∏ l ∈ s, f l := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih fun l hl => hf l (Finset.mem_insert_of_mem hl)
    have hfa : 2 ≤ f a := hf a (Finset.mem_insert_self a s)
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    refine ⟨?_, by nlinarith⟩
    rcases s.eq_empty_or_nonempty with hs | ⟨b, hb⟩
    · subst hs
      simp
    · have hP2 : 2 ≤ ∏ l ∈ s, f l :=
        (hf b (Finset.mem_insert_of_mem hb)).trans
          (Finset.single_le_prod' (fun l hl => by
            have := hf l (Finset.mem_insert_of_mem hl)
            omega) hb)
      nlinarith

/- English proof (translation)
Establish `h1 : 16 * q ≤ y * z * P`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : 16 * q ≤ x * z * P`. Combine the equalities or inequalities in the displayed calculation. Establish `h3 : 16 * q ≤ x * y * P`.

Combine the equalities or inequalities in the displayed calculation. Establish `h4 : 16 * q * T ≤ x * y * z * P`. Establish `h5 : 16 * q ≤ x * y * z`. Combine the equalities or inequalities in the displayed calculation. Conclude with `Nat.mul_le_mul h5 hT`.

Use polynomial arithmetic with `[Nat.mul_le_mul_left x h1, Nat.mul_le_mul_left y h2, Nat.mul_le_mul_left z h3]`.
-/
private theorem one_sub_sum_mul_prod_le_prod (q x y z T P : ℕ) (hx : 16 ≤ x) (hy : q ≤ y) (hz : 16 ≤ z) (hqz : q ≤ z)
    (hT : T ≤ P) (hP : 1 ≤ P) : 4 * q * (x + (y + (z + T))) ≤ x * (y * (z * P)) := by
  have h1 : 16 * q ≤ y * z * P := by
    calc 16 * q = q * 16 * 1 := by ring
      _ ≤ y * z * P := Nat.mul_le_mul (Nat.mul_le_mul hy hz) hP
  have h2 : 16 * q ≤ x * z * P := by
    calc 16 * q = 16 * q * 1 := by ring
      _ ≤ x * z * P := Nat.mul_le_mul (Nat.mul_le_mul hx hqz) hP
  have h3 : 16 * q ≤ x * y * P := by
    calc 16 * q = 16 * q * 1 := by ring
      _ ≤ x * y * P := Nat.mul_le_mul (Nat.mul_le_mul hx hy) hP
  have h4 : 16 * q * T ≤ x * y * z * P := by
    have h5 : 16 * q ≤ x * y * z := by
      calc 16 * q = 16 * q * 1 := by ring
        _ ≤ x * y * z := Nat.mul_le_mul (Nat.mul_le_mul hx hy) (by omega)
    exact Nat.mul_le_mul h5 hT
  nlinarith [Nat.mul_le_mul_left x h1, Nat.mul_le_mul_left y h2, Nat.mul_le_mul_left z h3]

/- English proof (translation)
Introduce `g q₁ d hg hq hd hqd hq2 hd2 hM h16 hqn hdn`. Use `set n := g - 1 with hn`. Establish `hn0 : n ≠ 0` using `by omega`. Establish `h2n : 2 ∣ n` using `(show 2 ∣ 16 by norm_num).trans h16`. Establish `hmem : ∀ l, l.Prime → l ∣ n → l ∈ n.primeFactors` using `fun l hl hln => Nat.mem_primeFactors.mpr ⟨hl, hln, hn0⟩`.

Establish `hge : ∀ l, l.Prime → l ∣ n → l ≤ l ^ padicValNat l n`. Introduce `l hl hln`. Use `haveI := Fact.mk hl`. Establish `hv : 1 ≤ padicValNat l n` using `one_le_padicValNat_of_dvd hn0 hln`. Combine the equalities or inequalities in the displayed calculation.

Establish `hf2 : 16 ≤ 2 ^ padicValNat 2 n` using `by haveI := Fact.mk Nat.prime_two`. Establish `hv : 4 ≤ padicValNat 2 n` using `(padicValNat_dvd_iff_le hn0).mp (by norm_num; exact h16)`. Combine the equalities or inequalities in the displayed calculation. Establish `h2m` using `hmem 2 Nat.prime_two h2n`. Establish `hqm : q₁ ∈ n.primeFactors.erase 2` using `Finset.mem_erase.mpr ⟨hq2, hmem q₁ hq hqn⟩`.

Establish `hdm : d ∈ (n.primeFactors.erase 2).erase q₁` using `Finset.mem_erase.mpr ⟨fun h => hqd h.symm, Finset.mem_erase.mpr ⟨hd2, hmem d hd hdn⟩⟩`. Establish `hsum : ∑ l ∈ n.primeFactors, l ^ padicValNat l n = 2 ^ padicValNat 2 n + (q₁ ^ padicValNat q₁ n + (d ^ padicValNat d n + ∑ l ∈ ((n.primeFactors.erase 2).erase q₁).erase d, l ^ padicValNat l n))`. Rewrite using `[← Finset.add_sum_erase _ _ h2m, ← Finset.add_sum_erase _ _ hqm, ← Finset.add_sum_erase _ _ hdm]`. Establish `hprod : n = 2 ^ padicValNat 2 n * (q₁ ^ padicValNat q₁ n * (d ^ padicValNat d n * ∏ l ∈ ((n.primeFactors.erase 2).erase q₁).erase d, l ^ padicValNat l n))`. Establish `h1 : ∏ l ∈ n.primeFactors, l ^ padicValNat l n = n` using `by conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hn0]`.

Rewrite using `[Finsupp.prod, Nat.support_factorization]`. Use `Finset.prod_congr rfl fun l hl => ?_` and prove the remaining obligations. Rewrite using `[Nat.factorization_def n (Nat.prime_of_mem_primeFactors hl)]`. Rewrite `h1` using `[← Finset.mul_prod_erase _ _ h2m, ← Finset.mul_prod_erase _ _ hqm, ← Finset.mul_prod_erase _ _ hdm]`. Conclude with `h1.symm`.

Establish `hR2 : ∀ l ∈ ((n.primeFactors.erase 2).erase q₁).erase d, 2 ≤ l ^ padicValNat l n`. Introduce `l hl`. Establish `hl' : l ∈ n.primeFactors` using `Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hl))`. Establish `hlp` using `Nat.prime_of_mem_primeFactors hl'`. Conclude with `hlp.two_le.trans (hge l hlp (Nat.dvd_of_mem_primeFactors hl'))`.

Take `⟨hTP, hP1⟩` from `sum_le_prod_of_two_le _ (fun l => l ^ padicValNat l n) hR2`. Establish `hq16` using `hge q₁ hq hqn`. Establish `hd16` using `hge d hd hdn`. Establish `hnat : (∑ l ∈ n.primeFactors, l ^ padicValNat l n) * (4 * min q₁ d) ≤ n`. Rewrite using `[hsum]`.

Break down `le_total q₁ d with hle | hle` into its components or cases. Rewrite using `[min_eq_left hle]`. Establish `key` using `one_sub_sum_mul_prod_le_prod q₁ _ _ _ _ _ hf2 hq16 (le_trans (by omega : 16 ≤ d) hd16) (hle.trans hd16) hTP hP1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[min_eq_right hle]`.

Establish `key` using `one_sub_sum_mul_prod_le_prod d (2 ^ padicValNat 2 n) (d ^ padicValNat d n) (q₁ ^ padicValNat q₁ n) _ _ hf2 hd16 (le_trans (by omega : 16 ≤ q₁) hq16) (hle.trans hq16) hTP hP1`. Combine the equalities or inequalities in the displayed calculation. Establish `hnpos : (0 : ℝ) < n` using `Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)`. Establish `hmpos : (0 : ℝ) < 4 * ((min q₁ d : ℕ) : ℝ)` using `mul_pos (by norm_num) (Nat.cast_pos.mpr (lt_min hq.pos hd.pos))`. Rewrite using `[← Nat.cast_sum, div_le_div_iff₀ hnpos hmpos, one_mul]`.

Conclude with `hnat` after adjusting the coercions.
-/
theorem prime_power_order_share : PrimePowerOrderShare := by
  intro g q₁ d hg hq hd hqd hq2 hd2 hM h16 hqn hdn
  set n := g - 1 with hn
  have hn0 : n ≠ 0 := by omega
  have h2n : 2 ∣ n := (show 2 ∣ 16 by norm_num).trans h16
  have hmem : ∀ l, l.Prime → l ∣ n → l ∈ n.primeFactors := fun l hl hln =>
    Nat.mem_primeFactors.mpr ⟨hl, hln, hn0⟩
  have hge : ∀ l, l.Prime → l ∣ n → l ≤ l ^ padicValNat l n := by
    intro l hl hln
    haveI := Fact.mk hl
    have hv : 1 ≤ padicValNat l n := one_le_padicValNat_of_dvd hn0 hln
    calc l = l ^ 1 := (pow_one l).symm
      _ ≤ l ^ padicValNat l n := Nat.pow_le_pow_right hl.pos hv
  have hf2 : 16 ≤ 2 ^ padicValNat 2 n := by
    haveI := Fact.mk Nat.prime_two
    have hv : 4 ≤ padicValNat 2 n := (padicValNat_dvd_iff_le hn0).mp (by norm_num; exact h16)
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ padicValNat 2 n := Nat.pow_le_pow_right (by norm_num) hv
  have h2m := hmem 2 Nat.prime_two h2n
  have hqm : q₁ ∈ n.primeFactors.erase 2 := Finset.mem_erase.mpr ⟨hq2, hmem q₁ hq hqn⟩
  have hdm : d ∈ (n.primeFactors.erase 2).erase q₁ :=
    Finset.mem_erase.mpr ⟨fun h => hqd h.symm, Finset.mem_erase.mpr ⟨hd2, hmem d hd hdn⟩⟩
  have hsum : ∑ l ∈ n.primeFactors, l ^ padicValNat l n =
      2 ^ padicValNat 2 n + (q₁ ^ padicValNat q₁ n + (d ^ padicValNat d n +
        ∑ l ∈ ((n.primeFactors.erase 2).erase q₁).erase d, l ^ padicValNat l n)) := by
    rw [← Finset.add_sum_erase _ _ h2m, ← Finset.add_sum_erase _ _ hqm, ← Finset.add_sum_erase _ _ hdm]
  have hprod : n = 2 ^ padicValNat 2 n * (q₁ ^ padicValNat q₁ n * (d ^ padicValNat d n *
        ∏ l ∈ ((n.primeFactors.erase 2).erase q₁).erase d, l ^ padicValNat l n)) := by
    have h1 : ∏ l ∈ n.primeFactors, l ^ padicValNat l n = n := by
      conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hn0]
      rw [Finsupp.prod, Nat.support_factorization]
      refine Finset.prod_congr rfl fun l hl => ?_
      rw [Nat.factorization_def n (Nat.prime_of_mem_primeFactors hl)]
    rw [← Finset.mul_prod_erase _ _ h2m, ← Finset.mul_prod_erase _ _ hqm,
      ← Finset.mul_prod_erase _ _ hdm] at h1
    exact h1.symm
  have hR2 : ∀ l ∈ ((n.primeFactors.erase 2).erase q₁).erase d, 2 ≤ l ^ padicValNat l n := by
    intro l hl
    have hl' : l ∈ n.primeFactors :=
      Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hl))
    have hlp := Nat.prime_of_mem_primeFactors hl'
    exact hlp.two_le.trans (hge l hlp (Nat.dvd_of_mem_primeFactors hl'))
  obtain ⟨hTP, hP1⟩ := sum_le_prod_of_two_le _ (fun l => l ^ padicValNat l n) hR2
  have hq16 := hge q₁ hq hqn
  have hd16 := hge d hd hdn
  have hnat : (∑ l ∈ n.primeFactors, l ^ padicValNat l n) * (4 * min q₁ d) ≤ n := by
    rw [hsum]
    rcases le_total q₁ d with hle | hle
    · rw [min_eq_left hle]
      have key := one_sub_sum_mul_prod_le_prod q₁ _ _ _ _ _ hf2 hq16 (le_trans (by omega : 16 ≤ d) hd16)
        (hle.trans hd16) hTP hP1
      calc _ = 4 * q₁ * (2 ^ padicValNat 2 n + (q₁ ^ padicValNat q₁ n + (d ^ padicValNat d n +
            ∑ l ∈ ((n.primeFactors.erase 2).erase q₁).erase d, l ^ padicValNat l n))) := by ring
        _ ≤ _ := key
        _ = n := hprod.symm
    · rw [min_eq_right hle]
      have key := one_sub_sum_mul_prod_le_prod d (2 ^ padicValNat 2 n) (d ^ padicValNat d n) (q₁ ^ padicValNat q₁ n) _ _
        hf2 hd16 (le_trans (by omega : 16 ≤ q₁) hq16) (hle.trans hq16) hTP hP1
      calc _ = 4 * d * (2 ^ padicValNat 2 n + (d ^ padicValNat d n + (q₁ ^ padicValNat q₁ n +
            ∑ l ∈ ((n.primeFactors.erase 2).erase q₁).erase d, l ^ padicValNat l n))) := by ring
        _ ≤ _ := key
        _ = 2 ^ padicValNat 2 n * (q₁ ^ padicValNat q₁ n * (d ^ padicValNat d n *
            ∏ l ∈ ((n.primeFactors.erase 2).erase q₁).erase d, l ^ padicValNat l n)) := by ring
        _ = n := hprod.symm
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  have hmpos : (0 : ℝ) < 4 * ((min q₁ d : ℕ) : ℝ) :=
    mul_pos (by norm_num) (Nat.cast_pos.mpr (lt_min hq.pos hd.pos))
  rw [← Nat.cast_sum, div_le_div_iff₀ hnpos hmpos, one_mul]
  exact_mod_cast hnat

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
