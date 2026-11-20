import Mathlib
import Formalism.LocalRingCardinality.DataHost
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.NonemptyFieldAxiomsCyclicPow

noncomputable section

namespace UpperTheory.Host

open Formalism.BasicNotions Formalism.FrobeniusOrbits NumberField
open scoped Pointwise

/- English proof (translation)
Introduce `h`. Establish `hu : IsUnit (m : 𝓞 K)`. Rewrite using `[← Ideal.span_singleton_eq_top]`. Conclude with `top_le_iff.1 h`. Establish `hn : IsUnit (Algebra.norm ℤ (m : 𝓞 K))` using `hu.map _`.

Rewrite `hn` using `[show (m : 𝓞 K) = algebraMap ℤ (𝓞 K) (m : ℤ) by simp, Algebra.norm_algebraMap, Int.isUnit_iff]`. Establish `hr : 0 < Module.finrank ℤ (𝓞 K)` using `Module.finrank_pos`. Establish `h2 : (2 : ℤ) ^ Module.finrank ℤ (𝓞 K) ≤ (m : ℤ) ^ Module.finrank ℤ (𝓞 K)` using `pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hm) _`. Establish `h3 : (2 : ℤ) ≤ 2 ^ Module.finrank ℤ (𝓞 K)`. Combine the equalities or inequalities in the displayed calculation.

Apply the tactic sequence `rcases hn with h | h <;> omega`.
-/
theorem top_not_le_span {K : Type} [Field K] [NumberField K] (m : ℕ) (hm : 1 < m) :
    ¬ (⊤ : Ideal (𝓞 K)) ≤ Ideal.span {(m : 𝓞 K)} := by
  intro h
  have hu : IsUnit (m : 𝓞 K) := by
    rw [← Ideal.span_singleton_eq_top]; exact top_le_iff.1 h
  have hn : IsUnit (Algebra.norm ℤ (m : 𝓞 K)) := hu.map _
  rw [show (m : 𝓞 K) = algebraMap ℤ (𝓞 K) (m : ℤ) by simp, Algebra.norm_algebraMap,
    Int.isUnit_iff] at hn
  have hr : 0 < Module.finrank ℤ (𝓞 K) := Module.finrank_pos
  have h2 : (2 : ℤ) ^ Module.finrank ℤ (𝓞 K) ≤ (m : ℤ) ^ Module.finrank ℤ (𝓞 K) :=
    pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hm) _
  have h3 : (2 : ℤ) ≤ 2 ^ Module.finrank ℤ (𝓞 K) := by
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ Module.finrank ℤ (𝓞 K) := pow_le_pow_right₀ (by norm_num) hr
  rcases hn with h | h <;> omega

def withTop {R : Ranks} (H : Host R) : Host R :=
  { H with
    ccK := ⊤
    ccK_ne_bot := top_ne_bot
    ccK_primitive := fun m hm => top_not_le_span m hm
    ccK_split := fun _ hP hle => absurd (top_le_iff.1 hle) hP.ne_top
    ccK_coprime := fun p _ => by rw [Ideal.absNorm_top]; exact Nat.coprime_one_left p
    ccK_coprimeS := by rw [Ideal.absNorm_top]; exact Nat.coprime_one_left _ }

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem withTop_ccK {R : Ranks} (H : Host R) : (withTop H).ccK = ⊤ := rfl

/- English proof (translation)
Proceed by induction on `B with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [Finset.prod_range_succ]`. Conclude with `ih.mul ⟨n, rfl⟩`.
-/
private theorem oddProd_odd (B : ℕ) : Odd (∏ i ∈ Finset.range B, (2 * i + 1)) := by
  induction B with
  | zero => simp
  | succ n ih => rw [Finset.prod_range_succ]; exact ih.mul ⟨n, rfl⟩

/- English proof (translation)
Use `set P : ℕ := ∏ i ∈ Finset.range B, (2 * i + 1) with hP`. Establish `hodd : Odd P` using `oddProd_odd B`. Establish `hP0 : P ≠ 0` using `by rintro h; rw [h] at hodd; exact absurd hodd (by decide)`. Establish `hco : IsCoprime (8 * (P : ℤ) - 1) ((16 * P : ℕ) : ℤ)` using `⟨-(8 * (P : ℤ) + 1), 4 * P, by push_cast; ring⟩`. Take `⟨d, hdN, hdp, hd⟩` from `Nat.forall_exists_prime_gt_and_zmodEq N (q := 16 * P) (a := 8 * (P : ℤ) - 1) (by omega) hco`.

Take `⟨c, hc⟩` from `hd.symm.dvd`. Move the coercions through the operations in `at hc`. Take `⟨s, hs⟩` from `hodd`. Use `⟨d, hdN, hdp, ?_, fun p hp h2 hB => ?_⟩` and prove the remaining obligations. Establish `h1 : (d : ℤ) = 16 * (s + P * c) + 7`.

Establish `: (P : ℤ) = 2 * s + 1` using `by exact_mod_cast hs`. Take the linear combination `hc + 8 * this`. Use linear arithmetic over natural numbers and integers. Take `⟨i, hi⟩` from `hp.odd_of_ne_two h2`. Establish `hdv : p ∣ P`.

Rewrite using `[hi]; exact Finset.dvd_prod_of_mem _ (Finset.mem_range.2 (by omega))`. Take `⟨e, he⟩` from `hdv`. Establish `he' : (P : ℤ) = p * e` using `by exact_mod_cast he`. Establish `: (-(d : ℤ)) % p = 1 % p`. Establish `h3 : (-(d : ℤ)) = 1 + p * (-(8 * e) - 16 * e * c)`.

Take the linear combination `(-1 : ℤ) * hc + (-8 - 16 * c) * he'`. Rewrite using `[h3, Int.add_mul_emod_self_left]`. Rewrite using `[jacobiSym.mod_left' this, jacobiSym.one_left]`.
-/
private theorem exists_d (B N : ℕ) : ∃ d : ℕ, N < d ∧ d.Prime ∧ d % 16 = 7 ∧
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ≤ B → jacobiSym (-(d : ℤ)) p = 1 := by
  set P : ℕ := ∏ i ∈ Finset.range B, (2 * i + 1) with hP
  have hodd : Odd P := oddProd_odd B
  have hP0 : P ≠ 0 := by rintro h; rw [h] at hodd; exact absurd hodd (by decide)
  have hco : IsCoprime (8 * (P : ℤ) - 1) ((16 * P : ℕ) : ℤ) :=
    ⟨-(8 * (P : ℤ) + 1), 4 * P, by push_cast; ring⟩
  obtain ⟨d, hdN, hdp, hd⟩ := Nat.forall_exists_prime_gt_and_zmodEq N (q := 16 * P)
    (a := 8 * (P : ℤ) - 1) (by omega) hco
  obtain ⟨c, hc⟩ := hd.symm.dvd
  push_cast at hc
  obtain ⟨s, hs⟩ := hodd
  refine ⟨d, hdN, hdp, ?_, fun p hp h2 hB => ?_⟩
  · have h1 : (d : ℤ) = 16 * (s + P * c) + 7 := by
      have : (P : ℤ) = 2 * s + 1 := by exact_mod_cast hs
      linear_combination hc + 8 * this
    omega
  · obtain ⟨i, hi⟩ := hp.odd_of_ne_two h2
    have hdv : p ∣ P := by
      rw [hi]; exact Finset.dvd_prod_of_mem _ (Finset.mem_range.2 (by omega))
    obtain ⟨e, he⟩ := hdv
    have he' : (P : ℤ) = p * e := by exact_mod_cast he
    have : (-(d : ℤ)) % p = 1 % p := by
      have h3 : (-(d : ℤ)) = 1 + p * (-(8 * e) - 16 * e * c) := by
        linear_combination (-1 : ℤ) * hc + (-8 - 16 * c) * he'
      rw [h3, Int.add_mul_emod_self_left]
    rw [jacobiSym.mod_left' this, jacobiSym.one_left]

/- English proof (translation)
Take `⟨s, hs⟩ : ∃ s : ℕ, d = 16 * s + 7` from `⟨d / 16, by omega⟩`. Establish `hs' : (d : ℤ) = 16 * s + 7` using `by exact_mod_cast hs`. Establish `hco : IsCoprime (1 + 6 * (d : ℤ)) ((8 * d : ℕ) : ℤ)`. Use `push_cast`. Conclude with `IsCoprime.mul_right ⟨3, -(36 * s + 16), by rw [hs']; ring⟩ ⟨1, -6, by ring⟩`.

Take `⟨q, hqN, hqp, hq⟩` from `Nat.forall_exists_prime_gt_and_zmodEq N (q := 8 * d) (a := 1 + 6 * (d : ℤ)) (by omega) hco`. Take `⟨c, hc⟩` from `hq.symm.dvd`. Move the coercions through the operations in `at hc`. Establish `h8 : q % 8 = 3`. Establish `h1 : (q : ℤ) = 8 * (12 * s + 5 + d * c) + 3` using `by linear_combination hc + 6 * hs'`.

Use linear arithmetic over natural numbers and integers. Use `⟨q, hqN, hqp, h8, ?_⟩` and prove the remaining obligations. Establish `hq4 : q % 4 = 3` using `by omega`. Establish `hd4 : d % 4 = 3` using `by omega`. Establish `hqd : jacobiSym (q : ℤ) d = 1`.

Establish `: (q : ℤ) % d = 1 % d`. Establish `h3 : (q : ℤ) = 1 + d * (6 + 8 * c)` using `by linear_combination hc`. Rewrite using `[h3, Int.add_mul_emod_self_left]`. Rewrite using `[jacobiSym.mod_left' this, jacobiSym.one_left]`. Rewrite using `[jacobiSym.neg _ (Nat.odd_iff.2 (by omega)), ZMod.χ₄_nat_three_mod_four hq4, jacobiSym.quadratic_reciprocity_three_mod_four hd4 hq4, hqd]`.

Evaluate the numerical expressions.
-/
private theorem exists_q (d N : ℕ) (hd : d % 16 = 7) : ∃ q : ℕ, N < q ∧ q.Prime ∧ q % 8 = 3 ∧
    jacobiSym (-(d : ℤ)) q = 1 := by
  obtain ⟨s, hs⟩ : ∃ s : ℕ, d = 16 * s + 7 := ⟨d / 16, by omega⟩
  have hs' : (d : ℤ) = 16 * s + 7 := by exact_mod_cast hs
  have hco : IsCoprime (1 + 6 * (d : ℤ)) ((8 * d : ℕ) : ℤ) := by
    push_cast
    exact IsCoprime.mul_right ⟨3, -(36 * s + 16), by rw [hs']; ring⟩ ⟨1, -6, by ring⟩
  obtain ⟨q, hqN, hqp, hq⟩ := Nat.forall_exists_prime_gt_and_zmodEq N (q := 8 * d)
    (a := 1 + 6 * (d : ℤ)) (by omega) hco
  obtain ⟨c, hc⟩ := hq.symm.dvd
  push_cast at hc
  have h8 : q % 8 = 3 := by
    have h1 : (q : ℤ) = 8 * (12 * s + 5 + d * c) + 3 := by linear_combination hc + 6 * hs'
    omega
  refine ⟨q, hqN, hqp, h8, ?_⟩
  have hq4 : q % 4 = 3 := by omega
  have hd4 : d % 4 = 3 := by omega
  have hqd : jacobiSym (q : ℤ) d = 1 := by
    have : (q : ℤ) % d = 1 % d := by
      have h3 : (q : ℤ) = 1 + d * (6 + 8 * c) := by linear_combination hc
      rw [h3, Int.add_mul_emod_self_left]
    rw [jacobiSym.mod_left' this, jacobiSym.one_left]
  rw [jacobiSym.neg _ (Nat.odd_iff.2 (by omega)), ZMod.χ₄_nat_three_mod_four hq4,
    jacobiSym.quadratic_reciprocity_three_mod_four hd4 hq4, hqd]
  norm_num

/- English proof (translation)
Take `⟨d, hdN, hdp, hd16, hsp⟩` from `exists_d B (N + 4 * R.t * R.r + 3)`. Take `⟨q, hqN, hqp, hq8, hj⟩` from `exists_q d (N + 4 * R.t * R.r + 3) hd16`. Establish `hyp : HostHyp q d` using `⟨hqp, hdp, hq8, hd16, hj⟩`. Take `⟨H, rfl, rfl, hQS, h2G, h15, hMu, hPS, hEx, s, hs, hgs⟩` from `Formalism.HC.exists_hostAx R.toFrame hinj he hyp`. Establish `hcm : H.cmType.Nonempty`.

Apply `Set.nonempty_of_ncard_ne_zero` to reduce the goal to its premises. Rewrite using `[H.der.cmType.2.1]`. Use `R.ord_pos` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨𝔟, h1, h2, h3⟩` from `H.der.principal`.

Use `⟨{ toHostAx := H flPS := hPS sqq := s sqq_sq := hs gal_sqq := hgs QS_exact := hEx QS_le := by rw [hQS]; exact Formalism.HC.D7.qs_le R.toFrame hinj he o_pow := ho q_ne_three := by omega qd_big := ⟨by omega, by omega⟩ splitBound := B split_small := hsp small_le := fun l hl h2 hd => …` and prove the remaining obligations. Rewrite `hd` using `[hQS]`. Conclude with `absurd ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (hl.dvd_of_dvd_pow hd)) h2`. Use `φ₀ := hcm.some`. Use `φ₀_mem := hcm.some_mem`.

Use `𝔟 := 𝔟`. Use `𝔟_spec := ⟨h1, h2⟩`. Use `𝔟_stable := h3`. Use `levelPrimes := {31, 61, 67, 71}`. Use `g := ![67, 71]`.

Apply the tactic sequence `g_prime := by intro i; fin_cases i <;> norm_num`. Use `g_ne := by simp`. Apply the tactic sequence `g_level := by intro i; fin_cases i <;> simp`. Use `pde := 31`. Use the proof step `pde' := 61`.

Use `pde_prime := by norm_num`. Use the proof step `pde'_prime := by norm_num`. Use `pde_ne := by norm_num`. Use `pde_level := by simp`. Use `pde_mod := by norm_num`.

Apply the tactic sequence `pde_ne_g := by intro i; fin_cases i <;> simp`. Use `ccK := ⊤`. Use `ccK_ne_bot := top_ne_bot`. Use `ccK_primitive := fun m hm => top_not_le_span m hm`. Use `ccK_split := fun P hP hle => absurd (top_le_iff.1 hle) hP.ne_top`.

Use `ccK_coprime := fun p _ => by rw [Ideal.absNorm_top]; exact Nat.coprime_one_left p`. Use `ccK_coprimeS := by rw [Ideal.absNorm_top]; exact Nat.coprime_one_left _`. Use `level_coprimeS := fun p hp => by`. Rewrite using `[hQS]`. Apply `Nat.Coprime.pow_right` to reduce the goal to its premises.

Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at hp`. Apply the tactic sequence `rcases hp with rfl | rfl | rfl | rfl <;> norm_num`. Use `TT := TT`. Use `T2 := {0}`. Use `u0 := 0`.

Use `Lw := 2`. Use `two_le_Lw := le_refl _`. Use `second_set_range := by`. Introduce `s hs`. Simplify using `at hs`.

Substitute `hs` using the available equality. Simplify `addOrderOf_pos R.a0` using `[Formalism.HC.Frame.n0]`. Use `second_set_no_relation := by`. Introduce `s₁ h₁ s₂ h₂ _ _ h12`. Simplify using `at h₁ h₂`.

Conclude with `absurd (h₁.trans h₂.symm) h12`. Use `CT2 := 0 }, rfl, ?_, ?_, rfl, rfl, hQS⟩`. Use `show N < H.q`. Use linear arithmetic over natural numbers and integers. Use `show N < H.d`.

Use linear arithmetic over natural numbers and integers.
-/
theorem exists_host_of_injective (R : Ranks) (hinj : Function.Injective R.h) (ho : R.o ^ 64 ≤ 2 ^ R.e) (he : 2 ≤ R.e)
    (B N : ℕ) (TT : Finset R.A) :
    ∃ H : Host R, H.splitBound = B ∧ N < H.q ∧ N < H.d ∧ H.ccK = ⊤ ∧ H.TT = TT ∧ H.QS = 2 ^ (R.e + 2) := by
  obtain ⟨d, hdN, hdp, hd16, hsp⟩ := exists_d B (N + 4 * R.t * R.r + 3)
  obtain ⟨q, hqN, hqp, hq8, hj⟩ := exists_q d (N + 4 * R.t * R.r + 3) hd16
  have hyp : HostHyp q d := ⟨hqp, hdp, hq8, hd16, hj⟩
  obtain ⟨H, rfl, rfl, hQS, h2G, h15, hMu, hPS, hEx, s, hs, hgs⟩ := Formalism.HC.exists_hostAx R.toFrame hinj he hyp
  have hcm : H.cmType.Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    rw [H.der.cmType.2.1]
    have := R.ord_pos
    omega
  obtain ⟨𝔟, h1, h2, h3⟩ := H.der.principal
  refine ⟨{
    toHostAx := H
    flPS := hPS
    sqq := s
    sqq_sq := hs
    gal_sqq := hgs
    QS_exact := hEx
    QS_le := by rw [hQS]; exact Formalism.HC.D7.qs_le R.toFrame hinj he
    o_pow := ho
    q_ne_three := by omega
    qd_big := ⟨by omega, by omega⟩
    splitBound := B
    split_small := hsp
    small_le := fun l hl h2 hd => by
      rw [hQS] at hd
      exact absurd ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (hl.dvd_of_dvd_pow hd)) h2
    φ₀ := hcm.some
    φ₀_mem := hcm.some_mem
    𝔟 := 𝔟
    𝔟_spec := ⟨h1, h2⟩
    𝔟_stable := h3
    levelPrimes := {31, 61, 67, 71}
    g := ![67, 71]
    g_prime := by intro i; fin_cases i <;> norm_num
    g_ne := by simp
    g_level := by intro i; fin_cases i <;> simp
    pde := 31
    pde' := 61
    pde_prime := by norm_num
    pde'_prime := by norm_num
    pde_ne := by norm_num
    pde_level := by simp
    pde_mod := by norm_num
    pde_ne_g := by intro i; fin_cases i <;> simp
    ccK := ⊤
    ccK_ne_bot := top_ne_bot
    ccK_primitive := fun m hm => top_not_le_span m hm
    ccK_split := fun P hP hle => absurd (top_le_iff.1 hle) hP.ne_top
    ccK_coprime := fun p _ => by rw [Ideal.absNorm_top]; exact Nat.coprime_one_left p
    ccK_coprimeS := by rw [Ideal.absNorm_top]; exact Nat.coprime_one_left _
    level_coprimeS := fun p hp => by
      rw [hQS]
      apply Nat.Coprime.pow_right
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> norm_num
    TT := TT
    T2 := {0}
    u0 := 0
    Lw := 2
    two_le_Lw := le_refl _
    second_set_range := by
      intro s hs
      simp at hs
      subst hs
      simpa [Formalism.HC.Frame.n0] using addOrderOf_pos R.a0
    second_set_no_relation := by
      intro s₁ h₁ s₂ h₂ _ _ h12
      simp at h₁ h₂
      exact absurd (h₁.trans h₂.symm) h12
    CT2 := 0 }, rfl, ?_, ?_, rfl, rfl, hQS⟩
  · show N < H.q
    omega
  · show N < H.d
    omega

/- English proof (translation)
Establish `h : ∀ φ : Formalism.HC.Frame, ∀ e, φ = Formalism.HC.cyclicFrame e → Function.Injective φ.h ∧ φ.o = 1`. Introduce and unpack `_ e rfl`. Conclude with `⟨Formalism.HC.frameCyc_h_injective e 1, Formalism.HC.cyclicFrame_index e⟩`. Take `⟨h1, h2⟩` from `h _ _ hφ`. Conclude with `exists_host_of_injective R h1 (by rw [h2, one_pow]; exact Nat.one_le_two_pow) he B N TT`.
-/
theorem exists_host_over_cyclic_two_power (R : Ranks) (hφ : R.toFrame = Formalism.HC.cyclicFrame R.e) (he : 2 ≤ R.e)
    (B N : ℕ) (TT : Finset R.A) :
    ∃ H : Host R, H.splitBound = B ∧ N < H.q ∧ N < H.d ∧ H.ccK = ⊤ ∧ H.TT = TT ∧ H.QS = 2 ^ (R.e + 2) := by
  have h : ∀ φ : Formalism.HC.Frame, ∀ e, φ = Formalism.HC.cyclicFrame e → Function.Injective φ.h ∧ φ.o = 1 := by
    rintro _ e rfl
    exact ⟨Formalism.HC.frameCyc_h_injective e 1, Formalism.HC.cyclicFrame_index e⟩
  obtain ⟨h1, h2⟩ := h _ _ hφ
  exact exists_host_of_injective R h1 (by rw [h2, one_pow]; exact Nat.one_le_two_pow) he B N TT

/- English proof (translation)
The claim follows from `let ⟨H, _⟩ := exists_host_over_cyclic_two_power R hφ he 0 0 ∅ ⟨H⟩`.
-/
theorem nonempty_host_over_cyclic_two_power (R : Ranks) (hφ : R.toFrame = Formalism.HC.cyclicFrame R.e) (he : 2 ≤ R.e) : Nonempty (Host R) :=
  let ⟨H, _⟩ := exists_host_over_cyclic_two_power R hφ he 0 0 ∅
  ⟨H⟩

end UpperTheory.Host

end
