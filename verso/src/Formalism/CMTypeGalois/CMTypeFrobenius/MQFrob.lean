import Formalism.CMTypeGalois.StatementField

open NumberField Ideal

noncomputable section

namespace Formalism.Q3

/- English proof (translation)
Rewrite using `[← Ideal.mem_span_singleton, Ideal.over_def P (span {(p : ℤ)}), Ideal.under_def, Ideal.mem_comap, eq_intCast]`.
-/
theorem mqFrob_intCast_mem_iff {E : Type} [Field E] [NumberField E] (p : ℕ)
    (P : Ideal (𝓞 E)) [P.LiesOver (span {(p : ℤ)})] (n : ℤ) :
    (n : 𝓞 E) ∈ P ↔ (p : ℤ) ∣ n := by
  rw [← Ideal.mem_span_singleton, Ideal.over_def P (span {(p : ℤ)}), Ideal.under_def,
    Ideal.mem_comap, eq_intCast]

/- English proof (translation)
Rewrite using `[← Ideal.over_def P (span {(p : ℤ)}), Int.card_ideal_quot]`.
-/
theorem mqFrob_card {E : Type} [Field E] [NumberField E] (p : ℕ)
    (P : Ideal (𝓞 E)) [P.LiesOver (span {(p : ℤ)})] :
    Nat.card (ℤ ⧸ P.under ℤ) = p := by
  rw [← Ideal.over_def P (span {(p : ℤ)}), Int.card_ideal_quot]

/- English proof (translation)
Introduce `k E _ _ a α hMQ ha p _ P hPp _ σ H i`. Establish `hp : p.Prime` using `Fact.out`. Establish `hmem` using `mqFrob_intCast_mem_iff p P`. Establish `hF : ∀ x : 𝓞 E, σ • x - x ^ p ∈ P`. Introduce `x`.

Use `H x` as an intermediate fact. Rewrite `this` using `[mqFrob_card p P]`. Conclude with `this`. Establish `hsq : α i ^ 2 = (a i : E)` using `hMQ.1 i`. Establish `hσ : σ (α i) = (((galSign α σ i : ℤˣ) : ℤ) : E) * α i` using `(hG k E a α hMQ ha).2.1 σ i`.

Establish `hint : IsIntegral ℤ (α i)`. Use `IsIntegral.of_pow (n := 2) (by norm_num) ?_` and prove the remaining obligations. Rewrite using `[hsq, ← eq_intCast (algebraMap ℤ E)]`. Conclude with `isIntegral_algebraMap`. Take `⟨A, hAcoe⟩ : ∃ A : 𝓞 E, (A : E) = α i` from `⟨⟨α i, hint⟩, rfl⟩`.

Establish `hA2 : A ^ 2 = (a i : 𝓞 E)`. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Simplify using `[hAcoe, hsq]`. Establish `hσA : σ • A = (((galSign α σ i : ℤˣ) : ℤ) : 𝓞 E) * A`. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises.

Use `show σ (A : E) = _`. Rewrite using `[hAcoe, hσ]`. Simplify using `[hAcoe]`. Establish `hAnot : ¬ (p : ℤ) ∣ a i → A ∉ P`. Introduce `hpa hA`.

Apply `hpa` to reduce the goal to its premises. Rewrite using `[← hmem, ← hA2]`. Conclude with `P.pow_mem_of_mem hA 2 (by norm_num)`. Use `⟨fun hnd => ?_, fun hp2 ha4 => ?_⟩` and prove the remaining obligations. Establish `hp2 : p ≠ 2`.

Introduce and unpack `rfl`. Conclude with `hnd (by push_cast; exact dvd_mul_right 2 _)`. Establish `hpa : ¬ (p : ℤ) ∣ a i` using `fun h => hnd (dvd_mul_of_dvd_right h 2)`. Establish `hodd : p % 2 = 1` using `Nat.odd_iff.mp (hp.odd_of_ne_two hp2)`. Establish `hpow : A ^ p = A * (a i : 𝓞 E) ^ (p / 2)`.

Rewrite using `[← hA2, ← pow_mul, ← pow_succ']`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Establish `hE : (p : ℤ) ∣ (a i) ^ (p / 2) - legendreSym p (a i)`. Rewrite using `[← ZMod.intCast_eq_intCast_iff_dvd_sub, legendreSym.eq_pow]`.

Use `push_cast`. Both sides reduce to the same expression. Establish `hE' : (a i : 𝓞 E) ^ (p / 2) - ((legendreSym p (a i) : ℤ) : 𝓞 E) ∈ P`. Use `(hmem _).mpr hE` as an intermediate fact. Move the coercions through the operations in `at this`.

Conclude with `this`. Establish `hprod : ((((galSign α σ i : ℤˣ) : ℤ) - legendreSym p (a i) : ℤ) : 𝓞 E) * A ∈ P`. Establish `heq : ((((galSign α σ i : ℤˣ) : ℤ) - legendreSym p (a i) : ℤ) : 𝓞 E) * A = (σ • A - A ^ p) + A * ((a i : 𝓞 E) ^ (p / 2) - ((legendreSym p (a i) : ℤ) : 𝓞 E))`. Rewrite using `[hσA, hpow]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[heq]`. Conclude with `P.add_mem (hF A) (P.mul_mem_left A hE')`. Rewrite using `[← jacobiSym.legendreSym.to_jacobiSym]`. Establish `hbad : ∀ n : ℤ, (n = 2 ∨ n = -2) → ¬ (p : ℤ) ∣ n`.

Introduce and unpack `n (rfl | rfl) h`. Use `Int.le_of_dvd (by norm_num) h` as an intermediate fact. Use `hp.two_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `Int.le_of_dvd (by norm_num) (dvd_neg.mpr h)` as an intermediate fact.

Use `hp.two_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Break down `(inferInstance : P.IsPrime).mem_or_mem hprod with h | h` into its components or cases. Rewrite `h` using `[hmem]`. Establish `hL` using `legendreSym.eq_one_or_neg_one p (a := a i) (by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpa)`.

Apply the tactic sequence `rcases Int.units_eq_one_or (galSign α σ i) with h1 | h1 <;>`. Apply the tactic sequence `simp only [h1, Units.val_one, Units.val_neg] at h ⊢ <;>`. Apply the tactic sequence `rcases hL with h2 | h2 <;> rw [h2] at h ⊢ <;>`. Apply the tactic sequence `first | rfl | exact absurd h (hbad _ (by norm_num))`. Conclude with `absurd h (hAnot hpa)`.

Substitute `hp2` using the available equality. Take `⟨c, hc⟩ : ∃ c : ℤ, a i = 4 * c + 1` from `⟨(a i - 1) / 4, by omega⟩`. Establish `hcE : (a i : E) = 4 * c + 1` using `by exact_mod_cast hc`. Take `⟨ω, hωdef⟩ : ∃ ω : E, ω = (1 + α i) / 2` from `⟨_, rfl⟩`. Establish `hω2 : ω ^ 2 = ω + (c : E)`.

Rewrite using `[hωdef]`. Take the linear combination `(1 / 4 : E) * hsq + (1 / 4 : E) * hcE`. Establish `hωint : IsIntegral ℤ ω`. Use `⟨Polynomial.X ^ 2 - (Polynomial.X + Polynomial.C c), ?_, ?_⟩` and prove the remaining obligations. Apply `Polynomial.monic_X_pow_sub` to reduce the goal to its premises.

Rewrite using `[Polynomial.degree_X_add_C]`. Evaluate the numerical expressions. Rewrite using `[Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, hω2]`. Simplify using the standard rewrite rules. Take `⟨W, hWcoe⟩ : ∃ W : 𝓞 E, (W : E) = ω` from `⟨⟨ω, hωint⟩, rfl⟩`.

Establish `hW2 : W ^ 2 = W + (c : 𝓞 E)`. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Simplify using `[hWcoe, hω2]`. Establish `h2P : (2 : 𝓞 E) ∈ P`. Use `(hmem 2).mpr (by norm_num)` as an intermediate fact.

Conclude with `this` after adjusting the coercions. Establish `hs : galSign α σ i = 1 ∨ galSign α σ i = -1`. Unfold `galSign`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hFW` using `hF W`.

Break down `hs with hs | hs` into its components or cases. Establish `hσW : σ • W = W`. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Use `show σ (W : E) = (W : E)`. Rewrite using `[hWcoe, hωdef, map_div₀, map_add, map_one, hσ, hs, map_ofNat]`.

Simplify using the standard rewrite rules. Rewrite `hFW` using `[hσW, hW2, show W - (W + (c : 𝓞 E)) = ((-c : ℤ) : 𝓞 E) by push_cast; ring, hmem]`. Move the coercions through the operations in `at hFW`. Simplify using `only [hs, true_iff]`. Use linear arithmetic over natural numbers and integers.

Establish `hσW : σ • W = 1 - W`. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Use `show σ (W : E) = ((1 - W : 𝓞 E) : E)`. Establish `hc1 : ((1 - W : 𝓞 E) : E) = 1 - (W : E)` using `by simp`. Rewrite using `[hc1]`.

Rewrite using `[hWcoe, hωdef, map_div₀, map_add, map_one, hσ, hs, map_ofNat]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hFW` using `[hσW, hW2, show 1 - W - (W + (c : 𝓞 E)) = ((1 - c : ℤ) : 𝓞 E) - 2 * W by push_cast; ring]`. Establish `h1c : ((1 - c : ℤ) : 𝓞 E) ∈ P`.

Use `P.add_mem hFW (P.mul_mem_right W h2P)` as an intermediate fact. Simplify using `using this`. Rewrite `h1c` using `[hmem]`. Move the coercions through the operations in `at h1c`. Rewrite using `[hs]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `congrArg (fun u : ℤˣ => (u : ℤ)) h` as an intermediate fact. Simplify using `at this`. Introduce `h`.

Use linear arithmetic over natural numbers and integers.
-/
theorem mqFrob_of (hG : MQGalois) : MQFrob := by
  intro k E _ _ a α hMQ ha p _ P hPp _ σ H i
  have hp : p.Prime := Fact.out
  have hmem := mqFrob_intCast_mem_iff p P
  have hF : ∀ x : 𝓞 E, σ • x - x ^ p ∈ P := by
    intro x
    have := H x
    rw [mqFrob_card p P] at this
    exact this
  have hsq : α i ^ 2 = (a i : E) := hMQ.1 i
  have hσ : σ (α i) = (((galSign α σ i : ℤˣ) : ℤ) : E) * α i := (hG k E a α hMQ ha).2.1 σ i
  have hint : IsIntegral ℤ (α i) := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [hsq, ← eq_intCast (algebraMap ℤ E)]
    exact isIntegral_algebraMap
  obtain ⟨A, hAcoe⟩ : ∃ A : 𝓞 E, (A : E) = α i := ⟨⟨α i, hint⟩, rfl⟩
  have hA2 : A ^ 2 = (a i : 𝓞 E) := by
    apply RingOfIntegers.coe_injective
    simp [hAcoe, hsq]
  have hσA : σ • A = (((galSign α σ i : ℤˣ) : ℤ) : 𝓞 E) * A := by
    apply RingOfIntegers.coe_injective
    show σ (A : E) = _
    rw [hAcoe, hσ]
    simp [hAcoe]
  have hAnot : ¬ (p : ℤ) ∣ a i → A ∉ P := by
    intro hpa hA
    apply hpa
    rw [← hmem, ← hA2]
    exact P.pow_mem_of_mem hA 2 (by norm_num)
  refine ⟨fun hnd => ?_, fun hp2 ha4 => ?_⟩
  ·
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact hnd (by push_cast; exact dvd_mul_right 2 _)
    have hpa : ¬ (p : ℤ) ∣ a i := fun h => hnd (dvd_mul_of_dvd_right h 2)
    have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
    have hpow : A ^ p = A * (a i : 𝓞 E) ^ (p / 2) := by
      rw [← hA2, ← pow_mul, ← pow_succ']
      congr 1
      omega
    have hE : (p : ℤ) ∣ (a i) ^ (p / 2) - legendreSym p (a i) := by
      rw [← ZMod.intCast_eq_intCast_iff_dvd_sub, legendreSym.eq_pow]
      push_cast
      rfl
    have hE' : (a i : 𝓞 E) ^ (p / 2) - ((legendreSym p (a i) : ℤ) : 𝓞 E) ∈ P := by
      have := (hmem _).mpr hE
      push_cast at this
      exact this
    have hprod : ((((galSign α σ i : ℤˣ) : ℤ) - legendreSym p (a i) : ℤ) : 𝓞 E) * A ∈ P := by
      have heq : ((((galSign α σ i : ℤˣ) : ℤ) - legendreSym p (a i) : ℤ) : 𝓞 E) * A =
          (σ • A - A ^ p) + A * ((a i : 𝓞 E) ^ (p / 2) - ((legendreSym p (a i) : ℤ) : 𝓞 E)) := by
        rw [hσA, hpow]
        push_cast
        ring
      rw [heq]
      exact P.add_mem (hF A) (P.mul_mem_left A hE')
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    have hbad : ∀ n : ℤ, (n = 2 ∨ n = -2) → ¬ (p : ℤ) ∣ n := by
      rintro n (rfl | rfl) h
      · have := Int.le_of_dvd (by norm_num) h
        have := hp.two_le
        omega
      · have := Int.le_of_dvd (by norm_num) (dvd_neg.mpr h)
        have := hp.two_le
        omega
    rcases (inferInstance : P.IsPrime).mem_or_mem hprod with h | h
    · rw [hmem] at h
      have hL := legendreSym.eq_one_or_neg_one p (a := a i)
        (by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpa)
      rcases Int.units_eq_one_or (galSign α σ i) with h1 | h1 <;>
        simp only [h1, Units.val_one, Units.val_neg] at h ⊢ <;>
        rcases hL with h2 | h2 <;> rw [h2] at h ⊢ <;>
        first | rfl | exact absurd h (hbad _ (by norm_num))
    · exact absurd h (hAnot hpa)
  ·
    subst hp2
    obtain ⟨c, hc⟩ : ∃ c : ℤ, a i = 4 * c + 1 := ⟨(a i - 1) / 4, by omega⟩
    have hcE : (a i : E) = 4 * c + 1 := by exact_mod_cast hc
    obtain ⟨ω, hωdef⟩ : ∃ ω : E, ω = (1 + α i) / 2 := ⟨_, rfl⟩
    have hω2 : ω ^ 2 = ω + (c : E) := by
      rw [hωdef]
      linear_combination (1 / 4 : E) * hsq + (1 / 4 : E) * hcE
    have hωint : IsIntegral ℤ ω := by
      refine ⟨Polynomial.X ^ 2 - (Polynomial.X + Polynomial.C c), ?_, ?_⟩
      · apply Polynomial.monic_X_pow_sub
        rw [Polynomial.degree_X_add_C]
        norm_num
      · rw [Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C,
          Polynomial.eval₂_X_pow, hω2]
        simp
    obtain ⟨W, hWcoe⟩ : ∃ W : 𝓞 E, (W : E) = ω := ⟨⟨ω, hωint⟩, rfl⟩
    have hW2 : W ^ 2 = W + (c : 𝓞 E) := by
      apply RingOfIntegers.coe_injective
      simp [hWcoe, hω2]
    have h2P : (2 : 𝓞 E) ∈ P := by
      have := (hmem 2).mpr (by norm_num)
      exact_mod_cast this
    have hs : galSign α σ i = 1 ∨ galSign α σ i = -1 := by
      unfold galSign
      split_ifs <;> simp
    have hFW := hF W
    rcases hs with hs | hs
    · have hσW : σ • W = W := by
        apply RingOfIntegers.coe_injective
        show σ (W : E) = (W : E)
        rw [hWcoe, hωdef, map_div₀, map_add, map_one, hσ, hs, map_ofNat]
        simp
      rw [hσW, hW2, show W - (W + (c : 𝓞 E)) = ((-c : ℤ) : 𝓞 E) by push_cast; ring, hmem] at hFW
      push_cast at hFW
      simp only [hs, true_iff]
      omega
    · have hσW : σ • W = 1 - W := by
        apply RingOfIntegers.coe_injective
        show σ (W : E) = ((1 - W : 𝓞 E) : E)
        have hc1 : ((1 - W : 𝓞 E) : E) = 1 - (W : E) := by simp
        rw [hc1]
        rw [hWcoe, hωdef, map_div₀, map_add, map_one, hσ, hs, map_ofNat]
        push_cast
        ring
      rw [hσW, hW2, show 1 - W - (W + (c : 𝓞 E)) = ((1 - c : ℤ) : 𝓞 E) - 2 * W by push_cast; ring]
        at hFW
      have h1c : ((1 - c : ℤ) : 𝓞 E) ∈ P := by
        have := P.add_mem hFW (P.mul_mem_right W h2P)
        simpa using this
      rw [hmem] at h1c
      push_cast at h1c
      rw [hs]
      constructor
      · intro h
        have := congrArg (fun u : ℤˣ => (u : ℤ)) h
        simp at this
      · intro h
        omega

end Formalism.Q3
