import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

/- English proof (translation)
Establish `hx1 : (1:ℝ) ≤ x` using `by linarith`. Establish `h1` using `one_add_mul_le_pow (show (-2:ℝ) ≤ x - 1 by linarith) K`. Rewrite `h1` using `[show (1:ℝ) + (x - 1) = x by ring]`. Establish `hKr : (k:ℝ) ≤ K` using `by exact_mod_cast hk`. Establish `hK0 : (0:ℝ) ≤ K` using `by positivity`.

Establish `hD0 : (0:ℝ) ≤ D` using `by positivity`. Establish `hC0 : (0:ℝ) ≤ C0` using `by positivity`. Establish `hc : (K:ℝ) + 1 ≤ x ^ K` using `by nlinarith`. Establish `ha : 1 ≤ x ^ C0` using `one_le_pow₀ hx1`. Establish `hb : 1 ≤ x ^ D` using `one_le_pow₀ hx1`.

Establish `he : 1 ≤ x ^ (K * D)` using `one_le_pow₀ hx1`. Establish `hpow : x ^ (C0 + D + K + K * D) = x ^ C0 * x ^ D * x ^ K * x ^ (K * D)`. Rewrite using `[pow_add, pow_add, pow_add]`. Establish `hM : (k:ℝ) * D ≤ ((C0 + D + K + K * D : ℕ) : ℝ)`. Use `push_cast`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hMB : (k:ℝ) * D * B ≤ ((C0 + D + K + K * D : ℕ) : ℝ) * B` using `mul_le_mul_of_nonneg_right hM hB`. Establish `hab : x ^ C0 ≤ x ^ C0 * x ^ D` using `le_mul_of_one_le_right (by positivity) hb`. Establish `habc : x ^ C0 * x ^ D * ((K:ℝ) + 1) ≤ x ^ C0 * x ^ D * x ^ K` using `mul_le_mul_of_nonneg_left hc (by positivity)`. Establish `hq : x ^ C0 * x ^ D * x ^ K ≤ x ^ C0 * x ^ D * x ^ K * x ^ (K * D)` using `le_mul_of_one_le_right (by positivity) he`.

Establish `hkb : (k:ℝ) * x ^ D ≤ K * x ^ D` using `mul_le_mul_of_nonneg_right hKr (by positivity)`. Establish `hKb : (K:ℝ) * x ^ D ≤ K * (x ^ C0 * x ^ D)` using `mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by positivity) ha) hK0`. Rewrite using `[hpow]`. Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem point_arith (x B : ℝ) (hx : 2 ≤ x) (hB : 0 ≤ B) (k K D C0 : ℕ) (hk : k ≤ K) :
    (k : ℝ) * (x ^ D + D * B) + x ^ C0 ≤ x ^ (C0 + D + K + K * D) + ((C0 + D + K + K * D : ℕ) : ℝ) * B := by
  have hx1 : (1:ℝ) ≤ x := by linarith
  have h1 := one_add_mul_le_pow (show (-2:ℝ) ≤ x - 1 by linarith) K
  rw [show (1:ℝ) + (x - 1) = x by ring] at h1
  have hKr : (k:ℝ) ≤ K := by exact_mod_cast hk
  have hK0 : (0:ℝ) ≤ K := by positivity
  have hD0 : (0:ℝ) ≤ D := by positivity
  have hC0 : (0:ℝ) ≤ C0 := by positivity
  have hc : (K:ℝ) + 1 ≤ x ^ K := by nlinarith
  have ha : 1 ≤ x ^ C0 := one_le_pow₀ hx1
  have hb : 1 ≤ x ^ D := one_le_pow₀ hx1
  have he : 1 ≤ x ^ (K * D) := one_le_pow₀ hx1
  have hpow : x ^ (C0 + D + K + K * D) = x ^ C0 * x ^ D * x ^ K * x ^ (K * D) := by
    rw [pow_add, pow_add, pow_add]
  have hM : (k:ℝ) * D ≤ ((C0 + D + K + K * D : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have hMB : (k:ℝ) * D * B ≤ ((C0 + D + K + K * D : ℕ) : ℝ) * B :=
    mul_le_mul_of_nonneg_right hM hB
  have hab : x ^ C0 ≤ x ^ C0 * x ^ D := le_mul_of_one_le_right (by positivity) hb
  have habc : x ^ C0 * x ^ D * ((K:ℝ) + 1) ≤ x ^ C0 * x ^ D * x ^ K :=
    mul_le_mul_of_nonneg_left hc (by positivity)
  have hq : x ^ C0 * x ^ D * x ^ K ≤ x ^ C0 * x ^ D * x ^ K * x ^ (K * D) :=
    le_mul_of_one_le_right (by positivity) he
  have hkb : (k:ℝ) * x ^ D ≤ K * x ^ D := mul_le_mul_of_nonneg_right hKr (by positivity)
  have hKb : (K:ℝ) * x ^ D ≤ K * (x ^ C0 * x ^ D) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by positivity) ha) hK0
  rw [hpow]
  nlinarith

/- English proof (translation)
Introduce `hin hout χ j`. Take `⟨C0, r₁, r₂, hr₁, hr₂, hO⟩` from `hout χ`. Take `⟨Cl, hCl⟩ : ∃ Cl : ℕ → ℕ, ∀ (l : Nat.Primes) (hl : (l:ℕ) ∈ Bchi χ), Cl l = Classical.choose (hin χ l (j l) hl)` from `⟨fun n => if hn : n.Prime ∧ n ∈ Bchi χ then Classical.choose (hin χ ⟨n, hn.1⟩ (j n) hn.2) else 0, fun l hl => dif_pos (show (l:ℕ).Prime ∧ (l:ℕ) ∈ Bchi χ from ⟨l.2, hl⟩)⟩`. Take `⟨D, hD⟩ : ∃ D : ℕ, ∀ l ∈ Bchi χ, Cl l ≤ D` from `⟨∑ l ∈ Bchi χ, Cl l, fun l hl => Finset.single_le_sum (fun _ _ => Nat.zero_le _) hl⟩`. Use `⟨C0 + D + (Bchi χ).card + (Bchi χ).card * D, r₁, r₂, hr₁, hr₂, ?_⟩` and prove the remaining obligations.

Introduce `h hχ h1 h2 h3 h4 t ht hbig B hB hlay E _ _ _ hE Ω _ _ _ ld`. Establish `hIn : ∀ l : Nat.Primes, (l:ℕ) ∈ Bchi χ → PlusLe ld {l} t (((h.N:ℝ) * t) ^ (Cl l) + (Cl l : ℝ) * B)`. Introduce `l hl`. Rewrite using `[hCl l hl]`. Conclude with `Classical.choose_spec (hin χ l (j l) hl) h hχ t ht hbig B hB (hlay l hl) E hE Ω ld`.

Establish `hOut : ∀ S : Finset Nat.Primes, (∀ l ∈ S, (l:ℕ) ≠ 2 ∧ (l:ℕ) ∉ Bchi χ) → PlusLe ld S t (((h.N:ℝ) * t) ^ C0)` using `fun S hS => hO h hχ h1 h2 h3 h4 t ht hbig E hE Ω ld S hS`. Establish `hx2 : (2:ℝ) ≤ (h.N:ℝ) * t`. Establish `hN : (1:ℝ) ≤ h.N` using `by exact_mod_cast h.N_pos`. Establish `ht' : (2:ℝ) ≤ t` using `by exact_mod_cast ht`. Use the polynomial consequences of the given equalities and inequalities.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `p hpf e hp2 he1 he2`. Distinguish the cases in `hb : p ∈ Bchi χ`. Conclude with `(hIn ⟨p, hpf.out⟩ hb).1 ⟨p, hpf.out⟩ (Finset.mem_singleton_self _) e he1 he2`. Use `(hOut {⟨p, hpf.out⟩} ?_).1 ⟨p, hpf.out⟩ (Finset.mem_singleton_self _) e he1 he2` and prove the remaining obligations.

Introduce `l hl`. Take `rfl` from `Finset.mem_singleton.mp hl`. Conclude with `⟨hp2, hb⟩`. Introduce `S hS2`. Rewrite using `[← Finset.sum_filter_add_sum_filter_not S (fun l : Nat.Primes => (l:ℕ) ∈ Bchi χ)]`.

Establish `hout2` using `(hOut (S.filter (fun l : Nat.Primes => (l:ℕ) ∉ Bchi χ)) (by`. Introduce `l hl`. Rewrite `hl` using `[Finset.mem_filter]`. Conclude with `⟨hS2 l hl.1, hl.2⟩)).2`. Establish `hin2 : ∑ l ∈ S.filter (fun l : Nat.Primes => (l:ℕ) ∈ Bchi χ), Real.log ((l:ℕ):ℝ) * ∑ e ∈ Finset.Ico 1 t, ((plusLen (ld l) e).toNat : ℝ) ≤ ∑ l ∈ S.filter (fun l : Nat.Primes => (l:ℕ) ∈ Bchi χ), (((h.N:ℝ) * t) ^ D + (D:ℝ) * B)`.

Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `l hl`. Rewrite `hl` using `[Finset.mem_filter]`. Establish `h0` using `(hIn l hl.2).2`. Rewrite `h0` using `[Finset.sum_singleton]`.

Establish `hle` using `hD l hl.2`. Establish `hp1 : ((h.N:ℝ) * t) ^ (Cl l) ≤ ((h.N:ℝ) * t) ^ D` using `pow_le_pow_right₀ (by linarith) hle`. Establish `hp2 : (Cl l : ℝ) * B ≤ (D:ℝ) * B` using `mul_le_mul_of_nonneg_right (by exact_mod_cast hle) hB`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `hin2` using `[Finset.sum_const, nsmul_eq_mul]`.

Establish `hcard : (S.filter (fun l : Nat.Primes => (l:ℕ) ∈ Bchi χ)).card ≤ (Bchi χ).card` using `Finset.card_le_card_of_injOn (fun l : Nat.Primes => (l:ℕ)) (fun l hl => (Finset.mem_filter.mp hl).2) Subtype.coe_injective.injOn`. Establish `key` using `point_arith ((h.N:ℝ) * t) B hx2 hB _ (Bchi χ).card D C0 hcard`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem UpperTheory.V.HV.point :
    SumIn → SumOut → PointHV := by
  intro hin hout χ j
  classical
  obtain ⟨C0, r₁, r₂, hr₁, hr₂, hO⟩ := hout χ
  obtain ⟨Cl, hCl⟩ : ∃ Cl : ℕ → ℕ, ∀ (l : Nat.Primes) (hl : (l:ℕ) ∈ Bchi χ),
      Cl l = Classical.choose (hin χ l (j l) hl) :=
    ⟨fun n => if hn : n.Prime ∧ n ∈ Bchi χ then Classical.choose (hin χ ⟨n, hn.1⟩ (j n) hn.2) else 0,
      fun l hl => dif_pos (show (l:ℕ).Prime ∧ (l:ℕ) ∈ Bchi χ from ⟨l.2, hl⟩)⟩
  obtain ⟨D, hD⟩ : ∃ D : ℕ, ∀ l ∈ Bchi χ, Cl l ≤ D :=
    ⟨∑ l ∈ Bchi χ, Cl l, fun l hl => Finset.single_le_sum (fun _ _ => Nat.zero_le _) hl⟩
  refine ⟨C0 + D + (Bchi χ).card + (Bchi χ).card * D, r₁, r₂, hr₁, hr₂, ?_⟩
  intro h hχ h1 h2 h3 h4 t ht hbig B hB hlay E _ _ _ hE Ω _ _ _ ld
  have hIn : ∀ l : Nat.Primes, (l:ℕ) ∈ Bchi χ →
      PlusLe ld {l} t (((h.N:ℝ) * t) ^ (Cl l) + (Cl l : ℝ) * B) := by
    intro l hl
    rw [hCl l hl]
    exact Classical.choose_spec (hin χ l (j l) hl) h hχ t ht hbig B hB (hlay l hl) E hE Ω ld
  have hOut : ∀ S : Finset Nat.Primes, (∀ l ∈ S, (l:ℕ) ≠ 2 ∧ (l:ℕ) ∉ Bchi χ) →
      PlusLe ld S t (((h.N:ℝ) * t) ^ C0) :=
    fun S hS => hO h hχ h1 h2 h3 h4 t ht hbig E hE Ω ld S hS
  have hx2 : (2:ℝ) ≤ (h.N:ℝ) * t := by
    have hN : (1:ℝ) ≤ h.N := by exact_mod_cast h.N_pos
    have ht' : (2:ℝ) ≤ t := by exact_mod_cast ht
    nlinarith
  refine ⟨?_, ?_⟩
  · intro p hpf e hp2 he1 he2
    by_cases hb : p ∈ Bchi χ
    · exact (hIn ⟨p, hpf.out⟩ hb).1 ⟨p, hpf.out⟩ (Finset.mem_singleton_self _) e he1 he2
    · refine (hOut {⟨p, hpf.out⟩} ?_).1 ⟨p, hpf.out⟩ (Finset.mem_singleton_self _) e he1 he2
      intro l hl
      obtain rfl := Finset.mem_singleton.mp hl
      exact ⟨hp2, hb⟩
  · intro S hS2
    rw [← Finset.sum_filter_add_sum_filter_not S (fun l : Nat.Primes => (l:ℕ) ∈ Bchi χ)]
    have hout2 := (hOut (S.filter (fun l : Nat.Primes => (l:ℕ) ∉ Bchi χ)) (by
      intro l hl
      rw [Finset.mem_filter] at hl
      exact ⟨hS2 l hl.1, hl.2⟩)).2
    have hin2 : ∑ l ∈ S.filter (fun l : Nat.Primes => (l:ℕ) ∈ Bchi χ),
        Real.log ((l:ℕ):ℝ) * ∑ e ∈ Finset.Ico 1 t, ((plusLen (ld l) e).toNat : ℝ)
        ≤ ∑ l ∈ S.filter (fun l : Nat.Primes => (l:ℕ) ∈ Bchi χ), (((h.N:ℝ) * t) ^ D + (D:ℝ) * B) := by
      apply Finset.sum_le_sum
      intro l hl
      rw [Finset.mem_filter] at hl
      have h0 := (hIn l hl.2).2
      rw [Finset.sum_singleton] at h0
      have hle := hD l hl.2
      have hp1 : ((h.N:ℝ) * t) ^ (Cl l) ≤ ((h.N:ℝ) * t) ^ D := pow_le_pow_right₀ (by linarith) hle
      have hp2 : (Cl l : ℝ) * B ≤ (D:ℝ) * B := mul_le_mul_of_nonneg_right (by exact_mod_cast hle) hB
      linarith
    rw [Finset.sum_const, nsmul_eq_mul] at hin2
    have hcard : (S.filter (fun l : Nat.Primes => (l:ℕ) ∈ Bchi χ)).card ≤ (Bchi χ).card :=
      Finset.card_le_card_of_injOn (fun l : Nat.Primes => (l:ℕ))
        (fun l hl => (Finset.mem_filter.mp hl).2) Subtype.coe_injective.injOn
    have key := point_arith ((h.N:ℝ) * t) B hx2 hB _ (Bchi χ).card D C0 hcard
    linarith
