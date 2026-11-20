import Formalism.LocalToGlobal.CharacterGerms.RowTiePAllSet

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace TypAr

variable {C : Type} [Field C] {V : VF C}

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using VF.Ge.one (V := V)`. Consider the case `succ k ih`. Rewrite using `[pow_succ]`. Use `ih.mul VF.ge_l` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ge_lpow (k : ℕ) : V.Ge (k : ℝ) ((V.l : C) ^ k) := by
  induction k with
  | zero => simpa using VF.Ge.one (V := V)
  | succ k ih =>
    rw [pow_succ]
    have := ih.mul VF.ge_l
    convert this using 1
    push_cast; ring

/- English proof (translation)
Take `⟨t, rfl⟩` from `h`. Rewrite using `[Nat.cast_mul, Nat.cast_pow]`. Simplify using `using (ge_lpow (V := V) k).mul (VF.ge_natCast t)`.
-/
theorem ge_of_lpow_dvd {k m : ℕ} (h : V.l ^ k ∣ m) : V.Ge (k : ℝ) (m : C) := by
  obtain ⟨t, rfl⟩ := h
  rw [Nat.cast_mul, Nat.cast_pow]
  simpa using (ge_lpow (V := V) k).mul (VF.ge_natCast t)

/- English proof (translation)
Introduce `K _ _` and use `h K`.
-/
theorem vlim_const {N : Type} {a : ℕ → C} {b : C} (h : ∀ K : ℝ, ∃ k0 : ℕ, ∀ k ≥ k0, V.Ge K (b - a k)) :
    VLim V (fun k (_ : ℕ) (_ : N) => a k) (fun _ _ => b) := fun K _ _ => h K

/- English proof (translation)
Take `⟨k0, hk0⟩` from `exists_nat_ge K`. Use `⟨k0, fun k hk => ?_⟩` and prove the remaining obligations. Establish `: (k0 : ℝ) ≤ k` using `by exact_mod_cast hk`. Use `push_cast`. Establish `: (0 : ℝ) ≤ c` using `Nat.cast_nonneg c`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem eventually_ge_nat (K : ℝ) (c : ℕ) : ∃ k0 : ℕ, ∀ k ≥ k0, K ≤ ((k + c : ℕ) : ℝ) := by
  obtain ⟨k0, hk0⟩ := exists_nat_ge K
  refine ⟨k0, fun k hk => ?_⟩
  have : (k0 : ℝ) ≤ k := by exact_mod_cast hk
  push_cast
  have : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  linarith

/- English proof (translation)
Establish `hl2` using `V.l_prime.two_le`. Establish `hconst : ∀ k : ℕ, (fun (_ : ℕ) (_ : N) => ((k + 1 : ℕ) : C)) ∈ M`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => convert h1 using 1`.

Use function extensionality and compare the values at `n x`. Simplify using the standard rewrite rules. Consider the case `succ k ih`. Use `hadd _ _ ih h1` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `n x`. Simplify using `only [Pi.add_apply, Pi.one_apply]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h0 : (0 : ℕ → N → C) ∈ M`.

Establish `hm : ∀ k, (fun (_ : ℕ) (_ : N) => ((V.l ^ k - 1 + 1 : ℕ) : C)) ∈ M` using `fun k => hconst _`. Establish `e : ∀ k, ((V.l ^ k - 1 + 1 : ℕ) : C) = (V.l : C) ^ k` using `fun k => by`. Rewrite using `[Nat.sub_add_cancel (Nat.one_le_pow _ _ V.l_prime.pos)]`. Use `push_cast`. Both sides reduce to the same expression.

Use `hlim (fun k (_ : ℕ) (_ : N) => ((V.l ^ k - 1 + 1 : ℕ) : C)) 0 hm ?_` and prove the remaining obligations. Introduce `K s x`. Take `⟨k0, hk0⟩` from `eventually_ge_nat K 0`. Use `⟨k0, fun k hk => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.zero_apply, zero_sub, e]`.

Conclude with `((ge_lpow k).neg).mono (by simpa using hk0 k hk)`. Establish `hneg : ∀ m, m ∈ M → -m ∈ M`. Introduce `m hm`. Establish `hc : ∀ k, (fun (_ : ℕ) (_ : N) => ((V.l ^ (k + 1) - 2 + 1 : ℕ) : C)) * m ∈ M` using `fun k => hmul _ _ (hconst _) hm`. Establish `e : ∀ k, ((V.l ^ (k + 1) - 2 + 1 : ℕ) : C) = (V.l : C) ^ (k + 1) - 1` using `fun k => by`.

Establish `h2 : 2 ≤ V.l ^ (k + 1)` using `le_trans hl2 (Nat.le_self_pow (Nat.succ_ne_zero k) _)`. Establish `: V.l ^ (k + 1) - 2 + 1 = V.l ^ (k + 1) - 1` using `by omega`. Rewrite using `[this, Nat.cast_sub (by omega), Nat.cast_pow, Nat.cast_one]`. Establish `hv : VLim V (fun k (_ : ℕ) (_ : N) => ((V.l ^ (k + 1) - 2 + 1 : ℕ) : C)) (fun _ _ => (-1 : C))`. Apply `vlim_const` to reduce the goal to its premises.

Introduce `K`. Take `⟨k0, hk0⟩` from `eventually_ge_nat K 1`. Use `⟨k0, fun k hk => ?_⟩` and prove the remaining obligations. Rewrite using `[e]`. Establish `: (-1 : C) - ((V.l : C) ^ (k + 1) - 1) = -((V.l : C) ^ (k + 1))` using `by ring`.

Rewrite using `[this]`. Conclude with `((ge_lpow (k + 1)).neg).mono (by simpa using hk0 k hk)`. Use `hlim _ _ hc (hv.mul_right m)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `n x`.

Simplify using the standard rewrite rules. Establish `hsum : ∀ {ι : Type} (s : Finset ι) (f : ι → ℕ → N → C), (∀ i ∈ s, f i ∈ M) → (∑ i ∈ s, f i) ∈ M`. Introduce `ι s f hf`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using h0`.

Consider the case `insert i s hi ih`. Rewrite using `[Finset.sum_insert hi]`. Conclude with `hadd _ _ (hf i (Finset.mem_insert_self i s)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))`. Establish `hprod : ∀ {ι : Type} (s : Finset ι) (f : ι → ℕ → N → C), (∀ i ∈ s, f i ∈ M) → (∏ i ∈ s, f i) ∈ M`. Introduce `ι s f hf`.

Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using h1`. Consider the case `insert i s hi ih`. Rewrite using `[Finset.prod_insert hi]`. Conclude with `hmul _ _ (hf i (Finset.mem_insert_self i s)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))`.

Establish `hpow : ∀ m, m ∈ M → ∀ e : ℕ, m ^ e ∈ M`. Introduce `m hm e`. Proceed by induction on `e with`. Consider the case `zero => simpa using h1`. Consider the case `succ e ih => rw [pow_succ]`.

Conclude with `hmul _ _ ih hm`. Establish `hD : ∀ p : ℕ, p.Prime → p ≠ V.l → (fun n (_ : N) => if p ∣ n then (1 : C) else 0) ∈ M`. Introduce `p hp hpl`. Take `⟨ζ, hζ⟩` from `hroot p hp hpl`. Establish `hζi : ∀ j : ℕ, V.Ge 0 (ζ ^ j)` using `fun j => VF.ge_of_pow_eq_one V hp.ne_zero (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow])`.

Use `set G : ℕ → N → C := ∑ j ∈ Finset.range p, fun n (_ : N) => (ζ ^ j) ^ n with hG`. Establish `hGM : G ∈ M` using `hsum _ _ fun j _ => hteich _ (hζi j)`. Establish `hGv : ∀ n x, G n x = if p ∣ n then (p : C) else 0`. Introduce `n x`. Rewrite using `[hG, Finset.sum_apply, Finset.sum_apply]`.

Establish `e : ∀ j ∈ Finset.range p, (ζ ^ j) ^ n = (ζ ^ n) ^ j` using `fun j _ => by`. Rewrite using `[← pow_mul, ← pow_mul, mul_comm]`. Rewrite using `[Finset.sum_congr rfl e]`. Distinguish the cases in `hn : p ∣ n`. Rewrite using `[if_pos hn]`.

Take `⟨t, rfl⟩` from `hn`. Rewrite using `[pow_mul, hζ.pow_eq_one, one_pow]`. Simplify using the standard rewrite rules. Rewrite using `[if_neg hn]`. Establish `hcop : n.Coprime p` using `(Nat.coprime_comm.trans (Nat.Prime.coprime_iff_not_dvd hp)).mpr hn`.

Conclude with `(hζ.pow_of_coprime n hcop).geom_sum_eq_zero hp.one_lt`. Use `hlim (fun k => G ^ Nat.totient (V.l ^ (k + 1))) _ (fun k => hpow _ hGM _) ?_` and prove the remaining obligations. Introduce `K n x`. Take `⟨k0, hk0⟩` from `eventually_ge_nat K 1`. Use `⟨k0, fun k hk => ?_⟩` and prove the remaining obligations.

Establish `hφ : 0 < Nat.totient (V.l ^ (k + 1))` using `Nat.totient_pos.mpr (pow_pos V.l_prime.pos _)`. Use `show V.Ge K ((if p ∣ n then (1 : C) else 0) - (G ^ Nat.totient (V.l ^ (k + 1))) n x)`. Rewrite using `[Pi.pow_apply, Pi.pow_apply, hGv]`. Distinguish the cases in `hn : p ∣ n`. Rewrite using `[if_pos hn, if_pos hn]`.

Establish `hcop : p.Coprime (V.l ^ (k + 1))` using `Nat.Coprime.pow_right _ ((Nat.coprime_primes hp V.l_prime).mpr hpl)`. Establish `hmod` using `Nat.ModEq.pow_totient hcop`. Establish `hdvd : V.l ^ (k + 1) ∣ p ^ Nat.totient (V.l ^ (k + 1)) - 1` using `(Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hp.pos)).mp hmod.symm`. Establish `hge` using `ge_of_lpow_dvd (V := V) hdvd`. Rewrite `hge` using `[Nat.cast_sub (Nat.one_le_pow _ _ hp.pos), Nat.cast_pow, Nat.cast_one]`.

Establish `: (1 : C) - (p : C) ^ Nat.totient (V.l ^ (k + 1)) = -((p : C) ^ Nat.totient (V.l ^ (k + 1)) - 1)` using `by ring`. Rewrite using `[this]`. Conclude with `hge.neg.mono (by simpa using hk0 k hk)`. Rewrite using `[if_neg hn, if_neg hn, zero_pow hφ.ne', sub_zero]`. Conclude with `VF.Ge.zero K`.

Use `set S : ℕ → Finset ℕ := fun P => (Finset.range (P + 1)).filter fun p => p.Prime ∧ p ≠ V.l with hS`. Use `set T : ℕ → ℕ → N → C := fun P => ∏ p ∈ S P, (1 + -(fun n (_ : N) => if p ∣ n then (1 : C) else 0)) with hT`. Establish `hTM : ∀ P, T P ∈ M` using `fun P => hprod _ _ fun p hp => by`. Establish `hp'` using `(Finset.mem_filter.mp hp).2`. Conclude with `hadd _ _ h1 (hneg _ (hD p hp'.1 hp'.2))`.

Use `hlim T _ hTM ?_` and prove the remaining obligations. Introduce `K n x`. Use `⟨n + 3, fun P hP => ?_⟩` and prove the remaining obligations. Use `show V.Ge K ((if ∃ s, V.l ^ s = n then (1 : C) else 0) - T P n x)`. Establish `hTv : T P n x = ∏ p ∈ S P, (1 - if p ∣ n then (1 : C) else 0)` using `by show (∏ p ∈ S P, (1 + -(fun n (_ : N) => if p ∣ n then (1 : C) else 0))) n x = _`.

Rewrite using `[Finset.prod_apply, Finset.prod_apply]`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `p _`. Simplify using `[sub_eq_add_neg]`. Rewrite using `[hTv]`.

Distinguish the cases in `hpow' : ∃ s, V.l ^ s = n`. Rewrite using `[if_pos hpow']`. Take `⟨s, rfl⟩` from `hpow'`. Establish `: ∏ p ∈ S P, (1 - if p ∣ V.l ^ s then (1 : C) else 0) = 1`. Apply `Finset.prod_eq_one` to reduce the goal to its premises.

Introduce `p hp`. Establish `hp'` using `(Finset.mem_filter.mp hp).2`. Establish `hnd : ¬ p ∣ V.l ^ s` using `fun h => hp'.2 ((Nat.prime_dvd_prime_iff_eq hp'.1 V.l_prime).mp (hp'.1.dvd_of_dvd_pow h))`. Rewrite using `[if_neg hnd, sub_zero]`. Rewrite using `[this, sub_self]`.

Conclude with `VF.Ge.zero K`. Rewrite using `[if_neg hpow']`. Establish `hex : ∃ p ∈ S P, p ∣ n`. Distinguish the cases in `hn0 : n = 0`. Substitute `hn0` using the available equality.

Distinguish the cases in `hl2' : V.l = 2`. Use `⟨3, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_three, by omega⟩, dvd_zero 3⟩` and prove the remaining obligations. Use `⟨2, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_two, fun h => hl2' h.symm⟩, dvd_zero 2⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne push_neg at hne`. Apply `hpow'` to reduce the goal to its premises.

Use `⟨n.primeFactorsList.length, (Nat.eq_prime_pow_of_unique_prime_dvd hn0 ?_).symm⟩` and prove the remaining obligations. Introduce `q hq hqn`. Assume the negation of the conclusion as `hql`. Establish `hqle : q ≤ n` using `Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hqn`. Conclude with `hne q (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hq, hql⟩) hqn`.

Take `⟨p, hpS, hpn⟩` from `hex`. Rewrite using `[Finset.prod_eq_zero hpS (by rw [if_pos hpn, sub_self]), sub_zero]`. Conclude with `VF.Ge.zero K`.
-/
theorem typ_gen {N : Type} (M : Set (ℕ → N → C))
    (hroot : ∀ p : ℕ, p.Prime → p ≠ V.l → ∃ ζ : C, IsPrimitiveRoot ζ p)
    (h1 : 1 ∈ M) (hadd : ∀ m m', m ∈ M → m' ∈ M → m + m' ∈ M) (hmul : ∀ m m', m ∈ M → m' ∈ M → m * m' ∈ M)
    (hteich : ∀ c : C, V.Ge 0 c → (fun n (_ : N) => c ^ n) ∈ M)
    (hlim : ∀ (m : ℕ → ℕ → N → C) (m' : ℕ → N → C), (∀ k, m k ∈ M) → VLim V m m' → m' ∈ M) :
    (fun n (_ : N) => if ∃ s, V.l ^ s = n then (1 : C) else 0) ∈ M := by
  have hl2 := V.l_prime.two_le

  have hconst : ∀ k : ℕ, (fun (_ : ℕ) (_ : N) => ((k + 1 : ℕ) : C)) ∈ M := by
    intro k
    induction k with
    | zero => convert h1 using 1; funext n x; simp
    | succ k ih =>
      have := hadd _ _ ih h1
      convert this using 1
      funext n x; simp only [Pi.add_apply, Pi.one_apply]; push_cast; ring

  have h0 : (0 : ℕ → N → C) ∈ M := by
    have hm : ∀ k, (fun (_ : ℕ) (_ : N) => ((V.l ^ k - 1 + 1 : ℕ) : C)) ∈ M := fun k => hconst _
    have e : ∀ k, ((V.l ^ k - 1 + 1 : ℕ) : C) = (V.l : C) ^ k := fun k => by
      rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ V.l_prime.pos)]; push_cast; rfl
    refine hlim (fun k (_ : ℕ) (_ : N) => ((V.l ^ k - 1 + 1 : ℕ) : C)) 0 hm ?_
    intro K s x
    obtain ⟨k0, hk0⟩ := eventually_ge_nat K 0
    refine ⟨k0, fun k hk => ?_⟩
    simp only [Pi.zero_apply, zero_sub, e]
    exact ((ge_lpow k).neg).mono (by simpa using hk0 k hk)

  have hneg : ∀ m, m ∈ M → -m ∈ M := by
    intro m hm
    have hc : ∀ k, (fun (_ : ℕ) (_ : N) => ((V.l ^ (k + 1) - 2 + 1 : ℕ) : C)) * m ∈ M :=
      fun k => hmul _ _ (hconst _) hm
    have e : ∀ k, ((V.l ^ (k + 1) - 2 + 1 : ℕ) : C) = (V.l : C) ^ (k + 1) - 1 := fun k => by
      have h2 : 2 ≤ V.l ^ (k + 1) := le_trans hl2 (Nat.le_self_pow (Nat.succ_ne_zero k) _)
      have : V.l ^ (k + 1) - 2 + 1 = V.l ^ (k + 1) - 1 := by omega
      rw [this, Nat.cast_sub (by omega), Nat.cast_pow, Nat.cast_one]
    have hv : VLim V (fun k (_ : ℕ) (_ : N) => ((V.l ^ (k + 1) - 2 + 1 : ℕ) : C)) (fun _ _ => (-1 : C)) := by
      apply vlim_const
      intro K
      obtain ⟨k0, hk0⟩ := eventually_ge_nat K 1
      refine ⟨k0, fun k hk => ?_⟩
      rw [e]
      have : (-1 : C) - ((V.l : C) ^ (k + 1) - 1) = -((V.l : C) ^ (k + 1)) := by ring
      rw [this]
      exact ((ge_lpow (k + 1)).neg).mono (by simpa using hk0 k hk)
    have := hlim _ _ hc (hv.mul_right m)
    convert this using 1
    funext n x; simp
  have hsum : ∀ {ι : Type} (s : Finset ι) (f : ι → ℕ → N → C), (∀ i ∈ s, f i ∈ M) → (∑ i ∈ s, f i) ∈ M := by
    intro ι s f hf
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact hadd _ _ (hf i (Finset.mem_insert_self i s)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
  have hprod : ∀ {ι : Type} (s : Finset ι) (f : ι → ℕ → N → C), (∀ i ∈ s, f i ∈ M) → (∏ i ∈ s, f i) ∈ M := by
    intro ι s f hf
    induction s using Finset.induction_on with
    | empty => simpa using h1
    | insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact hmul _ _ (hf i (Finset.mem_insert_self i s)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
  have hpow : ∀ m, m ∈ M → ∀ e : ℕ, m ^ e ∈ M := by
    intro m hm e
    induction e with
    | zero => simpa using h1
    | succ e ih => rw [pow_succ]; exact hmul _ _ ih hm

  have hD : ∀ p : ℕ, p.Prime → p ≠ V.l → (fun n (_ : N) => if p ∣ n then (1 : C) else 0) ∈ M := by
    intro p hp hpl
    obtain ⟨ζ, hζ⟩ := hroot p hp hpl
    have hζi : ∀ j : ℕ, V.Ge 0 (ζ ^ j) := fun j =>
      VF.ge_of_pow_eq_one V hp.ne_zero (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow])
    set G : ℕ → N → C := ∑ j ∈ Finset.range p, fun n (_ : N) => (ζ ^ j) ^ n with hG
    have hGM : G ∈ M := hsum _ _ fun j _ => hteich _ (hζi j)
    have hGv : ∀ n x, G n x = if p ∣ n then (p : C) else 0 := by
      intro n x
      rw [hG, Finset.sum_apply, Finset.sum_apply]
      have e : ∀ j ∈ Finset.range p, (ζ ^ j) ^ n = (ζ ^ n) ^ j := fun j _ => by
        rw [← pow_mul, ← pow_mul, mul_comm]
      rw [Finset.sum_congr rfl e]
      by_cases hn : p ∣ n
      · rw [if_pos hn]
        obtain ⟨t, rfl⟩ := hn
        rw [pow_mul, hζ.pow_eq_one, one_pow]
        simp
      · rw [if_neg hn]
        have hcop : n.Coprime p := (Nat.coprime_comm.trans (Nat.Prime.coprime_iff_not_dvd hp)).mpr hn
        exact (hζ.pow_of_coprime n hcop).geom_sum_eq_zero hp.one_lt
    refine hlim (fun k => G ^ Nat.totient (V.l ^ (k + 1))) _ (fun k => hpow _ hGM _) ?_
    intro K n x
    obtain ⟨k0, hk0⟩ := eventually_ge_nat K 1
    refine ⟨k0, fun k hk => ?_⟩
    have hφ : 0 < Nat.totient (V.l ^ (k + 1)) := Nat.totient_pos.mpr (pow_pos V.l_prime.pos _)
    show V.Ge K ((if p ∣ n then (1 : C) else 0) - (G ^ Nat.totient (V.l ^ (k + 1))) n x)
    rw [Pi.pow_apply, Pi.pow_apply, hGv]
    by_cases hn : p ∣ n
    · rw [if_pos hn, if_pos hn]
      have hcop : p.Coprime (V.l ^ (k + 1)) :=
        Nat.Coprime.pow_right _ ((Nat.coprime_primes hp V.l_prime).mpr hpl)
      have hmod := Nat.ModEq.pow_totient hcop
      have hdvd : V.l ^ (k + 1) ∣ p ^ Nat.totient (V.l ^ (k + 1)) - 1 :=
        (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hp.pos)).mp hmod.symm
      have hge := ge_of_lpow_dvd (V := V) hdvd
      rw [Nat.cast_sub (Nat.one_le_pow _ _ hp.pos), Nat.cast_pow, Nat.cast_one] at hge
      have : (1 : C) - (p : C) ^ Nat.totient (V.l ^ (k + 1)) = -((p : C) ^ Nat.totient (V.l ^ (k + 1)) - 1) := by ring
      rw [this]
      exact hge.neg.mono (by simpa using hk0 k hk)
    · rw [if_neg hn, if_neg hn, zero_pow hφ.ne', sub_zero]
      exact VF.Ge.zero K

  set S : ℕ → Finset ℕ := fun P => (Finset.range (P + 1)).filter fun p => p.Prime ∧ p ≠ V.l with hS
  set T : ℕ → ℕ → N → C := fun P => ∏ p ∈ S P, (1 + -(fun n (_ : N) => if p ∣ n then (1 : C) else 0)) with hT
  have hTM : ∀ P, T P ∈ M := fun P => hprod _ _ fun p hp => by
    have hp' := (Finset.mem_filter.mp hp).2
    exact hadd _ _ h1 (hneg _ (hD p hp'.1 hp'.2))
  refine hlim T _ hTM ?_
  intro K n x
  refine ⟨n + 3, fun P hP => ?_⟩
  show V.Ge K ((if ∃ s, V.l ^ s = n then (1 : C) else 0) - T P n x)
  have hTv : T P n x = ∏ p ∈ S P, (1 - if p ∣ n then (1 : C) else 0) := by
    show (∏ p ∈ S P, (1 + -(fun n (_ : N) => if p ∣ n then (1 : C) else 0))) n x = _
    rw [Finset.prod_apply, Finset.prod_apply]
    apply Finset.prod_congr rfl
    intro p _
    simp [sub_eq_add_neg]
  rw [hTv]
  by_cases hpow' : ∃ s, V.l ^ s = n
  · rw [if_pos hpow']
    obtain ⟨s, rfl⟩ := hpow'
    have : ∏ p ∈ S P, (1 - if p ∣ V.l ^ s then (1 : C) else 0) = 1 := by
      apply Finset.prod_eq_one
      intro p hp
      have hp' := (Finset.mem_filter.mp hp).2
      have hnd : ¬ p ∣ V.l ^ s := fun h => hp'.2 ((Nat.prime_dvd_prime_iff_eq hp'.1 V.l_prime).mp (hp'.1.dvd_of_dvd_pow h))
      rw [if_neg hnd, sub_zero]
    rw [this, sub_self]
    exact VF.Ge.zero K
  · rw [if_neg hpow']
    have hex : ∃ p ∈ S P, p ∣ n := by
      by_cases hn0 : n = 0
      · subst hn0
        by_cases hl2' : V.l = 2
        · refine ⟨3, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_three, by omega⟩, dvd_zero 3⟩
        · refine ⟨2, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_two, fun h => hl2' h.symm⟩, dvd_zero 2⟩
      · by_contra hne
        push_neg at hne
        apply hpow'
        refine ⟨n.primeFactorsList.length, (Nat.eq_prime_pow_of_unique_prime_dvd hn0 ?_).symm⟩
        intro q hq hqn
        by_contra hql
        have hqle : q ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hqn
        exact hne q (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hq, hql⟩) hqn
    obtain ⟨p, hpS, hpn⟩ := hex
    rw [Finset.prod_eq_zero hpS (by rw [if_pos hpn, sub_self]), sub_zero]
    exact VF.Ge.zero K

end TypAr

end Formalism.L2.FormalSeriesBounds
