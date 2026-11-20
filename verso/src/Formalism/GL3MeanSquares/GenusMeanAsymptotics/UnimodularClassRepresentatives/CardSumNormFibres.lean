import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassSt

open NumberField Module Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.FiniteNormFibres

/- English proof (translation)
Proceed by induction on `M with`. Consider the case `zero`. Introduce `c _`. Distinguish the cases in `h0 : c = 0`. Substitute `h0` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[h0, Ne.symm h0]`. Consider the case `succ M ih`. Introduce `c hc`. Establish `hsplit : ((univ.filter (fun x : Fin (M + 1) → X => ∑ i, N (x i) = c)).card : ℤ) = ∑ y : X, ((univ.filter (fun x : Fin M → X => ∑ i, N (x i) = c - N y)).card : ℤ)`.

Rewrite using `[← Nat.cast_sum]`. Use `congr 1`. Simplify using `only [Finset.card_filter]`. Rewrite using `[← (Fin.consEquiv (fun _ : Fin (M + 1) => X)).sum_comp, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations.

Simplify using `only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, eq_sub_iff_add_eq']`. Establish `hcount : ∑ y : X, (if c - N y = 0 then (1 : ℤ) else 0) = ((univ.filter fun y => N y = c).card : ℤ)`. Rewrite using `[Finset.card_filter]`. Use `push_cast`. Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations.

Simplify using `[sub_eq_zero, eq_comm]`. Rewrite using `[hsplit, Finset.mul_sum, Finset.sum_congr rfl fun y _ => ih (c - N y) (hS c y hc)]`. Simplify using `only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Rewrite using `[hcount, hN c hc, hX]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem card_sum_norm_fibres {k X : Type*} [AddCommGroup k] [DecidableEq k] [Fintype X]
    (N : X → k) (S : k → Prop) (hS : ∀ c y, S c → S (c - N y)) (q ε : ℤ)
    (hX : (Fintype.card X : ℤ) = q ^ 2)
    (hN : ∀ c, S c → ((univ.filter (fun y => N y = c)).card : ℤ) =
      (q - ε) + ε * q * (if c = 0 then 1 else 0)) (M : ℕ) :
    ∀ c, S c → q * ((univ.filter (fun x : Fin M → X => ∑ i, N (x i) = c)).card : ℤ) =
      q ^ (2 * M) + (ε * q) ^ M * (q * (if c = 0 then 1 else 0) - 1) := by
  induction M with
  | zero =>
    intro c _
    by_cases h0 : c = 0
    · subst h0
      simp
    · simp [h0, Ne.symm h0]
  | succ M ih =>
    intro c hc
    have hsplit : ((univ.filter (fun x : Fin (M + 1) → X => ∑ i, N (x i) = c)).card : ℤ) =
        ∑ y : X, ((univ.filter (fun x : Fin M → X => ∑ i, N (x i) = c - N y)).card : ℤ) := by
      rw [← Nat.cast_sum]
      congr 1
      simp only [Finset.card_filter]
      rw [← (Fin.consEquiv (fun _ : Fin (M + 1) => X)).sum_comp, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
        eq_sub_iff_add_eq']
    have hcount : ∑ y : X, (if c - N y = 0 then (1 : ℤ) else 0) =
        ((univ.filter fun y => N y = c).card : ℤ) := by
      rw [Finset.card_filter]
      push_cast
      refine Finset.sum_congr rfl fun y _ => ?_
      simp [sub_eq_zero, eq_comm]
    rw [hsplit, Finset.mul_sum, Finset.sum_congr rfl fun y _ => ih (c - N y) (hS c y hc)]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    rw [hcount, hN c hc, hX]
    ring

/- English proof (translation)
Take `⟨p, hchar⟩` from `CharP.exists k`. Take `⟨n, hp, hcard⟩` from `FiniteField.card k p`. Use `haveI := Fact.mk hp`. Use `haveI : NeZero p := ⟨hp.ne_zero⟩`. Use `letI : Algebra (ZMod p) k := ZMod.algebra k p`.

Establish `hpow : ∀ i : ℕ, ∀ x : k, ((FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) k) ^ i) x = x ^ (p ^ i)`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => intro x`. Simplify using the standard rewrite rules.

Consider the case `succ i ih`. Introduce `x`. Rewrite using `[pow_succ, AlgEquiv.mul_apply, ih]`. Simplify using `only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ZMod.card]`. Rewrite using `[← pow_mul, ← pow_succ']`.

Set `σ' : k ≃ₐ[ZMod p] k` to `AlgEquiv.ofRingEquiv (f := σ) (fun c => DFunLike.congr_fun (RingHom.ext_zmod (σ.toRingHom.comp (algebraMap (ZMod p) k)) (algebraMap (ZMod p) k)) c)`. Take `⟨j, hj⟩` from `(FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) k).2 σ'`. Establish `hj' : (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) k) ^ (j : ℕ) = σ'` using `hj`. Establish `hσj : ∀ x, σ x = x ^ (p ^ (j : ℕ))` using `fun x => by rw [← hpow, hj']; rfl`. Establish `hN : Fintype.card k = p ^ Module.finrank (ZMod p) k`.

Rewrite using `[Module.card_eq_pow_finrank (K := ZMod p) (V := k), ZMod.card]`. Establish `hfrN : (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) k) ^ Module.finrank (ZMod p) k = 1` using `AlgEquiv.ext fun x => by rw [hpow, AlgEquiv.one_apply, ← hN, FiniteField.pow_card]`. Establish `hσ2 : σ' ^ 2 = 1` using `AlgEquiv.ext fun x => by`. Rewrite using `[pow_two, AlgEquiv.mul_apply]`. Conclude with `hσ x`.

Rewrite `hσ2` using `[← hj', ← pow_mul]`. Establish `hN0 : 0 < Module.finrank (ZMod p) k` using `Fin.pos j`. Establish `hr : (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) k) ^ ((j : ℕ) * 2 % Module.finrank (ZMod p) k) = 1`. Establish `h1` using `Nat.mod_add_div ((j : ℕ) * 2) (Module.finrank (ZMod p) k)`. Rewrite `hσ2` using `[← h1, pow_add, pow_mul, hfrN, one_pow, mul_one]`.

Conclude with `hσ2`. Establish `hr0 : (j : ℕ) * 2 % Module.finrank (ZMod p) k = 0`. Establish `h1` using `(FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) k).1 (a₁ := ⟨(j : ℕ) * 2 % Module.finrank (ZMod p) k, Nat.mod_lt _ hN0⟩) (a₂ := ⟨0, hN0⟩) (by simp only [pow_zero]; exact hr)`. Conclude with `congrArg Fin.val h1`. Establish `hj0 : (j : ℕ) ≠ 0`.

Introduce `h0`. Take `⟨x, hx⟩` from `hne`. Apply `hx` to reduce the goal to its premises. Rewrite using `[hσj, h0, pow_zero, pow_one]`. Establish `hjlt` using `j.isLt`.

Establish `ht` using `Nat.mod_add_div ((j : ℕ) * 2) (Module.finrank (ZMod p) k)`. Rewrite `ht` using `[hr0, zero_add]`. Take `⟨t, ht2⟩ : ∃ t, Module.finrank (ZMod p) k * t = (j : ℕ) * 2` from `⟨_, ht⟩`. Establish `h2j : (j : ℕ) * 2 = Module.finrank (ZMod p) k`. Break down `t with _ | _ | t` into its components or cases.

Simplify using `at ht2`. Use linear arithmetic over natural numbers and integers. Simplify using `at ht2`. Use linear arithmetic over natural numbers and integers. It suffices to derive a contradiction.

Use the polynomial consequences of the given equalities and inequalities. Establish `hqj : q = p ^ (j : ℕ)`. Establish `h1 : q ^ 2 = (p ^ (j : ℕ)) ^ 2` using `by rw [← hq, hN, ← pow_mul, h2j]`. Conclude with `Nat.pow_left_injective two_ne_zero h1`. Introduce `x`.

Rewrite using `[hσj, hqj]`.
-/
theorem sigma_eq_pow {k : Type*} [Field k] [Fintype k] (σ : k ≃+* k)
    (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x) (q : ℕ) (hq : Fintype.card k = q ^ 2) :
    ∀ x, σ x = x ^ q := by
  classical
  obtain ⟨p, hchar⟩ := CharP.exists k
  obtain ⟨n, hp, hcard⟩ := FiniteField.card k p
  haveI := Fact.mk hp
  haveI : NeZero p := ⟨hp.ne_zero⟩
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  have hpow : ∀ i : ℕ, ∀ x : k,
      ((FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) k) ^ i) x = x ^ (p ^ i) := by
    intro i
    induction i with
    | zero => intro x; simp
    | succ i ih =>
      intro x
      rw [pow_succ, AlgEquiv.mul_apply, ih]
      simp only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ZMod.card]
      rw [← pow_mul, ← pow_succ']
  let σ' : k ≃ₐ[ZMod p] k := AlgEquiv.ofRingEquiv (f := σ) (fun c =>
    DFunLike.congr_fun (RingHom.ext_zmod (σ.toRingHom.comp (algebraMap (ZMod p) k))
      (algebraMap (ZMod p) k)) c)
  obtain ⟨j, hj⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) k).2 σ'
  have hj' : (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) k) ^ (j : ℕ) = σ' := hj
  have hσj : ∀ x, σ x = x ^ (p ^ (j : ℕ)) := fun x => by rw [← hpow, hj']; rfl
  have hN : Fintype.card k = p ^ Module.finrank (ZMod p) k := by
    rw [Module.card_eq_pow_finrank (K := ZMod p) (V := k), ZMod.card]
  have hfrN : (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) k) ^ Module.finrank (ZMod p) k = 1 :=
    AlgEquiv.ext fun x => by rw [hpow, AlgEquiv.one_apply, ← hN, FiniteField.pow_card]
  have hσ2 : σ' ^ 2 = 1 := AlgEquiv.ext fun x => by
    rw [pow_two, AlgEquiv.mul_apply]
    exact hσ x
  rw [← hj', ← pow_mul] at hσ2
  have hN0 : 0 < Module.finrank (ZMod p) k := Fin.pos j
  have hr : (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) k) ^
      ((j : ℕ) * 2 % Module.finrank (ZMod p) k) = 1 := by
    have h1 := Nat.mod_add_div ((j : ℕ) * 2) (Module.finrank (ZMod p) k)
    rw [← h1, pow_add, pow_mul, hfrN, one_pow, mul_one] at hσ2
    exact hσ2
  have hr0 : (j : ℕ) * 2 % Module.finrank (ZMod p) k = 0 := by
    have h1 := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) k).1
      (a₁ := ⟨(j : ℕ) * 2 % Module.finrank (ZMod p) k, Nat.mod_lt _ hN0⟩) (a₂ := ⟨0, hN0⟩)
      (by simp only [pow_zero]; exact hr)
    exact congrArg Fin.val h1
  have hj0 : (j : ℕ) ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ := hne
    apply hx
    rw [hσj, h0, pow_zero, pow_one]
  have hjlt := j.isLt
  have ht := Nat.mod_add_div ((j : ℕ) * 2) (Module.finrank (ZMod p) k)
  rw [hr0, zero_add] at ht
  obtain ⟨t, ht2⟩ : ∃ t, Module.finrank (ZMod p) k * t = (j : ℕ) * 2 := ⟨_, ht⟩
  have h2j : (j : ℕ) * 2 = Module.finrank (ZMod p) k := by
    rcases t with _ | _ | t
    · simp at ht2
      omega
    · simp at ht2
      omega
    · exfalso
      nlinarith
  have hqj : q = p ^ (j : ℕ) := by
    have h1 : q ^ 2 = (p ^ (j : ℕ)) ^ 2 := by rw [← hq, hN, ← pow_mul, h2j]
    exact Nat.pow_left_injective two_ne_zero h1
  intro x
  rw [hσj, hqj]

/- English proof (translation)
Establish `hpow` using `sigma_eq_pow σ hσ hne q hq`. Establish `hne0 : ∀ y : k, y ≠ 0 → σ y ≠ 0` using `fun y hy h => hy (σ.injective (by rw [h, map_zero]))`. Establish `hq2 : 2 ≤ q`. Establish `h1 : 1 < Fintype.card k` using `Fintype.one_lt_card`. Rewrite `h1` using `[hq]`.

Assume the negation of the conclusion as `h2`. Establish `: q ≤ 1` using `by omega`. Establish `: q ^ 2 ≤ 1` using `by nlinarith`. Use linear arithmetic over natural numbers and integers. Distinguish the cases in `hc0 : c = 0`.

Substitute `hc0` using the available equality. Establish `: univ.filter (fun y : k => σ y * y = 0) = {0}`. Use extensionality with `y`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Assume the negation of the conclusion as `hy`. Conclude with `mul_ne_zero (hne0 y hy) hy h`. Introduce `h`. Rewrite using `[h, map_zero, zero_mul]`.

Rewrite using `[this, Finset.card_singleton, if_pos rfl]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hc0]`. Use `set Fs := univ.filter (fun b : k => σ b = b ∧ b ≠ 0) with hFs`.

Use `set G : k → Finset k := fun b => univ.filter (fun y : k => σ y * y = b) with hG`. Establish `hGle : ∀ b, (G b).card ≤ q + 1`. Introduce `b`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.card_le_card` to reduce the goal to its premises.

Introduce `y hy`. Simplify using `only [hG, Finset.mem_filter, Finset.mem_univ, true_and] at hy`. Rewrite using `[Multiset.mem_toFinset, Polynomial.mem_nthRoots (by omega), pow_succ, ← hpow y, hy]`. Use `_ ≤ (Polynomial.nthRoots (q + 1) b).card := Multiset.toFinset_card_le _`. Use `_ ≤ q + 1 := Polynomial.card_nthRoots _ _`.

Establish `hFle : Fs.card ≤ q - 1`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.card_le_card` to reduce the goal to its premises. Introduce `b hb`. Simplify using `only [hFs, Finset.mem_filter, Finset.mem_univ, true_and] at hb`.

Rewrite using `[Multiset.mem_toFinset, Polynomial.mem_nthRoots (by omega)]`. Establish `h1 : b ^ (q - 1) * b = b`. Rewrite using `[← pow_succ, show q - 1 + 1 = q by omega, ← hpow b, hb.1]`. Establish `h2 : b ^ (q - 1) * b = 1 * b` using `by rw [h1, one_mul]`. Conclude with `mul_right_cancel₀ hb.2 h2`.

Use `_ ≤ (Polynomial.nthRoots (q - 1) (1 : k)).card := Multiset.toFinset_card_le _`. Use `_ ≤ q - 1 := Polynomial.card_nthRoots _ _`. Establish `hsum : ∑ b ∈ Fs, (G b).card = q ^ 2 - 1`. Establish `hmaps : ∀ y ∈ univ.filter (fun y : k => y ≠ 0), σ y * y ∈ Fs`. Introduce `y hy`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hy`. Simplify using `only [hFs, Finset.mem_filter, Finset.mem_univ, true_and]`. Use `⟨by rw [map_mul, hσ, mul_comm], mul_ne_zero (hne0 y hy) hy⟩` and prove the remaining obligations. Establish `h1` using `Finset.card_eq_sum_card_fiberwise hmaps`. Establish `h2 : (univ.filter (fun y : k => y ≠ 0)).card = q ^ 2 - 1`.

Rewrite using `[Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hq]`. Rewrite using `[← h2, h1]`. Use `Finset.sum_congr rfl fun b hb => ?_` and prove the remaining obligations. Simplify using `only [hFs, Finset.mem_filter, Finset.mem_univ, true_and] at hb`. Use `congr 1`.

Use extensionality with `y`. Simplify using `only [hG, Finset.mem_filter, Finset.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨fun hy => hb.2 ?_, h⟩` and prove the remaining obligations.

Rewrite using `[← h, hy, mul_zero]`. Conclude with `fun h => h.2`. Establish `hcF : c ∈ Fs`. Simplify using `only [hFs, Finset.mem_filter, Finset.mem_univ, true_and]`. Conclude with `⟨hc, hc0⟩`.

Establish `hGc : (G c).card = q + 1`. Assume the negation of the conclusion as `hlt`. Establish `hlt' : (G c).card < q + 1` using `lt_of_le_of_ne (hGle c) hlt`. Establish `h1 : ∑ b ∈ Fs, (G b).card < ∑ b ∈ Fs, (q + 1)` using `Finset.sum_lt_sum (fun b _ => hGle b) ⟨c, hcF, hlt'⟩`. Rewrite `h1` using `[Finset.sum_const, smul_eq_mul, hsum]`.

Establish `h2 : Fs.card * (q + 1) ≤ (q - 1) * (q + 1)` using `Nat.mul_le_mul_right _ hFle`. Establish `h3 : (q - 1) * (q + 1) = q ^ 2 - 1`. Take `⟨r, rfl⟩ : ∃ r, q = r + 1` from `⟨q - 1, by omega⟩`. Simplify using `only [Nat.add_sub_cancel]`. Put the polynomial expressions in normal form.

Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Establish `: (univ.filter (fun y : k => σ y * y = c)).card = q + 1` using `hGc`. Rewrite using `[this]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem card_norm_fibre {k : Type*} [Field k] [Fintype k] [DecidableEq k] (σ : k ≃+* k)
    (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x) (q : ℕ) (hq : Fintype.card k = q ^ 2)
    (c : k) (hc : σ c = c) :
    ((univ.filter (fun y : k => σ y * y = c)).card : ℤ) =
      ((q : ℤ) - (-1)) + (-1) * (q : ℤ) * (if c = 0 then 1 else 0) := by
  have hpow := sigma_eq_pow σ hσ hne q hq
  have hne0 : ∀ y : k, y ≠ 0 → σ y ≠ 0 := fun y hy h => hy (σ.injective (by rw [h, map_zero]))
  have hq2 : 2 ≤ q := by
    have h1 : 1 < Fintype.card k := Fintype.one_lt_card
    rw [hq] at h1
    by_contra h2
    have : q ≤ 1 := by omega
    have : q ^ 2 ≤ 1 := by nlinarith
    omega
  by_cases hc0 : c = 0
  · subst hc0
    have : univ.filter (fun y : k => σ y * y = 0) = {0} := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h
        by_contra hy
        exact mul_ne_zero (hne0 y hy) hy h
      · intro h
        rw [h, map_zero, zero_mul]
    rw [this, Finset.card_singleton, if_pos rfl]
    push_cast
    ring
  rw [if_neg hc0]

  set Fs := univ.filter (fun b : k => σ b = b ∧ b ≠ 0) with hFs
  set G : k → Finset k := fun b => univ.filter (fun y : k => σ y * y = b) with hG
  have hGle : ∀ b, (G b).card ≤ q + 1 := by
    intro b
    calc (G b).card ≤ (Polynomial.nthRoots (q + 1) b).toFinset.card := by
          apply Finset.card_le_card
          intro y hy
          simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and] at hy
          rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by omega), pow_succ, ← hpow y, hy]
      _ ≤ (Polynomial.nthRoots (q + 1) b).card := Multiset.toFinset_card_le _
      _ ≤ q + 1 := Polynomial.card_nthRoots _ _
  have hFle : Fs.card ≤ q - 1 := by
    calc Fs.card ≤ (Polynomial.nthRoots (q - 1) (1 : k)).toFinset.card := by
          apply Finset.card_le_card
          intro b hb
          simp only [hFs, Finset.mem_filter, Finset.mem_univ, true_and] at hb
          rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by omega)]
          have h1 : b ^ (q - 1) * b = b := by
            rw [← pow_succ, show q - 1 + 1 = q by omega, ← hpow b, hb.1]
          have h2 : b ^ (q - 1) * b = 1 * b := by rw [h1, one_mul]
          exact mul_right_cancel₀ hb.2 h2
      _ ≤ (Polynomial.nthRoots (q - 1) (1 : k)).card := Multiset.toFinset_card_le _
      _ ≤ q - 1 := Polynomial.card_nthRoots _ _
  have hsum : ∑ b ∈ Fs, (G b).card = q ^ 2 - 1 := by
    have hmaps : ∀ y ∈ univ.filter (fun y : k => y ≠ 0), σ y * y ∈ Fs := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      simp only [hFs, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨by rw [map_mul, hσ, mul_comm], mul_ne_zero (hne0 y hy) hy⟩
    have h1 := Finset.card_eq_sum_card_fiberwise hmaps
    have h2 : (univ.filter (fun y : k => y ≠ 0)).card = q ^ 2 - 1 := by
      rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hq]
    rw [← h2, h1]
    refine Finset.sum_congr rfl fun b hb => ?_
    simp only [hFs, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    congr 1
    ext y
    simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      refine ⟨fun hy => hb.2 ?_, h⟩
      rw [← h, hy, mul_zero]
    · exact fun h => h.2
  have hcF : c ∈ Fs := by
    simp only [hFs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hc, hc0⟩
  have hGc : (G c).card = q + 1 := by
    by_contra hlt
    have hlt' : (G c).card < q + 1 := lt_of_le_of_ne (hGle c) hlt
    have h1 : ∑ b ∈ Fs, (G b).card < ∑ b ∈ Fs, (q + 1) :=
      Finset.sum_lt_sum (fun b _ => hGle b) ⟨c, hcF, hlt'⟩
    rw [Finset.sum_const, smul_eq_mul, hsum] at h1
    have h2 : Fs.card * (q + 1) ≤ (q - 1) * (q + 1) := Nat.mul_le_mul_right _ hFle
    have h3 : (q - 1) * (q + 1) = q ^ 2 - 1 := by
      obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring_nf
      omega
    omega
  have : (univ.filter (fun y : k => σ y * y = c)).card = q + 1 := hGc
  rw [this]
  push_cast
  ring

/- English proof (translation)
Establish `h1 : (univ.filter (fun y : k × k => y.1 * y.2 = c)).card = ∑ a : k, (univ.filter (fun b : k => a * b = c)).card`. Simplify using `only [Finset.card_filter]`. Rewrite using `[← Finset.univ_product_univ, Finset.sum_product]`. Establish `h2 : ∀ a : k, a ≠ 0 → (univ.filter (fun b : k => a * b = c)).card = 1`. Introduce `a ha`.

Rewrite using `[Finset.card_eq_one]`. Use `⟨a⁻¹ * c, ?_⟩` and prove the remaining obligations. Use extensionality with `b`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Rewrite using `[← h, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]`. Introduce `h`. Rewrite using `[h, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]`. Establish `hk : 1 ≤ Fintype.card k` using `Fintype.card_pos`.

Establish `h0 : (univ.filter (fun b : k => (0 : k) * b = c)).card = if c = 0 then Fintype.card k else 0` using `by split_ifs with hc`. Substitute `hc` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Finset.card_eq_zero, Finset.filter_eq_empty_iff]`. Introduce `x _ h`.

Conclude with `hc (by rw [← h, zero_mul])`. Rewrite using `[h1, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : k)), Finset.sum_congr rfl fun a ha => h2 a (Finset.ne_of_mem_erase ha), h0]`. Simplify using `only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]`. Apply the tactic sequence `split_ifs <;> push_cast [Nat.cast_sub hk] <;> ring`.
-/
theorem card_mul_fibre {k : Type*} [Field k] [Fintype k] [DecidableEq k] (c : k) :
    ((univ.filter (fun y : k × k => y.1 * y.2 = c)).card : ℤ) =
      ((Fintype.card k : ℤ) - 1) + 1 * (Fintype.card k : ℤ) * (if c = 0 then 1 else 0) := by
  have h1 : (univ.filter (fun y : k × k => y.1 * y.2 = c)).card =
      ∑ a : k, (univ.filter (fun b : k => a * b = c)).card := by
    simp only [Finset.card_filter]
    rw [← Finset.univ_product_univ, Finset.sum_product]
  have h2 : ∀ a : k, a ≠ 0 → (univ.filter (fun b : k => a * b = c)).card = 1 := by
    intro a ha
    rw [Finset.card_eq_one]
    refine ⟨a⁻¹ * c, ?_⟩
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      rw [← h, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
    · intro h
      rw [h, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  have hk : 1 ≤ Fintype.card k := Fintype.card_pos
  have h0 : (univ.filter (fun b : k => (0 : k) * b = c)).card = if c = 0 then Fintype.card k else 0 := by
    split_ifs with hc
    · subst hc
      simp
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x _ h
      exact hc (by rw [← h, zero_mul])
  rw [h1, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : k)),
    Finset.sum_congr rfl fun a ha => h2 a (Finset.ne_of_mem_erase ha), h0]
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ]
  split_ifs <;> push_cast [Nat.cast_sub hk] <;> ring

end Formalism.HermitianLattices.Ext.L3.FiniteNormFibres

namespace Formalism.HermitianLattices.Ext.L3

/- English proof (translation)
Establish `h` using `FiniteNormFibres.card_sum_norm_fibres (fun y : k => σ y * y) (fun c => σ c = c) (fun c y hc => by simp only [map_sub, map_mul, hσ, hc]; ring) (q : ℤ) (-1) (by rw [hq]; push_cast; ring) (fun c hc => by convert FiniteNormFibres.card_norm_fibre σ hσ hne q hq c hc) M c hc`. Rewrite `h` using `[if_neg hc0, mul_pow]`. Establish `hq0 : (q : ℤ) ≠ 0`. Introduce `h0`. Establish `h1 : q = 0` using `by exact_mod_cast h0`.

Use `Fintype.card_pos (α := k)` as an intermediate fact. Rewrite `this` using `[hq, h1]`. Simplify using `at this`. Establish `key : (q : ℤ) * ((q : ℤ) ^ (M - 1) * ((q : ℤ) ^ M - (-1) ^ M)) = (q : ℤ) ^ (2 * M) + (-1) ^ M * (q : ℤ) ^ M * ((q : ℤ) * 0 - 1)`. Take `⟨M', rfl⟩ : ∃ M', M = M' + 1` from `⟨M - 1, by omega⟩`.

Rewrite using `[show M' + 1 - 1 = M' by omega]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Nat.card_eq_fintype_card, Fintype.card_subtype]`. Apply `mul_left_cancel₀ hq0` to reduce the goal to its premises. Rewrite using `[key]`.

Use `h using 3` and compare the differences between its conclusion and the goal.
-/
theorem card_herm_norm_eq {k : Type*} [Field k] [Fintype k] (σ : k ≃+* k)
    (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x) (q : ℕ) (hq : Fintype.card k = q ^ 2)
    (M : ℕ) (hM : 1 ≤ M) (c : k) (hc : σ c = c) (hc0 : c ≠ 0) :
    (Nat.card {x : Fin M → k // ∑ i, σ (x i) * x i = c} : ℤ) =
      (q : ℤ) ^ (M - 1) * ((q : ℤ) ^ M - (-1) ^ M) := by
  classical
  have h := FiniteNormFibres.card_sum_norm_fibres (fun y : k => σ y * y) (fun c => σ c = c)
    (fun c y hc => by simp only [map_sub, map_mul, hσ, hc]; ring) (q : ℤ) (-1)
    (by rw [hq]; push_cast; ring) (fun c hc => by convert FiniteNormFibres.card_norm_fibre σ hσ hne q hq c hc) M c hc
  rw [if_neg hc0, mul_pow] at h
  have hq0 : (q : ℤ) ≠ 0 := by
    intro h0
    have h1 : q = 0 := by exact_mod_cast h0
    have := Fintype.card_pos (α := k)
    rw [hq, h1] at this
    simp at this
  have key : (q : ℤ) * ((q : ℤ) ^ (M - 1) * ((q : ℤ) ^ M - (-1) ^ M)) =
      (q : ℤ) ^ (2 * M) + (-1) ^ M * (q : ℤ) ^ M * ((q : ℤ) * 0 - 1) := by
    obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
    rw [show M' + 1 - 1 = M' by omega]
    ring
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  apply mul_left_cancel₀ hq0
  rw [key]
  convert h using 3

/- English proof (translation)
Establish `h` using `FiniteNormFibres.card_sum_norm_fibres (fun y : k × k => y.1 * y.2) (fun _ => True) (fun _ _ _ => trivial) (q : ℤ) 1 (by rw [Fintype.card_prod, hq]; push_cast; ring) (fun c _ => by rw [← hq]; convert FiniteNormFibres.card_mul_fibre c) M c trivial`. Rewrite `h` using `[if_neg hc, one_mul]`. Establish `hq0 : (q : ℤ) ≠ 0`. Introduce `h0`. Establish `h1 : q = 0` using `by exact_mod_cast h0`.

Use `Fintype.card_pos (α := k)` as an intermediate fact. Rewrite `this` using `[hq, h1]`. Conclude with `lt_irrefl 0 this`. Establish `e : {x : (Fin M → k) × (Fin M → k) // ∑ i, x.1 i * x.2 i = c} ≃ {x : Fin M → k × k // ∑ i, (x i).1 * (x i).2 = c}` using `(Equiv.arrowProdEquivProdArrow _ _ _).symm.subtypeEquiv (fun x => Iff.rfl)`. Establish `key : (q : ℤ) * ((q : ℤ) ^ (2 * M - 1) - (q : ℤ) ^ (M - 1)) = (q : ℤ) ^ (2 * M) + (q : ℤ) ^ M * ((q : ℤ) * 0 - 1)`.

Take `⟨M', rfl⟩ : ∃ M', M = M' + 1` from `⟨M - 1, by omega⟩`. Rewrite using `[show 2 * (M' + 1) - 1 = 2 * M' + 1 by omega, show M' + 1 - 1 = M' by omega]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]`. Apply `mul_left_cancel₀ hq0` to reduce the goal to its premises.

Rewrite using `[key]`. Use `h using 3` and compare the differences between its conclusion and the goal.
-/
theorem card_dot_eq {k : Type*} [Field k] [Fintype k] (q : ℕ) (hq : Fintype.card k = q)
    (M : ℕ) (hM : 1 ≤ M) (c : k) (hc : c ≠ 0) :
    (Nat.card {x : (Fin M → k) × (Fin M → k) // ∑ i, x.1 i * x.2 i = c} : ℤ) =
      (q : ℤ) ^ (2 * M - 1) - (q : ℤ) ^ (M - 1) := by
  classical
  have h := FiniteNormFibres.card_sum_norm_fibres (fun y : k × k => y.1 * y.2) (fun _ => True) (fun _ _ _ => trivial)
    (q : ℤ) 1 (by rw [Fintype.card_prod, hq]; push_cast; ring)
    (fun c _ => by rw [← hq]; convert FiniteNormFibres.card_mul_fibre c) M c trivial
  rw [if_neg hc, one_mul] at h
  have hq0 : (q : ℤ) ≠ 0 := by
    intro h0
    have h1 : q = 0 := by exact_mod_cast h0
    have := Fintype.card_pos (α := k)
    rw [hq, h1] at this
    exact lt_irrefl 0 this
  have e : {x : (Fin M → k) × (Fin M → k) // ∑ i, x.1 i * x.2 i = c} ≃
      {x : Fin M → k × k // ∑ i, (x i).1 * (x i).2 = c} :=
    (Equiv.arrowProdEquivProdArrow _ _ _).symm.subtypeEquiv (fun x => Iff.rfl)
  have key : (q : ℤ) * ((q : ℤ) ^ (2 * M - 1) - (q : ℤ) ^ (M - 1)) =
      (q : ℤ) ^ (2 * M) + (q : ℤ) ^ M * ((q : ℤ) * 0 - 1) := by
    obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
    rw [show 2 * (M' + 1) - 1 = 2 * M' + 1 by omega, show M' + 1 - 1 = M' by omega]
    ring
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  apply mul_left_cancel₀ hq0
  rw [key]
  convert h using 3

end Formalism.HermitianLattices.Ext.L3
