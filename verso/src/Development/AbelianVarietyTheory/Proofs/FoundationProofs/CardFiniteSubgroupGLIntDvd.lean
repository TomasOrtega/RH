import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsInvariantNatLengthLattice

namespace GlobalTheory

namespace MinkowskiOrder

/- English proof (translation)
Use `haveI := Fact.mk hl`. Set `f : G →* GL (Fin n) (ZMod l)` to `(Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod l))).comp G.subtype`. Establish `hf : Function.Injective f`. Rewrite using `[injective_iff_map_eq_one]`. Introduce `g hg`.

Establish `hm : 0 < orderOf g` using `orderOf_pos g`. Establish `hpow : ((g : GL (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ) ^ orderOf g = 1`. Rewrite using `[← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, pow_orderOf_eq_one]`. Both sides reduce to the same expression. Establish `hent : ∀ i j, (l : ℤ) ∣ (((g : GL (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ) - 1) i j`.

Introduce `i j`. Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Establish `h1` using `congrArg (fun u : GL (Fin n) (ZMod l) => (u : Matrix (Fin n) (Fin n) (ZMod l)) i j) hg`. Establish `h2 : ((((g : GL (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ) i j : ℤ) : ZMod l) = (1 : Matrix (Fin n) (Fin n) (ZMod l)) i j` using `h1`. Rewrite using `[Matrix.sub_apply, Int.cast_sub, h2, Matrix.one_apply, Matrix.one_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Use `choose B hB using hent`. Establish `key` using `end_eq_one_of_pow_eq_one_of_congr (Fin n → ℤ) (Matrix.toLin' ((g : GL (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ)) (orderOf g) l hm (by rw [← Matrix.toLin'_pow, hpow, Matrix.toLin'_one]; rfl) h3 (by`. Introduce `y`. Use `⟨(Matrix.of B).mulVec y, ?_⟩` and prove the remaining obligations.

Establish `e : ((g : GL (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ) = 1 + l • Matrix.of B`. Use extensionality with `i j`. Use `hB i j` as an intermediate fact. Rewrite `this` using `[Matrix.sub_apply]`. Rewrite using `[Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul, ← this]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Matrix.toLin'_apply, e, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec])`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Apply `Matrix.toLin'.injective` to reduce the goal to its premises.

Rewrite using `[key]`. Conclude with `Matrix.toLin'_one.symm`. Establish `h` using `Subgroup.card_dvd_of_injective f hf`. Rewrite `h` using `[Matrix.card_GL_field, ZMod.card]`. Then use the resulting hypothesis.
-/
theorem card_dvd_prod (n : ℕ) (G : Subgroup (GL (Fin n) ℤ)) [Finite G] (l : ℕ) (hl : l.Prime)
    (h3 : 3 ≤ l) : Nat.card G ∣ ∏ i : Fin n, (l ^ n - l ^ (i : ℕ)) := by
  haveI := Fact.mk hl
  let f : G →* GL (Fin n) (ZMod l) :=
    (Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod l))).comp G.subtype
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hm : 0 < orderOf g := orderOf_pos g
    have hpow : ((g : GL (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ) ^ orderOf g = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, pow_orderOf_eq_one]
      rfl
    have hent : ∀ i j, (l : ℤ) ∣ (((g : GL (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ) - 1) i j := by
      intro i j
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      have h1 := congrArg (fun u : GL (Fin n) (ZMod l) => (u : Matrix (Fin n) (Fin n) (ZMod l)) i j) hg
      have h2 : ((((g : GL (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ) i j : ℤ) : ZMod l)
          = (1 : Matrix (Fin n) (Fin n) (ZMod l)) i j := h1
      rw [Matrix.sub_apply, Int.cast_sub, h2, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    choose B hB using hent
    have key := end_eq_one_of_pow_eq_one_of_congr (Fin n → ℤ)
      (Matrix.toLin' ((g : GL (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ)) (orderOf g) l hm
      (by rw [← Matrix.toLin'_pow, hpow, Matrix.toLin'_one]; rfl) h3 (by
        intro y
        refine ⟨(Matrix.of B).mulVec y, ?_⟩
        have e : ((g : GL (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ) = 1 + l • Matrix.of B := by
          ext i j
          have := hB i j
          rw [Matrix.sub_apply] at this
          rw [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul, ← this]
          ring
        rw [Matrix.toLin'_apply, e, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec])
    apply Subtype.ext
    apply Units.ext
    apply Matrix.toLin'.injective
    rw [key]
    exact Matrix.toLin'_one.symm
  have h := Subgroup.card_dvd_of_injective f hf
  rwa [Matrix.card_GL_field, ZMod.card] at h

/- English proof (translation)
Use `haveI := Fact.mk hp`. Use `haveI := Fact.mk hl`. Establish `hne0 : ∀ i, i < n → l ^ n - l ^ i ≠ 0` using `fun i hi => Nat.sub_ne_zero_of_lt (Nat.pow_lt_pow_right hl.one_lt hi)`. Rewrite using `[Fin.prod_univ_eq_prod_range (fun i => l ^ n - l ^ i) n, Nat.factorization_prod (fun i hi => hne0 i (Finset.mem_range.mp hi)), Finsupp.finset_sum_apply, ← Finset.sum_range_reflect]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations.

Establish `hi'` using `Finset.mem_range.mp hi`. Establish `e : l ^ n - l ^ (n - 1 - i) = l ^ (n - 1 - i) * (l ^ (i + 1) - 1)`. Rewrite using `[Nat.mul_sub, ← pow_add, mul_one]`. Use `congr 2`. Use linear arithmetic over natural numbers and integers.

Establish `h1 : l ^ (i + 1) - 1 ≠ 0` using `Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by omega) hl.one_lt)`. Rewrite using `[e, Nat.factorization_def _ hp, padicValNat.mul (pow_ne_zero _ hl.ne_zero) h1, padicValNat_prime_prime_pow _ hne, zero_add]`.
-/
theorem val_prod (n p l : ℕ) (hp : p.Prime) (hl : l.Prime) (hne : p ≠ l) :
    (∏ i : Fin n, (l ^ n - l ^ (i : ℕ))).factorization p
      = ∑ i ∈ Finset.range n, padicValNat p (l ^ (i + 1) - 1) := by
  haveI := Fact.mk hp
  haveI := Fact.mk hl
  have hne0 : ∀ i, i < n → l ^ n - l ^ i ≠ 0 := fun i hi =>
    Nat.sub_ne_zero_of_lt (Nat.pow_lt_pow_right hl.one_lt hi)
  rw [Fin.prod_univ_eq_prod_range (fun i => l ^ n - l ^ i) n,
    Nat.factorization_prod (fun i hi => hne0 i (Finset.mem_range.mp hi)), Finsupp.finset_sum_apply,
    ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  have e : l ^ n - l ^ (n - 1 - i) = l ^ (n - 1 - i) * (l ^ (i + 1) - 1) := by
    rw [Nat.mul_sub, ← pow_add, mul_one]
    congr 2
    omega
  have h1 : l ^ (i + 1) - 1 ≠ 0 :=
    Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by omega) hl.one_lt)
  rw [e, Nat.factorization_def _ hp, padicValNat.mul (pow_ne_zero _ hl.ne_zero) h1,
    padicValNat_prime_prime_pow _ hne, zero_add]

/- English proof (translation)
Use `haveI : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩`. Use `haveI := ZMod.isCyclic_units_of_prime_pow p hp h2 2`. Take `⟨g, hg⟩` from `IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod (p ^ 2))ˣ)`. Take `⟨l, hlp, hl, hlg⟩` from `Nat.forall_exists_prime_gt_and_eq_mod g.isUnit p`. Use `⟨l, hl, hlp, fun i hi => ?_⟩` and prove the remaining obligations.

Rewrite `hg` using `[Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow hp (by norm_num)]`. Establish `: g ^ i = 1`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_pow_eq_pow_val, ← hlg, Units.val_one]`. Establish `h0` using `(ZMod.natCast_eq_zero_iff _ _).mpr hi`.

Rewrite `h0` using `[Nat.cast_sub (Nat.one_le_pow _ _ hl.pos), Nat.cast_pow, Nat.cast_one, sub_eq_zero]`. Conclude with `h0`. Use `orderOf_dvd_of_pow_eq_one this` as an intermediate fact. Rewrite `this` using `[hg]`. Simplify using `using this`.
-/
theorem exists_prime_gen (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) :
    ∃ l : ℕ, l.Prime ∧ p < l ∧ ∀ i, p ^ 2 ∣ l ^ i - 1 → p * (p - 1) ∣ i := by
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI := ZMod.isCyclic_units_of_prime_pow p hp h2 2
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod (p ^ 2))ˣ)
  obtain ⟨l, hlp, hl, hlg⟩ := Nat.forall_exists_prime_gt_and_eq_mod g.isUnit p
  refine ⟨l, hl, hlp, fun i hi => ?_⟩
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow hp (by norm_num)] at hg
  have : g ^ i = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, ← hlg, Units.val_one]
    have h0 := (ZMod.natCast_eq_zero_iff _ _).mpr hi
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hl.pos), Nat.cast_pow, Nat.cast_one, sub_eq_zero] at h0
    exact h0
  have := orderOf_dvd_of_pow_eq_one this
  rw [hg] at this
  simpa using this

/- English proof (translation)
Use `haveI := Fact.mk hp`. Establish `hp2` using `hp.two_le`. Establish `hodd : Odd p` using `hp.odd_of_ne_two h2`. Establish `hnd : ∀ k, ¬ p ∣ l ^ k` using `fun k hk => by`. Use `(Nat.prime_dvd_prime_iff_eq hp hl).mp (hp.dvd_of_dvd_pow hk)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hlte : ∀ k m, k ≠ 0 → m ≠ 0 → p ∣ l ^ k - 1 → padicValNat p (l ^ (k * m) - 1) = padicValNat p (l ^ k - 1) + padicValNat p m`. Introduce `k m hk hm hd`. Use `padicValNat.pow_sub_pow (p := p) (x := l ^ k) (y := 1) hodd (Nat.one_lt_pow hk hl.one_lt) hd (hnd k) hm` as an intermediate fact. Rewrite `this` using `[one_pow, ← pow_mul]`. Then use the resulting hypothesis.

Establish `hne : ∀ k, k ≠ 0 → l ^ k - 1 ≠ 0` using `fun k hk => Nat.sub_ne_zero_of_lt (Nat.one_lt_pow hk hl.one_lt)`. Establish `hferm : p ∣ l ^ (p - 1) - 1`. Establish `hc : l.Coprime p` using `(Nat.coprime_primes hl hp).mpr (by omega)`. Use `Nat.ModEq.pow_totient hc` as an intermediate fact. Rewrite `this` using `[Nat.totient_prime hp]`.

Conclude with `(Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hl.pos)).mp this.symm`. Establish `hone : padicValNat p (l ^ (p - 1) - 1) ≤ 1`. Assume the negation of the conclusion as `hc`. Establish `h0` using `h (p - 1) ((padicValNat_dvd_iff_le (hne (p - 1) (by omega))).mpr (by omega))`. Use `Nat.le_of_dvd (by omega) h0` as an intermediate fact.

Establish `h3 : 2 * (p - 1) ≤ p * (p - 1)` using `Nat.mul_le_mul_right _ hp2`. Use linear arithmetic over natural numbers and integers. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`.

Rewrite using `[Finset.sum_range_succ, Nat.succ_div]`. Use `split_ifs with hd`. Establish `e : n + 1 = (p - 1) * (n / (p - 1) + 1)`. Use `Nat.succ_div_of_dvd hd` as an intermediate fact. Rewrite using `[← this, Nat.mul_div_cancel' hd]`.

Rewrite using `[Nat.factorial_succ, padicValNat.mul (Nat.succ_ne_zero _) (Nat.factorial_ne_zero _)]`. Use `hlte (p - 1) (n / (p - 1) + 1) (by omega) (Nat.succ_ne_zero _) hferm` as an intermediate fact. Rewrite `this` using `[← e]`. Simplify using `only [Nat.succ_eq_add_one]`. Use linear arithmetic over natural numbers and integers.

Establish `: padicValNat p (l ^ (n + 1) - 1) = 0`. Apply `padicValNat.eq_zero_of_not_dvd` to reduce the goal to its premises. Introduce `hd'`. Establish `h1` using `hlte (n + 1) p (by omega) (by omega) hd'`. Establish `h3` using `one_le_padicValNat_of_dvd (hne (n + 1) (by omega)) hd'`.

Rewrite `h1` using `[padicValNat_self]`. Establish `h4` using `h _ ((padicValNat_dvd_iff_le (hne ((n + 1) * p) (Nat.mul_ne_zero (by omega) (by omega)))).mpr (by omega : 2 ≤ _))`. Rewrite `h4` using `[mul_comm (n + 1)]`. Conclude with `hd (Nat.dvd_of_mul_dvd_mul_left hp.pos h4)`. Simplify using `only [add_zero]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem sum_odd (p l : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (hl : l.Prime) (hpl : p < l)
    (h : ∀ i, p ^ 2 ∣ l ^ i - 1 → p * (p - 1) ∣ i) (n : ℕ) :
    ∑ i ∈ Finset.range n, padicValNat p (l ^ (i + 1) - 1)
      ≤ n / (p - 1) + padicValNat p (n / (p - 1)).factorial := by
  haveI := Fact.mk hp
  have hp2 := hp.two_le
  have hodd : Odd p := hp.odd_of_ne_two h2
  have hnd : ∀ k, ¬ p ∣ l ^ k := fun k hk => by
    have := (Nat.prime_dvd_prime_iff_eq hp hl).mp (hp.dvd_of_dvd_pow hk)
    omega
  have hlte : ∀ k m, k ≠ 0 → m ≠ 0 → p ∣ l ^ k - 1 →
      padicValNat p (l ^ (k * m) - 1) = padicValNat p (l ^ k - 1) + padicValNat p m := by
    intro k m hk hm hd
    have := padicValNat.pow_sub_pow (p := p) (x := l ^ k) (y := 1) hodd
      (Nat.one_lt_pow hk hl.one_lt) hd (hnd k) hm
    rwa [one_pow, ← pow_mul] at this
  have hne : ∀ k, k ≠ 0 → l ^ k - 1 ≠ 0 := fun k hk =>
    Nat.sub_ne_zero_of_lt (Nat.one_lt_pow hk hl.one_lt)
  have hferm : p ∣ l ^ (p - 1) - 1 := by
    have hc : l.Coprime p := (Nat.coprime_primes hl hp).mpr (by omega)
    have := Nat.ModEq.pow_totient hc
    rw [Nat.totient_prime hp] at this
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hl.pos)).mp this.symm
  have hone : padicValNat p (l ^ (p - 1) - 1) ≤ 1 := by
    by_contra hc
    have h0 := h (p - 1) ((padicValNat_dvd_iff_le (hne (p - 1) (by omega))).mpr (by omega))
    have := Nat.le_of_dvd (by omega) h0
    have h3 : 2 * (p - 1) ≤ p * (p - 1) := Nat.mul_le_mul_right _ hp2
    omega
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.succ_div]
    split_ifs with hd
    · have e : n + 1 = (p - 1) * (n / (p - 1) + 1) := by
        have := Nat.succ_div_of_dvd hd
        rw [← this, Nat.mul_div_cancel' hd]
      rw [Nat.factorial_succ, padicValNat.mul (Nat.succ_ne_zero _) (Nat.factorial_ne_zero _)]
      have := hlte (p - 1) (n / (p - 1) + 1) (by omega) (Nat.succ_ne_zero _) hferm
      rw [← e] at this
      simp only [Nat.succ_eq_add_one]
      omega
    · have : padicValNat p (l ^ (n + 1) - 1) = 0 := by
        apply padicValNat.eq_zero_of_not_dvd
        intro hd'
        have h1 := hlte (n + 1) p (by omega) (by omega) hd'
        have h3 := one_le_padicValNat_of_dvd (hne (n + 1) (by omega)) hd'
        rw [padicValNat_self] at h1
        have h4 := h _ ((padicValNat_dvd_iff_le (hne ((n + 1) * p)
          (Nat.mul_ne_zero (by omega) (by omega)))).mpr (by omega : 2 ≤ _))
        rw [mul_comm (n + 1)] at h4
        exact hd (Nat.dvd_of_mul_dvd_mul_left hp.pos h4)
      simp only [add_zero]
      omega

end MinkowskiOrder

open Matrix in
/- English proof (translation)
Apply `Finset.prod_pos` to reduce the goal to its premises. Introduce `i _`. Use `Nat.pow_lt_pow_right hq i.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
private theorem prod_pow_sub_pow_pos (q n : ℕ) (hq : 2 ≤ q) :
    0 < ∏ i : Fin n, (q ^ n - q ^ (i : ℕ)) := by
  apply Finset.prod_pos
  intro i _
  have := Nat.pow_lt_pow_right hq i.isLt
  omega

open Matrix in
/- English proof (translation)
Rewrite using `[Fin.prod_univ_succ]`. Simplify using `only [Fin.val_zero, pow_zero, Fin.val_succ]`. Use `congr 1`. Establish `h : ∀ i : Fin n, q ^ (n + 1) - q ^ ((i : ℕ) + 1) = q * (q ^ n - q ^ (i : ℕ))`. Introduce `i`.

Rewrite using `[pow_succ', pow_succ', Nat.mul_sub]`. Rewrite using `[Finset.prod_congr rfl (fun i _ => h i), Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`.
-/
private theorem prod_pow_sub_pow_succ (q n : ℕ) :
    ∏ i : Fin (n + 1), (q ^ (n + 1) - q ^ (i : ℕ)) =
      (q ^ (n + 1) - 1) * (q ^ n * ∏ i : Fin n, (q ^ n - q ^ (i : ℕ))) := by
  rw [Fin.prod_univ_succ]
  simp only [Fin.val_zero, pow_zero, Fin.val_succ]
  congr 1
  have h : ∀ i : Fin n, q ^ (n + 1) - q ^ ((i : ℕ) + 1) = q * (q ^ n - q ^ (i : ℕ)) := by
    intro i
    rw [pow_succ', pow_succ', Nat.mul_sub]
  rw [Finset.prod_congr rfl (fun i _ => h i), Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

open Matrix in
/- English proof (translation)
The claim follows from `(padicValNat_dvd_iff_le hb).mp (pow_padicValNat_dvd.trans h)`.
-/
private theorem padicValNat_le_padicValNat_of_dvd {p a b : ℕ} [Fact p.Prime] (hb : b ≠ 0) (h : a ∣ b) :
    padicValNat p a ≤ padicValNat p b :=
  (padicValNat_dvd_iff_le hb).mp (pow_padicValNat_dvd.trans h)

open Matrix in
/- English proof (translation)
Establish `hlte` using `padicValNat.pow_two_sub_pow (x := 3) (y := 1) (by norm_num) (by norm_num) (by norm_num) (n := 2 * k) (by omega) (even_two_mul k)`. Establish `h4 : padicValNat 2 (3 + 1) = 2`. Rewrite using `[show 3 + 1 = 2 ^ 2 by norm_num, padicValNat.prime_pow]`. Rewrite `hlte` using `[h4, show 3 - 1 = 2 by norm_num, padicValNat_self, padicValNat.mul (by norm_num) hk.ne', padicValNat_self, one_pow]`. Establish `hne : 3 ^ (2 * k) - 1 ≠ 0`.

Use `Nat.one_lt_pow (n := 2 * k) (by omega) (by norm_num : 1 < 3)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hdvd : 3 ^ k - 1 ∣ 3 ^ (2 * k) - 1`. Establish `h1 : 1 ≤ 3 ^ k` using `Nat.one_le_pow _ _ (by norm_num)`. Establish `h2 : 1 ≤ 3 ^ (2 * k)` using `Nat.one_le_pow _ _ (by norm_num)`.

Use `⟨3 ^ k + 1, ?_⟩` and prove the remaining obligations. Use `zify [h1, h2]`. Expand and normalize the polynomial expressions, which then agree. Use `padicValNat_le_padicValNat_of_dvd (p := 2) hne hdvd` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
private theorem padicValNat_two_three_pow_sub_one_le (k : ℕ) (hk : 0 < k) :
    padicValNat 2 (3 ^ k - 1) ≤ 3 + padicValNat 2 k := by
  have hlte := padicValNat.pow_two_sub_pow (x := 3) (y := 1) (by norm_num) (by norm_num)
    (by norm_num) (n := 2 * k) (by omega) (even_two_mul k)
  have h4 : padicValNat 2 (3 + 1) = 2 := by
    rw [show 3 + 1 = 2 ^ 2 by norm_num, padicValNat.prime_pow]
  rw [h4, show 3 - 1 = 2 by norm_num, padicValNat_self, padicValNat.mul (by norm_num) hk.ne',
    padicValNat_self, one_pow] at hlte
  have hne : 3 ^ (2 * k) - 1 ≠ 0 := by
    have := Nat.one_lt_pow (n := 2 * k) (by omega) (by norm_num : 1 < 3)
    omega
  have hdvd : 3 ^ k - 1 ∣ 3 ^ (2 * k) - 1 := by
    have h1 : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by norm_num)
    have h2 : 1 ≤ 3 ^ (2 * k) := Nat.one_le_pow _ _ (by norm_num)
    refine ⟨3 ^ k + 1, ?_⟩
    zify [h1, h2]
    ring
  have := padicValNat_le_padicValNat_of_dvd (p := 2) hne hdvd
  omega

open Matrix in
/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `hqn : 0 < 3 ^ (n + 1) - 1`. Use `Nat.one_lt_pow (n := n + 1) (by omega) (by norm_num : 1 < 3)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hpow : padicValNat 2 (3 ^ n) = 0` using `padicValNat.eq_zero_of_not_dvd fun h => by`. Use `Nat.prime_two.dvd_of_dvd_pow h` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hq0 : 3 ^ n ≠ 0` using `by positivity`.

Establish `hP` using `(prod_pow_sub_pow_pos 3 n (by norm_num)).ne'`. Rewrite using `[prod_pow_sub_pow_succ, padicValNat.mul hqn.ne' (Nat.mul_ne_zero hq0 hP), padicValNat.mul hq0 hP, hpow, zero_add, Nat.factorial_succ, padicValNat.mul (by omega) (Nat.factorial_ne_zero _)]`. Use `padicValNat_two_three_pow_sub_one_le (n + 1) (by omega)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
private theorem padicValNat_two_prod_three_pow_sub_le (n : ℕ) :
    padicValNat 2 (∏ i : Fin n, (3 ^ n - 3 ^ (i : ℕ))) ≤ 3 * n + padicValNat 2 n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hqn : 0 < 3 ^ (n + 1) - 1 := by
      have := Nat.one_lt_pow (n := n + 1) (by omega) (by norm_num : 1 < 3)
      omega
    have hpow : padicValNat 2 (3 ^ n) = 0 :=
      padicValNat.eq_zero_of_not_dvd fun h => by
        have := Nat.prime_two.dvd_of_dvd_pow h
        omega
    have hq0 : 3 ^ n ≠ 0 := by positivity
    have hP := (prod_pow_sub_pow_pos 3 n (by norm_num)).ne'
    rw [prod_pow_sub_pow_succ, padicValNat.mul hqn.ne' (Nat.mul_ne_zero hq0 hP),
      padicValNat.mul hq0 hP, hpow, zero_add, Nat.factorial_succ,
      padicValNat.mul (by omega) (Nat.factorial_ne_zero _)]
    have := padicValNat_two_three_pow_sub_one_le (n + 1) (by omega)
    omega

open Matrix in
/- English proof (translation)
Rewrite using `[padicValNat.mul (by positivity) (Nat.factorial_ne_zero _), show 8 ^ n = 2 ^ (3 * n) by rw [pow_mul]; norm_num, padicValNat.prime_pow]`. Establish `h1` using `padicValNat_two_prod_three_pow_sub_le n`. Establish `h2` using `padicValNat_le_padicValNat_of_dvd (p := 2) (Nat.factorial_ne_zero (2 * n)) (Nat.factorial_dvd_factorial (by omega : n ≤ 2 * n))`. Use linear arithmetic over natural numbers and integers.
-/
private theorem padicValNat_two_prod_three_pow_sub_le_eight_pow_factorial (n : ℕ) :
    padicValNat 2 (∏ i : Fin n, (3 ^ n - 3 ^ (i : ℕ))) ≤
      padicValNat 2 (8 ^ n * (2 * n).factorial) := by
  rw [padicValNat.mul (by positivity) (Nat.factorial_ne_zero _),
    show 8 ^ n = 2 ^ (3 * n) by rw [pow_mul]; norm_num, padicValNat.prime_pow]
  have h1 := padicValNat_two_prod_three_pow_sub_le n
  have h2 := padicValNat_le_padicValNat_of_dvd (p := 2) (Nat.factorial_ne_zero (2 * n))
    (Nat.factorial_dvd_factorial (by omega : n ≤ 2 * n))
  omega

open Matrix in
/- English proof (translation)
Establish `hp'` using `hp.out`. Establish `hp1 : 0 < p - 1` using `by have := hp'.two_le; omega`. Use `haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp'.ne_zero⟩`. Use `haveI := ZMod.isCyclic_units_of_prime_pow p hp' hp2 2`. Take `⟨u, hu⟩` from `IsCyclic.exists_generator (α := (ZMod (p ^ 2))ˣ)`.

Establish `hord : orderOf u = p * (p - 1)`. Rewrite using `[orderOf_eq_card_of_forall_mem_zpowers hu, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow hp' (by norm_num), pow_one]`. Take `⟨q, hqgt, hq, hqu⟩` from `Nat.forall_exists_prime_gt_and_eq_mod u.isUnit p`. Establish `hq1 : 1 < q` using `hq.one_lt`. Establish `hpq : ¬ p ∣ q` using `fun h => by`.

Use `(Nat.prime_dvd_prime_iff_eq hp' hq).mp h` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `key : ∀ m, p ^ 2 ∣ q ^ m - 1 ↔ p * (p - 1) ∣ m`. Introduce `m`. Rewrite using `[← hord, orderOf_dvd_iff_pow_eq_one, ← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), sub_eq_zero, Nat.cast_pow, hqu, Nat.cast_one, ← Units.val_pow_eq_pow_val, Units.val_eq_one]`.

Establish `hodd : Odd p` using `hp'.odd_of_ne_two hp2`. Use `⟨q, hq, hqgt, ?_, ?_⟩` and prove the remaining obligations. Introduce `k hk hdvd`. Establish `hqk : 1 < q ^ k` using `Nat.one_lt_pow hk.ne' hq1`. Establish `hnd : ¬ p ∣ q ^ k` using `fun h => hpq (hp'.dvd_of_dvd_pow h)`.

Establish `hlte` using `padicValNat.pow_sub_pow (p := p) (y := 1) hodd hqk (by simpa using hdvd) hnd (n := p) hp'.ne_zero`. Rewrite `hlte` using `[one_pow, ← pow_mul, padicValNat_self]`. Establish `h1 : 1 ≤ padicValNat p (q ^ k - 1)` using `one_le_padicValNat_of_dvd (by omega) hdvd`. Establish `hne : q ^ (k * p) - 1 ≠ 0`. Use `Nat.one_lt_pow (Nat.mul_ne_zero hk.ne' hp'.ne_zero) hq1` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `h2 : p ^ 2 ∣ q ^ (k * p) - 1` using `(padicValNat_dvd_iff_le hne).mpr (by omega)`. Rewrite `h2` using `[key, mul_comm k p]`. Conclude with `Nat.dvd_of_mul_dvd_mul_left hp'.pos h2`. Introduce `j hj`.

Establish `hcop : Nat.Coprime q p` using `(Nat.coprime_primes hq hp').mpr (by omega)`. Establish `hferm : p ∣ q ^ (p - 1) - 1`. Use `Nat.ModEq.pow_totient hcop` as an intermediate fact. Rewrite `this` using `[Nat.totient_prime hp']`. Conclude with `(Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).mp this.symm`.

Establish `hqp1 : 1 < q ^ (p - 1)` using `Nat.one_lt_pow hp1.ne' hq1`. Establish `hne : q ^ (p - 1) - 1 ≠ 0` using `by omega`. Establish `hv1 : padicValNat p (q ^ (p - 1) - 1) = 1`. Establish `h1 : 1 ≤ padicValNat p (q ^ (p - 1) - 1)` using `one_le_padicValNat_of_dvd hne hferm`. Assume the negation of the conclusion as `hne1`.

Establish `h2 : p ^ 2 ∣ q ^ (p - 1) - 1` using `(padicValNat_dvd_iff_le hne).mpr (by omega)`. Rewrite `h2` using `[key]`. Use `Nat.le_of_dvd hp1 h2` as an intermediate fact. Establish `: p - 1 < p * (p - 1)`. Use `hp'.two_le` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Use linear arithmetic over natural numbers and integers. Establish `hnd : ¬ p ∣ q ^ (p - 1)` using `fun h => hpq (hp'.dvd_of_dvd_pow h)`. Establish `hlte` using `padicValNat.pow_sub_pow (p := p) (y := 1) hodd hqp1 (by simpa using hferm) hnd (n := j) hj.ne'`. Rewrite `hlte` using `[one_pow, ← pow_mul, hv1]`.

Conclude with `hlte`.
-/
private theorem exists_prime_gt_order_padicValNat_pow_sub_one (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ q, q.Prime ∧ p < q ∧ (∀ k, 0 < k → p ∣ q ^ k - 1 → (p - 1) ∣ k) ∧
      (∀ j, 0 < j → padicValNat p (q ^ ((p - 1) * j) - 1) = 1 + padicValNat p j) := by
  have hp' := hp.out
  have hp1 : 0 < p - 1 := by have := hp'.two_le; omega
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp'.ne_zero⟩
  haveI := ZMod.isCyclic_units_of_prime_pow p hp' hp2 2
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := (ZMod (p ^ 2))ˣ)
  have hord : orderOf u = p * (p - 1) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hu, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow hp' (by norm_num), pow_one]
  obtain ⟨q, hqgt, hq, hqu⟩ := Nat.forall_exists_prime_gt_and_eq_mod u.isUnit p
  have hq1 : 1 < q := hq.one_lt
  have hpq : ¬ p ∣ q := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq hp' hq).mp h
    omega
  have key : ∀ m, p ^ 2 ∣ q ^ m - 1 ↔ p * (p - 1) ∣ m := by
    intro m
    rw [← hord, orderOf_dvd_iff_pow_eq_one, ← ZMod.natCast_eq_zero_iff,
      Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), sub_eq_zero, Nat.cast_pow, hqu, Nat.cast_one,
      ← Units.val_pow_eq_pow_val, Units.val_eq_one]
  have hodd : Odd p := hp'.odd_of_ne_two hp2
  refine ⟨q, hq, hqgt, ?_, ?_⟩
  · intro k hk hdvd
    have hqk : 1 < q ^ k := Nat.one_lt_pow hk.ne' hq1
    have hnd : ¬ p ∣ q ^ k := fun h => hpq (hp'.dvd_of_dvd_pow h)
    have hlte := padicValNat.pow_sub_pow (p := p) (y := 1) hodd hqk (by simpa using hdvd) hnd
      (n := p) hp'.ne_zero
    rw [one_pow, ← pow_mul, padicValNat_self] at hlte
    have h1 : 1 ≤ padicValNat p (q ^ k - 1) := one_le_padicValNat_of_dvd (by omega) hdvd
    have hne : q ^ (k * p) - 1 ≠ 0 := by
      have := Nat.one_lt_pow (Nat.mul_ne_zero hk.ne' hp'.ne_zero) hq1
      omega
    have h2 : p ^ 2 ∣ q ^ (k * p) - 1 := (padicValNat_dvd_iff_le hne).mpr (by omega)
    rw [key, mul_comm k p] at h2
    exact Nat.dvd_of_mul_dvd_mul_left hp'.pos h2
  · intro j hj
    have hcop : Nat.Coprime q p := (Nat.coprime_primes hq hp').mpr (by omega)
    have hferm : p ∣ q ^ (p - 1) - 1 := by
      have := Nat.ModEq.pow_totient hcop
      rw [Nat.totient_prime hp'] at this
      exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).mp this.symm
    have hqp1 : 1 < q ^ (p - 1) := Nat.one_lt_pow hp1.ne' hq1
    have hne : q ^ (p - 1) - 1 ≠ 0 := by omega
    have hv1 : padicValNat p (q ^ (p - 1) - 1) = 1 := by
      have h1 : 1 ≤ padicValNat p (q ^ (p - 1) - 1) := one_le_padicValNat_of_dvd hne hferm
      by_contra hne1
      have h2 : p ^ 2 ∣ q ^ (p - 1) - 1 := (padicValNat_dvd_iff_le hne).mpr (by omega)
      rw [key] at h2
      have := Nat.le_of_dvd hp1 h2
      have : p - 1 < p * (p - 1) := by
        have := hp'.two_le
        nlinarith
      omega
    have hnd : ¬ p ∣ q ^ (p - 1) := fun h => hpq (hp'.dvd_of_dvd_pow h)
    have hlte := padicValNat.pow_sub_pow (p := p) (y := 1) hodd hqp1 (by simpa using hferm) hnd
      (n := j) hj.ne'
    rw [one_pow, ← pow_mul, hv1] at hlte
    exact hlte

open Matrix in
/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `hqn : 0 < q ^ (n + 1) - 1`. Use `Nat.one_lt_pow (n := n + 1) (by omega) (by omega : 1 < q)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hpow : padicValNat p (q ^ n) = 0` using `padicValNat.eq_zero_of_not_dvd fun h => hqp (hp.out.dvd_of_dvd_pow h)`. Establish `hq0 : q ^ n ≠ 0` using `by positivity`. Establish `hP` using `(prod_pow_sub_pow_pos q n hq).ne'`. Rewrite using `[prod_pow_sub_pow_succ, padicValNat.mul hqn.ne' (Nat.mul_ne_zero hq0 hP), padicValNat.mul hq0 hP, hpow, zero_add, ih, Nat.succ_div]`.

Establish `hp1 : 0 < p - 1` using `by have := hp.out.two_le; omega`. Distinguish the cases in `hd : (p - 1) ∣ n + 1`. Take `⟨j, hj⟩` from `hd`. Establish `hj0 : 0 < j`. Break down `Nat.eq_zero_or_pos j with h | h` into its components or cases.

Simplify using `[h] at hj`. Conclude with `h`. Take `⟨m, rfl⟩ : ∃ m, j = m + 1` from `⟨j - 1, by omega⟩`. Establish `hdiv' : (n + 1) / (p - 1) = m + 1` using `by rw [hj, Nat.mul_div_cancel_left _ hp1]`. Establish `hn : n / (p - 1) = m`.

Rewrite `hdiv'` using `[Nat.succ_div, if_pos ⟨_, hj⟩]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_pos ⟨_, hj⟩, hn, hj, hval _ hj0, padicValNat_factorial_mul, padicValNat_factorial_mul, Nat.factorial_succ, padicValNat.mul (by omega) (Nat.factorial_ne_zero _)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hd, add_zero, padicValNat.eq_zero_of_not_dvd (fun h => hd (hdiv _ (by omega) h)), zero_add]`.
-/
private theorem padicValNat_prod_pow_sub_pow_eq_padicValNat_factorial (p q : ℕ) [hp : Fact p.Prime] (hq : 2 ≤ q)
    (hqp : ¬ p ∣ q) (hdiv : ∀ k, 0 < k → p ∣ q ^ k - 1 → (p - 1) ∣ k)
    (hval : ∀ j, 0 < j → padicValNat p (q ^ ((p - 1) * j) - 1) = 1 + padicValNat p j) (n : ℕ) :
    padicValNat p (∏ i : Fin n, (q ^ n - q ^ (i : ℕ))) =
      padicValNat p (p * (n / (p - 1))).factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hqn : 0 < q ^ (n + 1) - 1 := by
      have := Nat.one_lt_pow (n := n + 1) (by omega) (by omega : 1 < q)
      omega
    have hpow : padicValNat p (q ^ n) = 0 :=
      padicValNat.eq_zero_of_not_dvd fun h => hqp (hp.out.dvd_of_dvd_pow h)
    have hq0 : q ^ n ≠ 0 := by positivity
    have hP := (prod_pow_sub_pow_pos q n hq).ne'
    rw [prod_pow_sub_pow_succ, padicValNat.mul hqn.ne' (Nat.mul_ne_zero hq0 hP),
      padicValNat.mul hq0 hP, hpow, zero_add, ih, Nat.succ_div]
    have hp1 : 0 < p - 1 := by have := hp.out.two_le; omega
    by_cases hd : (p - 1) ∣ n + 1
    · obtain ⟨j, hj⟩ := hd
      have hj0 : 0 < j := by
        rcases Nat.eq_zero_or_pos j with h | h
        · simp [h] at hj
        · exact h
      obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      have hdiv' : (n + 1) / (p - 1) = m + 1 := by rw [hj, Nat.mul_div_cancel_left _ hp1]
      have hn : n / (p - 1) = m := by
        rw [Nat.succ_div, if_pos ⟨_, hj⟩] at hdiv'
        omega
      rw [if_pos ⟨_, hj⟩, hn, hj, hval _ hj0, padicValNat_factorial_mul, padicValNat_factorial_mul,
        Nat.factorial_succ, padicValNat.mul (by omega) (Nat.factorial_ne_zero _)]
      ring
    · rw [if_neg hd, add_zero,
        padicValNat.eq_zero_of_not_dvd (fun h => hd (hdiv _ (by omega) h)), zero_add]

open Matrix in
/- English proof (translation)
Establish `h2` using `hp.out.two_le`. Establish `hle : p * (n / (p - 1)) ≤ 2 * n`. Use `Nat.mul_div_le n (p - 1)` as an intermediate fact. Establish `hp' : p ≤ 2 * (p - 1)` using `by omega`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `padicValNat_le_padicValNat_of_dvd (by positivity) ((Nat.factorial_dvd_factorial hle).trans (Dvd.intro_left _ rfl))`.
-/
private theorem padicValNat_factorial_le_padicValNat_eight_pow_mul_factorial (p n : ℕ) [hp : Fact p.Prime] :
    padicValNat p (p * (n / (p - 1))).factorial ≤ padicValNat p (8 ^ n * (2 * n).factorial) := by
  have h2 := hp.out.two_le
  have hle : p * (n / (p - 1)) ≤ 2 * n := by
    have := Nat.mul_div_le n (p - 1)
    have hp' : p ≤ 2 * (p - 1) := by omega
    calc p * (n / (p - 1)) ≤ 2 * (p - 1) * (n / (p - 1)) := Nat.mul_le_mul_right _ hp'
      _ = 2 * ((p - 1) * (n / (p - 1))) := by ring
      _ ≤ 2 * n := by omega
  exact padicValNat_le_padicValNat_of_dvd (by positivity)
    ((Nat.factorial_dvd_factorial hle).trans (Dvd.intro_left _ rfl))

open Matrix in
/- English proof (translation)
Use `choose C hC using hcong`. Establish `hg : (g : Matrix (Fin n) (Fin n) ℤ) = 1 + (q : ℤ) • Matrix.of C`. Use extensionality with `i j`. Use `hC i j` as an intermediate fact. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `key` using `_root_.GlobalTheory.end_eq_one_of_pow_eq_one_of_congr (Fin n → ℤ) (Matrix.toLinAlgEquiv' (g : Matrix (Fin n) (Fin n) ℤ)) k q hk ?_ hq ?_`. Establish `h1 : (g : Matrix (Fin n) (Fin n) ℤ) = 1`. Apply `Matrix.toLinAlgEquiv'.injective` to reduce the goal to its premises. Rewrite using `[key, map_one]`.

Conclude with `Units.ext h1`. Rewrite using `[← map_pow, ← Units.val_pow_eq_pow_val, hgk, Units.val_one, map_one]`. Introduce `y`. Use `⟨Matrix.of C *ᵥ y, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.toLinAlgEquiv'_apply, hg, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, ← Nat.cast_smul_eq_nsmul ℤ]`.
-/
private theorem eq_one_of_pow_eq_one_of_congr_one_mod {n : ℕ} (g : GL (Fin n) ℤ) (k : ℕ) (hk : 0 < k)
    (hgk : g ^ k = 1) (q : ℕ) (hq : 3 ≤ q)
    (hcong : ∀ i j, (q : ℤ) ∣ (g : Matrix (Fin n) (Fin n) ℤ) i j - (1 : Matrix (Fin n) (Fin n) ℤ) i j) :
    g = 1 := by
  choose C hC using hcong
  have hg : (g : Matrix (Fin n) (Fin n) ℤ) = 1 + (q : ℤ) • Matrix.of C := by
    ext i j
    have := hC i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    linarith
  have key := _root_.GlobalTheory.end_eq_one_of_pow_eq_one_of_congr (Fin n → ℤ)
    (Matrix.toLinAlgEquiv' (g : Matrix (Fin n) (Fin n) ℤ)) k q hk ?_ hq ?_
  · have h1 : (g : Matrix (Fin n) (Fin n) ℤ) = 1 := by
      apply Matrix.toLinAlgEquiv'.injective
      rw [key, map_one]
    exact Units.ext h1
  · rw [← map_pow, ← Units.val_pow_eq_pow_val, hgk, Units.val_one, map_one]
  · intro y
    refine ⟨Matrix.of C *ᵥ y, ?_⟩
    rw [Matrix.toLinAlgEquiv'_apply, hg, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.smul_mulVec, ← Nat.cast_smul_eq_nsmul ℤ]

open Matrix in
/- English proof (translation)
Establish `hcard` using `Matrix.card_GL_field (𝔽 := ZMod q) n`. Rewrite `hcard` using `[ZMod.card]`. Rewrite using `[← hcard]`. Use `Subgroup.card_dvd_of_injective ((Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod q))).comp G.subtype) ?_` and prove the remaining obligations. Rewrite using `[← MonoidHom.ker_eq_bot_iff, eq_bot_iff]`.

Introduce `g hg`. Rewrite `hg` using `[MonoidHom.mem_ker]`. Rewrite using `[Subgroup.mem_bot]`. Take `⟨k, hk, hgk⟩` from `(isOfFinOrder_of_finite g).exists_pow_eq_one`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `eq_one_of_pow_eq_one_of_congr_one_mod (g : GL (Fin n) ℤ) k hk ?_ q hq ?_` and prove the remaining obligations. Rewrite using `[← Subgroup.coe_pow, hgk]`. Both sides reduce to the same expression. Introduce `i j`. Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`.

Use `congrArg (fun h : GL (Fin n) (ZMod q) => (h : Matrix _ _ (ZMod q)) i j) hg` as an intermediate fact. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify `this` using `[sub_eq_zero, Matrix.one_apply, Matrix.GeneralLinearGroup.map]`. Simplify `this` using `[sub_eq_zero, Matrix.one_apply, hij, Matrix.GeneralLinearGroup.map]`.
-/
private theorem card_finite_subgroup_dvd_prod_pow_sub_pow {n : ℕ} (G : Subgroup (GL (Fin n) ℤ)) [Finite G]
    (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q) :
    Nat.card G ∣ ∏ i : Fin n, (q ^ n - q ^ (i : ℕ)) := by
  have hcard := Matrix.card_GL_field (𝔽 := ZMod q) n
  rw [ZMod.card] at hcard
  rw [← hcard]
  refine Subgroup.card_dvd_of_injective
    ((Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod q))).comp G.subtype) ?_
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  rw [Subgroup.mem_bot]
  obtain ⟨k, hk, hgk⟩ := (isOfFinOrder_of_finite g).exists_pow_eq_one
  apply Subtype.ext
  refine eq_one_of_pow_eq_one_of_congr_one_mod (g : GL (Fin n) ℤ) k hk ?_ q hq ?_
  · rw [← Subgroup.coe_pow, hgk]; rfl
  · intro i j
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have := congrArg (fun h : GL (Fin n) (ZMod q) => (h : Matrix _ _ (ZMod q)) i j) hg
    by_cases hij : i = j
    · subst hij; simpa [sub_eq_zero, Matrix.one_apply, Matrix.GeneralLinearGroup.map] using this
    · simpa [sub_eq_zero, Matrix.one_apply, hij, Matrix.GeneralLinearGroup.map] using this

open Matrix in

/- English proof (translation)
Introduce `n G hG`. Establish `hB : 8 ^ n * (2 * n).factorial ≠ 0` using `by positivity`. Establish `hG0 : Nat.card G ≠ 0` using `Nat.card_pos.ne'`. Rewrite using `[← Nat.factorization_prime_le_iff_dvd hG0 hB]`. Introduce `p hp`.

Use `haveI := Fact.mk hp`. Rewrite using `[Nat.factorization_def _ hp, Nat.factorization_def _ hp]`. Choose the witnesses or unpack the hypotheses as in `⟨q, hq, hq3, hbound⟩ : ∃ q, q.Prime ∧ 3 ≤ q ∧ padicValNat p (∏ i : Fin n, (q ^ n - q ^ (i : ℕ))) ≤ padicValNat p (8 ^ n * (2 * n).factorial) := by`. Distinguish the cases in `hp2 : p = 2`. Substitute `hp2` using the available equality.

Conclude with `⟨3, Nat.prime_three, le_rfl, padicValNat_two_prod_three_pow_sub_le_eight_pow_factorial n⟩`. Take `⟨q, hq, hpq, hdiv, hval⟩` from `exists_prime_gt_order_padicValNat_pow_sub_one p hp2`. Establish `h2` using `hp.two_le`. Use `⟨q, hq, by omega, ?_⟩` and prove the remaining obligations. Establish `hnd : ¬ p ∣ q` using `fun h => by`.

Use `(Nat.prime_dvd_prime_iff_eq hp hq).mp h` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[padicValNat_prod_pow_sub_pow_eq_padicValNat_factorial p q hq.two_le hnd hdiv hval n]`. Conclude with `padicValNat_factorial_le_padicValNat_eight_pow_mul_factorial p n`. Use `haveI := Fact.mk hq`.

Use `haveI := hG`. Conclude with `(padicValNat_le_padicValNat_of_dvd (prod_pow_sub_pow_pos q n hq.two_le).ne' (card_finite_subgroup_dvd_prod_pow_sub_pow G q hq3)).trans hbound`.
-/
theorem _root_.GlobalTheory.card_finite_subgroup_GL_int_dvd :
    ∀ (n : ℕ) (G : Subgroup (GL (Fin n) ℤ)), Finite G → Nat.card G ∣ 8 ^ n * (2 * n).factorial := by
  intro n G hG
  have hB : 8 ^ n * (2 * n).factorial ≠ 0 := by positivity
  have hG0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  rw [← Nat.factorization_prime_le_iff_dvd hG0 hB]
  intro p hp
  haveI := Fact.mk hp
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
  obtain ⟨q, hq, hq3, hbound⟩ : ∃ q, q.Prime ∧ 3 ≤ q ∧
      padicValNat p (∏ i : Fin n, (q ^ n - q ^ (i : ℕ))) ≤
        padicValNat p (8 ^ n * (2 * n).factorial) := by
    by_cases hp2 : p = 2
    · subst hp2
      exact ⟨3, Nat.prime_three, le_rfl, padicValNat_two_prod_three_pow_sub_le_eight_pow_factorial n⟩
    · obtain ⟨q, hq, hpq, hdiv, hval⟩ := exists_prime_gt_order_padicValNat_pow_sub_one p hp2
      have h2 := hp.two_le
      refine ⟨q, hq, by omega, ?_⟩
      have hnd : ¬ p ∣ q := fun h => by
        have := (Nat.prime_dvd_prime_iff_eq hp hq).mp h
        omega
      rw [padicValNat_prod_pow_sub_pow_eq_padicValNat_factorial p q hq.two_le hnd hdiv hval n]
      exact padicValNat_factorial_le_padicValNat_eight_pow_mul_factorial p n
  haveI := Fact.mk hq
  haveI := hG
  exact (padicValNat_le_padicValNat_of_dvd (prod_pow_sub_pow_pos q n hq.two_le).ne'
    (card_finite_subgroup_dvd_prod_pow_sub_pow G q hq3)).trans hbound

end GlobalTheory
