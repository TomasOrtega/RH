import Formalism.WindowSums.Statement

namespace Formalism.WindowSums

open Finset

section ValProdAux

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Simplify using `[hx]`. Establish `h1 : (-1 : ℤ_[ℓ]) ≠ 0` using `neg_ne_zero.mpr one_ne_zero`. Establish `hm1 : (-1 : ℤ_[ℓ]).valuation = 0`. Establish `h` using `PadicInt.valuation_mul h1 h1`.

Rewrite `h` using `[neg_one_mul, neg_neg, PadicInt.valuation_one]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[← neg_one_mul x, PadicInt.valuation_mul h1 hx, hm1, zero_add]`.
-/
lemma vp_val_neg (x : ℤ_[ℓ]) : (-x).valuation = x.valuation := by
  by_cases hx : x = 0
  · simp [hx]
  have h1 : (-1 : ℤ_[ℓ]) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hm1 : (-1 : ℤ_[ℓ]).valuation = 0 := by
    have h := PadicInt.valuation_mul h1 h1
    rw [neg_one_mul, neg_neg, PadicInt.valuation_one] at h
    omega
  rw [← neg_one_mul x, PadicInt.valuation_mul h1 hx, hm1, zero_add]

/- English proof (translation)
Use `revert h`. Use `Finset.induction_on S ?_ ?_` and prove the remaining obligations. Introduce `_`. Simplify using `[PadicInt.valuation_one]`. Introduce `a S ha ih h`.

Establish `hS : ∀ i ∈ S, f i ≠ 0` using `fun i hi => h i (Finset.mem_insert_of_mem hi)`. Establish `ha0 : f a ≠ 0` using `h a (Finset.mem_insert_self a S)`. Take `⟨h1, h2⟩` from `ih hS`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha]`. Conclude with `⟨mul_ne_zero ha0 h1, by rw [PadicInt.valuation_mul ha0 h1, h2]⟩`.
-/
lemma vp_val_prod {ι : Type} [DecidableEq ι] (S : Finset ι) (f : ι → ℤ_[ℓ])
    (h : ∀ i ∈ S, f i ≠ 0) :
    (∏ i ∈ S, f i) ≠ 0 ∧ (∏ i ∈ S, f i).valuation = ∑ i ∈ S, (f i).valuation := by
  revert h
  refine Finset.induction_on S ?_ ?_
  · intro _
    simp [PadicInt.valuation_one]
  · intro a S ha ih h
    have hS : ∀ i ∈ S, f i ≠ 0 := fun i hi => h i (Finset.mem_insert_of_mem hi)
    have ha0 : f a ≠ 0 := h a (Finset.mem_insert_self a S)
    obtain ⟨h1, h2⟩ := ih hS
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact ⟨mul_ne_zero ha0 h1, by rw [PadicInt.valuation_mul ha0 h1, h2]⟩

/- English proof (translation)
Establish `hℓ0 : (ℓ : ℤ_[ℓ]) ≠ 0`. Introduce `h`. Establish `h'` using `PadicInt.valuation_p (p := ℓ)`. Rewrite `h'` using `[h, PadicInt.valuation_zero]`. Conclude with `absurd h' (by norm_num)`.

Proceed by induction on `n with`. Consider the case `zero => simp [PadicInt.valuation_one]`. Consider the case `succ n ih`. Use `⟨pow_ne_zero _ hℓ0, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ, PadicInt.valuation_mul ih.1 hℓ0, ih.2, PadicInt.valuation_p]`.
-/
private theorem prime_pow_ne_zero_and_valuation_eq (n : ℕ) :
    (ℓ : ℤ_[ℓ]) ^ n ≠ 0 ∧ ((ℓ : ℤ_[ℓ]) ^ n).valuation = n := by
  have hℓ0 : (ℓ : ℤ_[ℓ]) ≠ 0 := by
    intro h
    have h' := PadicInt.valuation_p (p := ℓ)
    rw [h, PadicInt.valuation_zero] at h'
    exact absurd h' (by norm_num)
  induction n with
  | zero => simp [PadicInt.valuation_one]
  | succ n ih =>
    refine ⟨pow_ne_zero _ hℓ0, ?_⟩
    rw [pow_succ, PadicInt.valuation_mul ih.1 hℓ0, ih.2, PadicInt.valuation_p]

/- English proof (translation)
Proceed by induction on `M with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[Finset.sum_Icc_succ_top (by omega), ih, Nat.factorial_succ, padicValNat.mul (by omega : n + 1 ≠ 0) (Nat.factorial_ne_zero n)]`. Use linear arithmetic over natural numbers and integers.
-/
lemma vp_sum_padicValNat (M : ℕ) :
    ∑ i ∈ Finset.Icc 1 M, padicValNat ℓ i = padicValNat ℓ M.factorial := by
  induction M with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.factorial_succ,
      padicValNat.mul (by omega : n + 1 ≠ 0) (Nat.factorial_ne_zero n)]
    omega

end ValProdAux

/- English proof (translation)
Unfold `ValProd`. Unfold `ZpowVal at hZ`. Introduce `ℓ hp u s hs h2 hv`. Establish `key : ∀ j : ℤ, j ≠ 0 → (1 - ((u ^ j : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) ≠ 0 ∧ (1 - ((u ^ j : ℤ_[ℓ]ˣ) : ℤ_[ℓ])).valuation = s + padicValInt ℓ j`. Introduce `j hj`.

Take `⟨h1, h2'⟩` from `hZ ℓ u s hs h2 hv j hj`. Rewrite using `[← neg_sub, vp_val_neg, h2']`. Conclude with `⟨neg_ne_zero.mpr h1, rfl⟩`. Use `⟨fun M => ?_, fun J hJ => ?_⟩` and prove the remaining obligations. Establish `hf : ∀ i ∈ Finset.Icc 1 M, (1 - (u : ℤ_[ℓ]) ^ i) ≠ 0 ∧ (1 - (u : ℤ_[ℓ]) ^ i).valuation = s + padicValNat ℓ i`.

Introduce `i hi`. Establish `hi0 : (i : ℤ) ≠ 0`. Use `(Finset.mem_Icc.mp hi).1` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hk` using `key i hi0`.

Establish `e : ((u ^ (i : ℤ) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = (u : ℤ_[ℓ]) ^ i`. Rewrite using `[zpow_natCast, Units.val_pow_eq_pow_val]`. Establish `hv' : padicValInt ℓ (i : ℤ) = padicValNat ℓ i`. Simplify using `[padicValInt]`. Rewrite `hk` using `[e, hv']`.

Conclude with `hk`. Take `⟨h1, h2'⟩` from `vp_val_prod (Finset.Icc 1 M) (fun i => 1 - (u : ℤ_[ℓ]) ^ i) (fun i hi => (hf i hi).1)`. Use `⟨h1, h2'.trans ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_congr rfl (fun i hi => (hf i hi).2), Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, smul_eq_mul, vp_sum_padicValNat, Nat.add_sub_cancel]`. Establish `hf : ∀ j ∈ J, (1 - ((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) ≠ 0 ∧ (1 - ((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])).valuation = s + padicValInt ℓ j`.

Introduce `j hj`. Establish `hj0 : -j ≠ 0` using `neg_ne_zero.mpr (fun h => hJ (by rw [← h]; exact hj))`. Take `⟨h1, h2'⟩` from `key (-j) hj0`. Use `⟨h1, h2'.trans ?_⟩` and prove the remaining obligations. Simplify using `[padicValInt]`.

Take `⟨h1, h2'⟩` from `vp_val_prod J (fun j => 1 - ((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) (fun j hj => (hf j hj).1)`. Use `⟨h1, h2'.trans ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_congr rfl (fun j hj => (hf j hj).2), Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]`.
-/
theorem valProd_of (hZ : ZpowVal) : ValProd := by
  unfold ValProd
  unfold ZpowVal at hZ
  intro ℓ hp u s hs h2 hv
  have key : ∀ j : ℤ, j ≠ 0 →
      (1 - ((u ^ j : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) ≠ 0 ∧
      (1 - ((u ^ j : ℤ_[ℓ]ˣ) : ℤ_[ℓ])).valuation = s + padicValInt ℓ j := by
    intro j hj
    obtain ⟨h1, h2'⟩ := hZ ℓ u s hs h2 hv j hj
    rw [← neg_sub, vp_val_neg, h2']
    exact ⟨neg_ne_zero.mpr h1, rfl⟩
  refine ⟨fun M => ?_, fun J hJ => ?_⟩
  · have hf : ∀ i ∈ Finset.Icc 1 M, (1 - (u : ℤ_[ℓ]) ^ i) ≠ 0 ∧
        (1 - (u : ℤ_[ℓ]) ^ i).valuation = s + padicValNat ℓ i := by
      intro i hi
      have hi0 : (i : ℤ) ≠ 0 := by
        have := (Finset.mem_Icc.mp hi).1
        omega
      have hk := key i hi0
      have e : ((u ^ (i : ℤ) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = (u : ℤ_[ℓ]) ^ i := by
        rw [zpow_natCast, Units.val_pow_eq_pow_val]
      have hv' : padicValInt ℓ (i : ℤ) = padicValNat ℓ i := by
        simp [padicValInt]
      rw [e, hv'] at hk
      exact hk
    obtain ⟨h1, h2'⟩ := vp_val_prod (Finset.Icc 1 M)
      (fun i => 1 - (u : ℤ_[ℓ]) ^ i) (fun i hi => (hf i hi).1)
    refine ⟨h1, h2'.trans ?_⟩
    rw [Finset.sum_congr rfl (fun i hi => (hf i hi).2), Finset.sum_add_distrib,
      Finset.sum_const, Nat.card_Icc, smul_eq_mul,
      vp_sum_padicValNat, Nat.add_sub_cancel]
  · have hf : ∀ j ∈ J, (1 - ((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) ≠ 0 ∧
        (1 - ((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])).valuation = s + padicValInt ℓ j := by
      intro j hj
      have hj0 : -j ≠ 0 := neg_ne_zero.mpr (fun h => hJ (by rw [← h]; exact hj))
      obtain ⟨h1, h2'⟩ := key (-j) hj0
      refine ⟨h1, h2'.trans ?_⟩
      simp [padicValInt]
    obtain ⟨h1, h2'⟩ := vp_val_prod J
      (fun j => 1 - ((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) (fun j hj => (hf j hj).1)
    refine ⟨h1, h2'.trans ?_⟩
    rw [Finset.sum_congr rfl (fun j hj => (hf j hj).2), Finset.sum_add_distrib,
      Finset.sum_const, smul_eq_mul]

/- English proof (translation)
Unfold `KillerVal`. Unfold `ZpowVal at hZ`. Introduce `ℓ hp h2 c hc e JJ`. Establish `h22 : ℓ = 2 → 2 ≤ 1` using `fun h => absurd h h2`. Establish `hf : ∀ i ∈ JJ.erase 0, (1 - ((c ^ (i * (ℓ : ℤ) ^ e) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) ≠ 0 ∧ (1 - ((c ^ (i * (ℓ : ℤ) ^ e) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])).valuation = 1 + e + padicValInt ℓ i`.

Introduce `i hi`. Establish `hi0 : i ≠ 0` using `Finset.ne_of_mem_erase hi`. Establish `hp0 : ((ℓ : ℤ) ^ e) ≠ 0` using `pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)`. Establish `hj : i * (ℓ : ℤ) ^ e ≠ 0` using `mul_ne_zero hi0 hp0`. Take `⟨h1, h2'⟩` from `hZ ℓ c 1 le_rfl h22 hc _ hj`.

Rewrite using `[← neg_sub, vp_val_neg, h2', padicValInt.mul hi0 hp0]`. Use `⟨neg_ne_zero.mpr h1, ?_⟩` and prove the remaining obligations. Establish `hpe : padicValInt ℓ ((ℓ : ℤ) ^ e) = e`. Simplify using `[padicValInt, Int.natAbs_pow]`. Use linear arithmetic over natural numbers and integers.

Take `⟨h1, h2'⟩` from `vp_val_prod (JJ.erase 0) (fun i => 1 - ((c ^ (i * (ℓ : ℤ) ^ e) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) (fun i hi => (hf i hi).1)`. Take `⟨hP1, hP2⟩` from `prime_pow_ne_zero_and_valuation_eq (ℓ := ℓ) e`. Establish `hev : (PP ℓ c e JJ).eval 1 = (∏ i ∈ JJ.erase 0, (1 - ((c ^ (i * (ℓ : ℤ) ^ e) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]))) * (ℓ : ℤ_[ℓ]) ^ e`. Simplify using `[PP, Polynomial.eval_prod, Polynomial.eval_finsetSum]`. Rewrite using `[hev]`.

Use `⟨mul_ne_zero h1 hP1, ?_⟩` and prove the remaining obligations. Rewrite using `[PadicInt.valuation_mul h1 hP1, hP2, h2', Finset.sum_congr rfl (fun i hi => (hf i hi).2)]`.
-/
theorem killerVal_of (hZ : ZpowVal) : KillerVal := by
  unfold KillerVal
  unfold ZpowVal at hZ
  intro ℓ hp h2 c hc e JJ
  have h22 : ℓ = 2 → 2 ≤ 1 := fun h => absurd h h2
  have hf : ∀ i ∈ JJ.erase 0,
      (1 - ((c ^ (i * (ℓ : ℤ) ^ e) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) ≠ 0 ∧
      (1 - ((c ^ (i * (ℓ : ℤ) ^ e) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])).valuation = 1 + e + padicValInt ℓ i := by
    intro i hi
    have hi0 : i ≠ 0 := Finset.ne_of_mem_erase hi
    have hp0 : ((ℓ : ℤ) ^ e) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
    have hj : i * (ℓ : ℤ) ^ e ≠ 0 := mul_ne_zero hi0 hp0
    obtain ⟨h1, h2'⟩ := hZ ℓ c 1 le_rfl h22 hc _ hj
    rw [← neg_sub, vp_val_neg, h2', padicValInt.mul hi0 hp0]
    refine ⟨neg_ne_zero.mpr h1, ?_⟩
    have hpe : padicValInt ℓ ((ℓ : ℤ) ^ e) = e := by
      simp [padicValInt, Int.natAbs_pow]
    omega
  obtain ⟨h1, h2'⟩ := vp_val_prod (JJ.erase 0)
    (fun i => 1 - ((c ^ (i * (ℓ : ℤ) ^ e) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) (fun i hi => (hf i hi).1)
  obtain ⟨hP1, hP2⟩ := prime_pow_ne_zero_and_valuation_eq (ℓ := ℓ) e
  have hev : (PP ℓ c e JJ).eval 1 =
      (∏ i ∈ JJ.erase 0, (1 - ((c ^ (i * (ℓ : ℤ) ^ e) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]))) * (ℓ : ℤ_[ℓ]) ^ e := by
    simp [PP, Polynomial.eval_prod, Polynomial.eval_finsetSum]
  rw [hev]
  refine ⟨mul_ne_zero h1 hP1, ?_⟩
  rw [PadicInt.valuation_mul h1 hP1, hP2, h2', Finset.sum_congr rfl (fun i hi => (hf i hi).2)]

end Formalism.WindowSums
