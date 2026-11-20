import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesReductionModPrimeRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionCommutesFormalGroupLawCoboundariesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFormalGroupCoboundaryHomogeneousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricCocycleAdditiveEqCoboundaryAddStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LazardOneVariableExistsWittLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffPowerSeriesEvalTwoGroupsSinglePairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveTwoCocycleCoeffRelationsOnePairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryOneAdditiveFormalGroupLawXPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffCoboundaryOneAdditiveEqZeroOfDegreeStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option maxHeartbeats 800000

namespace GlobalTheory.LazardHomog

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use extensionality with `α`. Rewrite using `[coeff_lift]`. Simplify using `only [addLaw, map_add, coeff_X]`. Establish `hne : (Finsupp.single (Sum.inl i) 1 : Fin d ⊕ Fin d →₀ ℕ) ≠ Finsupp.single (Sum.inr i) 1`.

Rewrite using `[Ne, Finsupp.single_left_inj one_ne_zero]`. Simplify using the standard rewrite rules. Distinguish the cases in `h1 : α = Finsupp.single (Sum.inl i) 1`. Simplify using `[h1, hne]`. Distinguish the cases in `h2 : α = Finsupp.single (Sum.inr i) 1`.

Simplify using `[h2, hne.symm]`. Simplify using `[h1, h2]`.
-/
theorem lift_addLaw (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (d : ℕ) :
    (fun i => Katz.lift p (addLaw k d i)) = addLaw (Fr p k) d := by
  funext i
  ext α
  rw [coeff_lift]
  simp only [addLaw, map_add, coeff_X]
  have hne : (Finsupp.single (Sum.inl i) 1 : Fin d ⊕ Fin d →₀ ℕ) ≠ Finsupp.single (Sum.inr i) 1 := by
    rw [Ne, Finsupp.single_left_inj one_ne_zero]; simp
  by_cases h1 : α = Finsupp.single (Sum.inl i) 1
  · simp [h1, hne]
  · by_cases h2 : α = Finsupp.single (Sum.inr i) 1
    · simp [h2, hne.symm]
    · simp [h1, h2]

/- English proof (translation)
Introduce `p _ k _ _ _ d N c hN hc hhom`. Establish `hconst : ∀ (R : Type) [CommRing R] (i : Fin d), constantCoeff (addLaw R d i) = 0`. Introduce `R _ i`. Simplify using `[addLaw]`. Establish `hc0 : constantCoeff c = 0`.

Rewrite using `[← coeff_zero_eq_constantCoeff_apply]`. Conclude with `hhom 0 (by simp; omega)`. Take `⟨b, hb⟩` from `GlobalTheory.T.symmetricCocycle_additive_eq_coboundary_add k d c hc hc0`. Use `set cm : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k := fun m => at2 c (Pi.single m (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) k)) (Pi.single m (X (Sum.inr m))) with hcm`. Use `set bN := homogeneousComponent N b with hbN`.

Establish `hbNc : ∀ α, coeff α bN = if α.degree = N then coeff α b else 0` using `fun α => coeff_homogeneousComponent N α b`. Establish `hdec : c = cob1 (addLaw k d) bN + ∑ m, cm m`. Use extensionality with `γ`. Distinguish the cases in `hγ : γ.degree = N`. Establish `e1 : coeff γ (cob1 (addLaw k d) b) = coeff γ (cob1 (addLaw k d) bN)`.

Use `formalCoboundary_add (hconst k) bN (b - bN)` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Rewrite using `[this, map_add, GlobalTheory.T.coeff_coboundaryOne_additive_eq_zero_of_degree k d N (b - bN) (fun α hα => by`. Rewrite using `[map_sub, hbNc, if_pos hα, sub_self]) γ hγ, add_zero]`. Use `conv_lhs => rw [hb]`.

Rewrite using `[map_add, map_add, e1]`. Rewrite using `[hhom γ hγ, map_add, map_sum, (GlobalTheory.T.additive_formal_group_coboundary_homogeneous k d N).1 bN (fun α hα => by`. Rewrite using `[hbNc, if_neg hα]) γ hγ, zero_add]`. Use `(Finset.sum_eq_zero fun m _ => ?_).symm` and prove the remaining obligations. Simplify using `only [cm]`.

Rewrite using `[GlobalTheory.T.coeff_powerSeriesEvalTwoGroups_single_pair]`. Apply the tactic sequence `split_ifs <;> simp [hhom γ hγ]`. Use `set a : Fin d → ℕ → k := fun m n => coeff (Finsupp.single (Sum.inl m) n + Finsupp.single (Sum.inr m) (N - n)) c with ha`. Establish `hsym : ∀ m n, n ≤ N → a m n = a m (N - n)`. Introduce `m n hn`.

Simplify using `only [ha]`. Use `conv_lhs => rw [← hc.2]`. Rewrite using `[(GlobalTheory.T.additive_formal_group_coboundary_homogeneous k d N).2.2.1, Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.mapDomain_single, Nat.sub_sub_self hn, add_comm]`. Both sides reduce to the same expression. Establish `hrel : ∀ m i j l, 0 < i → 0 < j → 0 < l → i + j + l = N → a m (i + j) * ((i + j).choose i : k) = a m i * ((j + l).choose j : k)`.

Introduce `m i j l hi hj hl hs`. Simplify using `only [ha]`. Establish `e1 : N - (i + j) = l` using `by omega`. Establish `e2 : N - i = j + l` using `by omega`. Rewrite using `[e1, e2]`.

Conclude with `(GlobalTheory.T.additiveTwoCocycle_coeff_relations_one_pair k d c hc.1 m).2 i j l hi hj hl`. Establish `ht` using `fun m => GlobalTheory.T.lazard_one_variable_exists_witt_lift p k N (a m) hN (hsym m) (hrel m)`. Use `choose t ht using ht`. Establish `hzero : ∀ m, coeff (Finsupp.single (Sum.inl m) N) c = 0` using `fun m => (GlobalTheory.T.additiveTwoCocycle_coeff_relations_one_pair k d c hc.1 m).1 N (by omega)`. Establish `hzero' : ∀ m, coeff (Finsupp.single (Sum.inr m) N) c = 0`.

Introduce `m`. Use `hsym m 0 (Nat.zero_le _)` as an intermediate fact. Simplify using `only [ha, Finsupp.single_zero, zero_add, Nat.sub_zero, Nat.sub_self, add_zero] at this`. Rewrite using `[this, hzero]`. Establish `hconstFr` using `hconst (Fr p k)`.

Establish `redSum : ∀ (s : Finset (Fin d)) (F : Fin d → MvPowerSeries (Fin d ⊕ Fin d) (Fr p k)) (G : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), (∀ m ∈ s, Red p (F m) (G m)) → Red p (∑ m ∈ s, F m) (∑ m ∈ s, G m)`. Introduce `s F G hFG`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro α; exact ⟨0, by simp⟩`. Consider the case `insert x s hx ih`.

Rewrite using `[Finset.sum_insert hx, Finset.sum_insert hx]`. Conclude with `((GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k _).2.2.2.1 _ _ _ _ (hFG x (Finset.mem_insert_self _ _)) (ih fun m hm => hFG m (Finset.mem_insert_of_mem hm))).1`. Establish `cob0 : cob1 (addLaw (Fr p k) d) 0 = 0`. Use `formalCoboundary_smul hconstFr (0 : Fr p k) 0` as an intermediate fact. Simplify using `using this`.

Establish `cobSum : ∀ (s : Finset (Fin d)) (F : Fin d → MvPowerSeries (Fin d) (Fr p k)), cob1 (addLaw (Fr p k) d) (∑ m ∈ s, F m) = ∑ m ∈ s, cob1 (addLaw (Fr p k) d) (F m)`. Introduce `s F`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using cob0`. Consider the case `insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, formalCoboundary_add hconstFr, ih]`.

Establish `redm : ∀ m, Red p (t m • cob1 (addLaw (Fr p k) d) (X m ^ N)) (cm m)`. Introduce `m α`. Rewrite using `[GlobalTheory.T.cob1_addLaw_X_pow_eq_sum_choose (Fr p k) d N m (by omega)]`. Simplify using `only [cm]`. Rewrite using `[GlobalTheory.T.coeff_powerSeriesEvalTwoGroups_single_pair, map_smul, map_sum]`.

Simplify using `only [coeff_monomial, smul_eq_mul]`. Use `set i := α (Sum.inl m) with hi`. Use `set j := α (Sum.inr m) with hj`. Establish `key : ∀ i', α = Finsupp.single (Sum.inl m) i' + Finsupp.single (Sum.inr m) (N - i') → i = i' ∧ j = N - i'`. Introduce `i' h`.

Prove the components needed by the constructor for the conclusion. Rewrite using `[hi, h]`. Simplify using the standard rewrite rules. Rewrite using `[hj, h]`. Simplify using the standard rewrite rules.

Distinguish the cases in `hs : α = Finsupp.single (Sum.inl m) i + Finsupp.single (Sum.inr m) j`. Rewrite using `[if_pos hs]`. Distinguish the cases in `hin : 0 < i ∧ i < N ∧ j = N - i`. Take `⟨w, hw1, hw2⟩` from `ht m i hin.1 hin.2.1`. Use `⟨w, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Finset.sum_eq_single_of_mem i (Finset.mem_Ioo.2 ⟨hin.1, hin.2.1⟩)]`. Rewrite using `[if_pos (hs.trans (by rw [hin.2.2])), hw1]`. Introduce `i' _ hne`. Rewrite using `[if_neg]`. Introduce `h`.

Conclude with `hne (key i' h).1.symm`. Rewrite using `[hw2]`. Simplify using `only [ha]`. Rewrite using `[← hin.2.2, ← hs]`. Use `⟨0, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Finset.sum_eq_zero, mul_zero, map_zero]`. Introduce `i' hi'`. Rewrite using `[if_neg]`. Introduce `h`. Take `⟨e1, e2⟩` from `key i' h`.

Rewrite `hi'` using `[Finset.mem_Ioo]`. Conclude with `hin ⟨e1 ▸ hi'.1, e1 ▸ hi'.2, e1 ▸ e2⟩`. Rewrite using `[map_zero]`. Distinguish the cases in `hd : i + j = N`. Establish `: i = 0 ∨ i = N` using `by omega`.

Break down `this with h0 | h0` into its components or cases. Establish `: α = Finsupp.single (Sum.inr m) N`. Rewrite using `[hs, h0, Finsupp.single_zero, zero_add]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[this, hzero']`. Establish `: α = Finsupp.single (Sum.inl m) N`. Rewrite using `[hs, h0, (by omega : j = 0), Finsupp.single_zero, add_zero]`. Rewrite using `[this, hzero]`. Use `(hhom α ?_).symm` and prove the remaining obligations.

Rewrite using `[hs, map_add, Finsupp.degree_single, Finsupp.degree_single]`. Conclude with `hd`. Rewrite using `[if_neg hs]`. Use `⟨0, ?_, by simp⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_zero, mul_zero, map_zero]`.

Introduce `i' _`. Rewrite using `[if_neg]`. Introduce `h`. Apply `hs` to reduce the goal to its premises. Take `⟨e1, e2⟩` from `key i' h`.

Rewrite using `[e1, e2]`. Conclude with `h`. Use `⟨Katz.lift p bN + ∑ m, t m • (X m ^ N : MvPowerSeries (Fin d) (Fr p k)), ?_, ?_⟩` and prove the remaining obligations. Introduce `α hα`. Rewrite using `[map_add, map_sum, coeff_lift, hbNc, if_neg hα, WittVector.teichmuller_zero, map_zero, zero_add]`.

Use `Finset.sum_eq_zero fun m _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, coeff_X_pow, if_neg, smul_zero]`. Introduce `h`. Apply `hα` to reduce the goal to its premises. Rewrite using `[h, Finsupp.degree_single]`.

Establish `h1 : Red p (cob1 (addLaw (Fr p k) d) (Katz.lift p bN)) (cob1 (addLaw k d) bN)`. Rewrite using `[← lift_addLaw p k d]`. Conclude with `((GlobalTheory.T.reduction_commutes_formalGroupLawCoboundaries p k d (addLaw k d) (hconst k)).2.1 _ _ ((GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k _).2.2.1 bN)).1`. Establish `h2 : Red p (∑ m, cob1 (addLaw (Fr p k) d) (t m • (X m ^ N : MvPowerSeries (Fin d) (Fr p k)))) (∑ m, cm m)`. Use `redSum _ _ _ fun m _ => ?_` and prove the remaining obligations.

Rewrite using `[formalCoboundary_smul hconstFr]`. Conclude with `redm m`. Use `((GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k _).2.2.2.1 _ _ _ _ h1 h2).1` as an intermediate fact. Rewrite using `[formalCoboundary_add hconstFr, cobSum]`. Rewrite `this` using `[← hdec]`. Then use the resulting hypothesis.
-/
theorem homogCoc_red_cob : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d N : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) k), 2 ≤ N → IsCoc (addLaw k d) c → (∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree ≠ N → coeff γ c = 0) → ∃ h : MvPowerSeries (Fin d) (Fr p k), (∀ α : Fin d →₀ ℕ, α.degree ≠ N → coeff α h = 0) ∧ Red p (cob1 (addLaw (Fr p k) d) h) c := by
  intro p _ k _ _ _ d N c hN hc hhom
  have hconst : ∀ (R : Type) [CommRing R] (i : Fin d), constantCoeff (addLaw R d i) = 0 := by
    intro R _ i; simp [addLaw]
  have hc0 : constantCoeff c = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    exact hhom 0 (by simp; omega)
  obtain ⟨b, hb⟩ := GlobalTheory.T.symmetricCocycle_additive_eq_coboundary_add k d c hc hc0
  set cm : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k := fun m => at2 c (Pi.single m (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) k)) (Pi.single m (X (Sum.inr m))) with hcm
  set bN := homogeneousComponent N b with hbN
  have hbNc : ∀ α, coeff α bN = if α.degree = N then coeff α b else 0 := fun α =>
    coeff_homogeneousComponent N α b

  have hdec : c = cob1 (addLaw k d) bN + ∑ m, cm m := by
    ext γ
    by_cases hγ : γ.degree = N
    · have e1 : coeff γ (cob1 (addLaw k d) b) = coeff γ (cob1 (addLaw k d) bN) := by
        have := formalCoboundary_add (hconst k) bN (b - bN)
        rw [add_sub_cancel] at this
        rw [this, map_add, GlobalTheory.T.coeff_coboundaryOne_additive_eq_zero_of_degree k d N (b - bN) (fun α hα => by
          rw [map_sub, hbNc, if_pos hα, sub_self]) γ hγ, add_zero]
      conv_lhs => rw [hb]
      rw [map_add, map_add, e1]
    · rw [hhom γ hγ, map_add, map_sum, (GlobalTheory.T.additive_formal_group_coboundary_homogeneous k d N).1 bN (fun α hα => by
        rw [hbNc, if_neg hα]) γ hγ, zero_add]
      refine (Finset.sum_eq_zero fun m _ => ?_).symm
      simp only [cm]
      rw [GlobalTheory.T.coeff_powerSeriesEvalTwoGroups_single_pair]
      split_ifs <;> simp [hhom γ hγ]

  set a : Fin d → ℕ → k := fun m n => coeff (Finsupp.single (Sum.inl m) n + Finsupp.single (Sum.inr m) (N - n)) c with ha
  have hsym : ∀ m n, n ≤ N → a m n = a m (N - n) := by
    intro m n hn
    simp only [ha]
    conv_lhs => rw [← hc.2]
    rw [(GlobalTheory.T.additive_formal_group_coboundary_homogeneous k d N).2.2.1, Finsupp.mapDomain_add, Finsupp.mapDomain_single,
      Finsupp.mapDomain_single, Nat.sub_sub_self hn, add_comm]
    rfl
  have hrel : ∀ m i j l, 0 < i → 0 < j → 0 < l → i + j + l = N → a m (i + j) * ((i + j).choose i : k) = a m i * ((j + l).choose j : k) := by
    intro m i j l hi hj hl hs
    simp only [ha]
    have e1 : N - (i + j) = l := by omega
    have e2 : N - i = j + l := by omega
    rw [e1, e2]
    exact (GlobalTheory.T.additiveTwoCocycle_coeff_relations_one_pair k d c hc.1 m).2 i j l hi hj hl
  have ht := fun m => GlobalTheory.T.lazard_one_variable_exists_witt_lift p k N (a m) hN (hsym m) (hrel m)
  choose t ht using ht
  have hzero : ∀ m, coeff (Finsupp.single (Sum.inl m) N) c = 0 :=
    fun m => (GlobalTheory.T.additiveTwoCocycle_coeff_relations_one_pair k d c hc.1 m).1 N (by omega)
  have hzero' : ∀ m, coeff (Finsupp.single (Sum.inr m) N) c = 0 := by
    intro m
    have := hsym m 0 (Nat.zero_le _)
    simp only [ha, Finsupp.single_zero, zero_add, Nat.sub_zero, Nat.sub_self, add_zero] at this
    rw [this, hzero]
  have hconstFr := hconst (Fr p k)
  have redSum : ∀ (s : Finset (Fin d)) (F : Fin d → MvPowerSeries (Fin d ⊕ Fin d) (Fr p k))
      (G : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), (∀ m ∈ s, Red p (F m) (G m)) →
      Red p (∑ m ∈ s, F m) (∑ m ∈ s, G m) := by
    intro s F G hFG
    induction s using Finset.induction_on with
    | empty => intro α; exact ⟨0, by simp⟩
    | insert x s hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx]
      exact ((GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k _).2.2.2.1 _ _ _ _ (hFG x (Finset.mem_insert_self _ _))
        (ih fun m hm => hFG m (Finset.mem_insert_of_mem hm))).1
  have cob0 : cob1 (addLaw (Fr p k) d) 0 = 0 := by
    have := formalCoboundary_smul hconstFr (0 : Fr p k) 0
    simpa using this
  have cobSum : ∀ (s : Finset (Fin d)) (F : Fin d → MvPowerSeries (Fin d) (Fr p k)),
      cob1 (addLaw (Fr p k) d) (∑ m ∈ s, F m) = ∑ m ∈ s, cob1 (addLaw (Fr p k) d) (F m) := by
    intro s F
    induction s using Finset.induction_on with
    | empty => simpa using cob0
    | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, formalCoboundary_add hconstFr, ih]
  have redm : ∀ m, Red p (t m • cob1 (addLaw (Fr p k) d) (X m ^ N)) (cm m) := by
    intro m α
    rw [GlobalTheory.T.cob1_addLaw_X_pow_eq_sum_choose (Fr p k) d N m (by omega)]
    simp only [cm]
    rw [GlobalTheory.T.coeff_powerSeriesEvalTwoGroups_single_pair, map_smul, map_sum]
    simp only [coeff_monomial, smul_eq_mul]
    set i := α (Sum.inl m) with hi
    set j := α (Sum.inr m) with hj
    have key : ∀ i', α = Finsupp.single (Sum.inl m) i' + Finsupp.single (Sum.inr m) (N - i') →
        i = i' ∧ j = N - i' := by
      intro i' h
      constructor
      · rw [hi, h]; simp
      · rw [hj, h]; simp
    by_cases hs : α = Finsupp.single (Sum.inl m) i + Finsupp.single (Sum.inr m) j
    · rw [if_pos hs]
      by_cases hin : 0 < i ∧ i < N ∧ j = N - i
      · obtain ⟨w, hw1, hw2⟩ := ht m i hin.1 hin.2.1
        refine ⟨w, ?_, ?_⟩
        · rw [Finset.sum_eq_single_of_mem i (Finset.mem_Ioo.2 ⟨hin.1, hin.2.1⟩)]
          · rw [if_pos (hs.trans (by rw [hin.2.2])), hw1]
          · intro i' _ hne; rw [if_neg]; intro h; exact hne (key i' h).1.symm
        · rw [hw2]; simp only [ha]; rw [← hin.2.2, ← hs]
      · refine ⟨0, ?_, ?_⟩
        · rw [Finset.sum_eq_zero, mul_zero, map_zero]
          intro i' hi'; rw [if_neg]; intro h
          obtain ⟨e1, e2⟩ := key i' h
          rw [Finset.mem_Ioo] at hi'
          exact hin ⟨e1 ▸ hi'.1, e1 ▸ hi'.2, e1 ▸ e2⟩
        · rw [map_zero]
          by_cases hd : i + j = N
          · have : i = 0 ∨ i = N := by omega
            rcases this with h0 | h0
            · have : α = Finsupp.single (Sum.inr m) N := by
                rw [hs, h0, Finsupp.single_zero, zero_add]; congr 1; omega
              rw [this, hzero']
            · have : α = Finsupp.single (Sum.inl m) N := by
                rw [hs, h0, (by omega : j = 0), Finsupp.single_zero, add_zero]
              rw [this, hzero]
          · refine (hhom α ?_).symm
            rw [hs, map_add, Finsupp.degree_single, Finsupp.degree_single]; exact hd
    · rw [if_neg hs]
      refine ⟨0, ?_, by simp⟩
      rw [Finset.sum_eq_zero, mul_zero, map_zero]
      intro i' _; rw [if_neg]; intro h
      apply hs; obtain ⟨e1, e2⟩ := key i' h; rw [e1, e2]; exact h
  refine ⟨Katz.lift p bN + ∑ m, t m • (X m ^ N : MvPowerSeries (Fin d) (Fr p k)), ?_, ?_⟩
  · intro α hα
    rw [map_add, map_sum, coeff_lift, hbNc, if_neg hα, WittVector.teichmuller_zero, map_zero,
      zero_add]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [map_smul, coeff_X_pow, if_neg, smul_zero]
    intro h; apply hα; rw [h, Finsupp.degree_single]
  · have h1 : Red p (cob1 (addLaw (Fr p k) d) (Katz.lift p bN)) (cob1 (addLaw k d) bN) := by
      rw [← lift_addLaw p k d]
      exact ((GlobalTheory.T.reduction_commutes_formalGroupLawCoboundaries p k d (addLaw k d) (hconst k)).2.1 _ _
        ((GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k _).2.2.1 bN)).1
    have h2 : Red p (∑ m, cob1 (addLaw (Fr p k) d) (t m • (X m ^ N : MvPowerSeries (Fin d) (Fr p k))))
        (∑ m, cm m) := by
      refine redSum _ _ _ fun m _ => ?_
      rw [formalCoboundary_smul hconstFr]; exact redm m
    have := ((GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k _).2.2.2.1 _ _ _ _ h1 h2).1
    rw [formalCoboundary_add hconstFr, cobSum]
    rwa [← hdec] at this

end GlobalTheory.LazardHomog
