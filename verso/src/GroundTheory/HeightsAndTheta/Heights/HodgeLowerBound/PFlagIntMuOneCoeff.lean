import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFlagIntMuOneDet
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

namespace FlagIntMuOne

open MvPolynomial Finset

noncomputable def rhoPerm (N : ℕ) (σ : Equiv.Perm (Fin N)) : Unit × Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => N - 1 - (σ p.2 : ℕ)

/- English proof (translation)
Unfold `flagInt antisym`. Rewrite using `[coeff_sum, ← (Equiv.funUnique Unit (Equiv.Perm (Fin N))).symm.sum_comp]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_smul, smul_eq_mul]`. Use `congr 1`.

Simplify using `[weylSign]`. Establish `hinj : Function.Injective (weylAct Unit N ((Equiv.funUnique Unit _).symm σ))`. Introduce and unpack `⟨⟨⟩, a⟩ ⟨⟨⟩, b⟩ h`. Simplify `h` using `[weylAct]`. Establish `hρ : rhoMono Unit N = Finsupp.mapDomain (weylAct Unit N ((Equiv.funUnique Unit _).symm σ)) (rhoPerm N σ)`.

Use extensionality with `⟨⟨⟩, k⟩`. Take `⟨i, rfl⟩` from `σ.surjective k`. Establish `: ((), σ i) = weylAct Unit N ((Equiv.funUnique Unit _).symm σ) ((), i)` using `rfl`. Rewrite using `[this, Finsupp.mapDomain_apply hinj]`. Simplify using `[rhoMono, rhoPerm, weylAct]`.

Rewrite using `[hρ, coeff_rename_mapDomain _ hinj]`.
-/
theorem flagInt_unit_eq (N : ℕ) (P : RootPoly Unit N) :
    flagInt Unit N P =
      ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤ) : ℚ) * coeff (rhoPerm N σ) P := by
  unfold flagInt antisym
  rw [coeff_sum, ← (Equiv.funUnique Unit (Equiv.Perm (Fin N))).symm.sum_comp]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [coeff_smul, smul_eq_mul]
  congr 1
  · simp [weylSign]
  · have hinj : Function.Injective (weylAct Unit N ((Equiv.funUnique Unit _).symm σ)) := by
      rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, b⟩ h
      simpa [weylAct] using h
    have hρ : rhoMono Unit N =
        Finsupp.mapDomain (weylAct Unit N ((Equiv.funUnique Unit _).symm σ)) (rhoPerm N σ) := by
      ext ⟨⟨⟩, k⟩
      obtain ⟨i, rfl⟩ := σ.surjective k
      have : ((), σ i) = weylAct Unit N ((Equiv.funUnique Unit _).symm σ) ((), i) := rfl
      rw [this, Finsupp.mapDomain_apply hinj]
      simp [rhoMono, rhoPerm, weylAct]
    rw [hρ, coeff_rename_mapDomain _ hinj]

/- English proof (translation)
Unfold `muPoly`. Rewrite using `[Finset.sum_filter]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp_all`.
-/
theorem muPoly_eq_sum (N j : ℕ) :
    muPoly Unit N j = ∑ p, (if (p.2 : ℕ) < j then (0 : ℚ) else 1) • X p := by
  unfold muPoly
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs <;> simp_all

/- English proof (translation)
Use `set d := rhoPerm (j + m) σ with hd`. Use `set s := rhoBlock Unit (j + m) j with hs`. Establish `hdv : ∀ i : Fin (j + m), d ((), i) = j + m - 1 - (σ i : ℕ)` using `fun i => rfl`. Establish `hsv : ∀ i : Fin (j + m), s ((), i) = if (i : ℕ) < j then j - 1 - (i : ℕ) else j + m - 1 - (i : ℕ)` using `fun i => rfl`. Establish `hpt : ∀ i : Fin (j + m), flagMat j m i (σ i) = if s ((), i) ≤ d ((), i) ∧ ((i : ℕ) < j → d ((), i) - s ((), i) = 0) then (((d ((), i) - s ((), i)).factorial : ℚ))⁻¹ else 0`.

Introduce `i`. Establish `hi` using `i.isLt`. Establish `hσ` using `(σ i).isLt`. Simplify using `only [flagMat, Matrix.of_apply, hdv, hsv]`. Distinguish the cases in `hij : (i : ℕ) < j`.

Simplify using `only [hij, if_true, forall_const]`. Distinguish the cases in `h : (σ i : ℕ) = m + i`. Rewrite using `[if_pos h, if_pos (by omega), show j + m - 1 - (σ i : ℕ) - (j - 1 - i) = 0 by omega]`. Simplify using the standard rewrite rules. Rewrite using `[if_neg h, if_neg (by omega)]`.

Simplify using `only [hij, if_false, false_implies, and_true]`. Distinguish the cases in `h : (σ i : ℕ) ≤ i`. Rewrite using `[if_pos h, if_pos (by omega), show j + m - 1 - (σ i : ℕ) - (j + m - 1 - i) = i - σ i by omega]`. Rewrite using `[if_neg h, if_neg (by omega)]`. Rewrite using `[coeff_mul_monomial', muPoly_eq_sum, coeff_linearCombination_X_pow_of_fintype]`.

Distinguish the cases in `hall : ∀ i : Fin (j + m), s ((), i) ≤ d ((), i) ∧ ((i : ℕ) < j → d ((), i) - s ((), i) = 0)`. Establish `hle : s ≤ d`. Introduce `p`. Take `⟨⟨⟩, i⟩` from `p`. Conclude with `(hall i).1`.

Establish `hev : ∀ i : Fin (j + m), ((d - s) ((), i) : ℤ) = (i : ℤ) - (σ i : ℤ) + (if (i : ℕ) < j then (m : ℤ) else 0)`. Introduce `i`. Establish `hi` using `i.isLt`. Establish `hσ` using `(σ i).isLt`. Use `hall i` as an intermediate fact.

Rewrite `*` using `[Finsupp.tsub_apply, hdv, hsv]`. Apply the tactic sequence `split_ifs at * with hij <;> omega`. Establish `hsumN : ∑ i : Fin (j + m), (d - s) ((), i) = j * m`. Establish `hz : ((∑ i : Fin (j + m), (d - s) ((), i) : ℕ) : ℤ) = ((j * m : ℕ) : ℤ)`. Establish `hσsum : ∑ i : Fin (j + m), ((σ i : ℕ) : ℤ) = ∑ i : Fin (j + m), ((i : ℕ) : ℤ)` using `Equiv.sum_comp σ (fun i => ((i : ℕ) : ℤ))`.

Rewrite using `[Nat.cast_sum, Finset.sum_congr rfl (fun i _ => hev i), Finset.sum_add_distrib, Finset.sum_sub_distrib, hσsum, sub_self, zero_add, Fin.sum_univ_add]`. Simplify using the standard rewrite rules. Conclude with `hz` after adjusting the coercions. Establish `hsum : (d - s).sum (fun _ k => k) = j * m`. Rewrite using `[Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_prod_type]`.

Simplify using `using hsumN`. Establish `hprod : ((d - s).prod fun r k => (if (r.2 : ℕ) < j then (0 : ℚ) else 1) ^ k) = 1`. Rewrite using `[Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]`. Use `Finset.prod_eq_one fun p _ => ?_` and prove the remaining obligations. Take `⟨⟨⟩, i⟩` from `p`.

Distinguish the cases in `hij : (i : ℕ) < j`. Simplify using `only [Finsupp.tsub_apply]`. Rewrite using `[(hall i).2 hij, pow_zero]`. Simplify using `[hij]`. Establish `hmult : (((d - s).multinomial : ℕ) : ℚ) = ((j * m).factorial : ℚ) / ∏ i : Fin (j + m), (((d - s) ((), i)).factorial : ℚ)`.

Establish `h` using `Nat.multinomial_spec (Finset.univ : Finset (Unit × Fin (j + m))) (DFunLike.coe (d - s))`. Rewrite `h` using `[← Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)]`. Rewrite `h` using `[Fintype.sum_prod_type, Fintype.prod_prod_type]`. Simplify using `only [Finset.univ_unique, Finset.sum_singleton, Finset.prod_singleton, PUnit.default_eq_unit] at h`. Rewrite `h` using `[hsumN]`.

Establish `hP : (∏ i : Fin (j + m), (((d - s) ((), i)).factorial : ℚ)) ≠ 0` using `prod_ne_zero_iff.mpr fun i _ => by positivity`. Rewrite using `[eq_div_iff hP, mul_comm]`. Conclude with `h` after adjusting the coercions. Rewrite using `[if_pos hle, if_pos hsum, hprod, mul_one, mul_one, hmult, div_eq_mul_inv, ← prod_inv_distrib]`. Use `congr 1`.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hpt, if_pos (hall i), Finsupp.tsub_apply]`. Use `push Not at hall`. Take `⟨i, hi⟩` from `hall`. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hpt, if_neg (by tauto)]), mul_zero]`.

Use `split_ifs with hle hsum`. Rewrite using `[Finsupp.prod_fintype _ _ (fun _ => pow_zero _), mul_one]`. Use `mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ ((), i)) ?_)` and prove the remaining obligations. Take `⟨hij, hne⟩` from `hi (hle ((), i))`. Simplify using `[hij, Finsupp.tsub_apply, hne]`.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem coeff_muPow_rhoBlock (j m : ℕ) (σ : Equiv.Perm (Fin (j + m))) :
    coeff (rhoPerm (j + m) σ)
        (muPoly Unit (j + m) j ^ (j * m) * monomial (rhoBlock Unit (j + m) j) 1) =
      ((j * m).factorial : ℚ) * ∏ i, flagMat j m i (σ i) := by
  set d := rhoPerm (j + m) σ with hd
  set s := rhoBlock Unit (j + m) j with hs
  have hdv : ∀ i : Fin (j + m), d ((), i) = j + m - 1 - (σ i : ℕ) := fun i => rfl
  have hsv : ∀ i : Fin (j + m), s ((), i) = if (i : ℕ) < j then j - 1 - (i : ℕ) else j + m - 1 - (i : ℕ) :=
    fun i => rfl

  have hpt : ∀ i : Fin (j + m), flagMat j m i (σ i) =
      if s ((), i) ≤ d ((), i) ∧ ((i : ℕ) < j → d ((), i) - s ((), i) = 0)
      then (((d ((), i) - s ((), i)).factorial : ℚ))⁻¹ else 0 := by
    intro i
    have hi := i.isLt
    have hσ := (σ i).isLt
    simp only [flagMat, Matrix.of_apply, hdv, hsv]
    by_cases hij : (i : ℕ) < j
    · simp only [hij, if_true, forall_const]
      by_cases h : (σ i : ℕ) = m + i
      · rw [if_pos h, if_pos (by omega), show j + m - 1 - (σ i : ℕ) - (j - 1 - i) = 0 by omega]
        simp
      · rw [if_neg h, if_neg (by omega)]
    · simp only [hij, if_false, false_implies, and_true]
      by_cases h : (σ i : ℕ) ≤ i
      · rw [if_pos h, if_pos (by omega), show j + m - 1 - (σ i : ℕ) - (j + m - 1 - i) = i - σ i by omega]
      · rw [if_neg h, if_neg (by omega)]
  rw [coeff_mul_monomial', muPoly_eq_sum, coeff_linearCombination_X_pow_of_fintype]
  by_cases hall : ∀ i : Fin (j + m), s ((), i) ≤ d ((), i) ∧ ((i : ℕ) < j → d ((), i) - s ((), i) = 0)
  · have hle : s ≤ d := by
      intro p
      obtain ⟨⟨⟩, i⟩ := p
      exact (hall i).1
    have hev : ∀ i : Fin (j + m), ((d - s) ((), i) : ℤ) = (i : ℤ) - (σ i : ℤ) + (if (i : ℕ) < j then (m : ℤ) else 0) := by
      intro i
      have hi := i.isLt
      have hσ := (σ i).isLt
      have := hall i
      rw [Finsupp.tsub_apply, hdv, hsv] at *
      split_ifs at * with hij <;> omega
    have hsumN : ∑ i : Fin (j + m), (d - s) ((), i) = j * m := by
      have hz : ((∑ i : Fin (j + m), (d - s) ((), i) : ℕ) : ℤ) = ((j * m : ℕ) : ℤ) := by
        have hσsum : ∑ i : Fin (j + m), ((σ i : ℕ) : ℤ) = ∑ i : Fin (j + m), ((i : ℕ) : ℤ) :=
          Equiv.sum_comp σ (fun i => ((i : ℕ) : ℤ))
        rw [Nat.cast_sum, Finset.sum_congr rfl (fun i _ => hev i), Finset.sum_add_distrib, Finset.sum_sub_distrib,
          hσsum, sub_self, zero_add, Fin.sum_univ_add]
        simp
      exact_mod_cast hz
    have hsum : (d - s).sum (fun _ k => k) = j * m := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_prod_type]
      simpa using hsumN
    have hprod : ((d - s).prod fun r k => (if (r.2 : ℕ) < j then (0 : ℚ) else 1) ^ k) = 1 := by
      rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
      refine Finset.prod_eq_one fun p _ => ?_
      obtain ⟨⟨⟩, i⟩ := p
      by_cases hij : (i : ℕ) < j
      · simp only [Finsupp.tsub_apply]
        rw [(hall i).2 hij, pow_zero]
      · simp [hij]
    have hmult : (((d - s).multinomial : ℕ) : ℚ) =
        ((j * m).factorial : ℚ) / ∏ i : Fin (j + m), (((d - s) ((), i)).factorial : ℚ) := by
      have h := Nat.multinomial_spec (Finset.univ : Finset (Unit × Fin (j + m))) (DFunLike.coe (d - s))
      rw [← Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)] at h
      rw [Fintype.sum_prod_type, Fintype.prod_prod_type] at h
      simp only [Finset.univ_unique, Finset.sum_singleton, Finset.prod_singleton, PUnit.default_eq_unit] at h
      rw [hsumN] at h
      have hP : (∏ i : Fin (j + m), (((d - s) ((), i)).factorial : ℚ)) ≠ 0 :=
        prod_ne_zero_iff.mpr fun i _ => by positivity
      rw [eq_div_iff hP, mul_comm]
      exact_mod_cast h
    rw [if_pos hle, if_pos hsum, hprod, mul_one, mul_one, hmult, div_eq_mul_inv, ← prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hpt, if_pos (hall i), Finsupp.tsub_apply]
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hpt, if_neg (by tauto)]), mul_zero]
    split_ifs with hle hsum
    · rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), mul_one]
      refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ ((), i)) ?_)
      obtain ⟨hij, hne⟩ := hi (hle ((), i))
      simp [hij, Finsupp.tsub_apply, hne]
    · simp
    · simp

end FlagIntMuOne

end GroundTheory.Heights₂.Heights.LowerBoundFree
