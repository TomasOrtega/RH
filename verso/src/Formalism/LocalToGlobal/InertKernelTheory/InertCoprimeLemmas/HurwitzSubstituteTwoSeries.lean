import Mathlib
import Formalism.FormalGroupLog.FormalGroupLogProofs.ChainRule
import Formalism.LocalToGlobal.InertKernelTheory.StatementZ
import Formalism.LocalToGlobal.InertKernelTheory.Adm11OfBeProp
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EnInParamKProd
import Formalism.FormalGroupWitt.FormalGroupWittProofs.WittTeichmullerRoot
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.CoeffPowEqZeroOfCc
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.DegreeLeOfMemAntidiagonal

noncomputable section

namespace Formalism.L2.KerInert.Jet

open MvPowerSeries Finset

section Gen

variable {K : Type*} [Field K] {σ : Type*}

def fc (n : σ →₀ ℕ) : K := ∏ x ∈ n.support, ((n x).factorial : K)

def Hur (R : Subring K) (f : MvPowerSeries σ K) : Prop := ∀ n, fc n * coeff n f ∈ R

/- English proof (translation)
Unfold `fc`. Use `Finset.prod_subset h (fun x _ hx => ?_)` and prove the remaining obligations. Establish `e : n x = 0` using `by simpa using hx`. Rewrite using `[e, Nat.factorial_zero, Nat.cast_one]`.
-/
theorem fc_of_subset {n : σ →₀ ℕ} {S : Finset σ} (h : n.support ⊆ S) :
    (fc n : K) = ∏ x ∈ S, ((n x).factorial : K) := by
  unfold fc
  refine Finset.prod_subset h (fun x _ hx => ?_)
  have e : n x = 0 := by simpa using hx
  rw [e, Nat.factorial_zero, Nat.cast_one]

/- English proof (translation)
Unfold `fc`. Simplify using the standard rewrite rules.
-/
theorem fc_zero : (fc (0 : σ →₀ ℕ) : K) = 1 := by
  unfold fc
  simp

/- English proof (translation)
Establish `hT1 : (n + Finsupp.single i 1).support ⊆ insert i n.support`. Introduce `k hk`. Distinguish the cases in `hki : k = i`. Rewrite using `[hki]`. Conclude with `Finset.mem_insert_self i _`.

Rewrite using `[Finset.mem_insert] right`. Rewrite `hk`, the goal using `[Finsupp.mem_support_iff]`. Simplify `hk` using `[Finsupp.single_apply, Ne.symm hki]`. Establish `hT0 : n.support ⊆ insert i n.support` using `Finset.subset_insert _ _`. Rewrite using `[fc_of_subset hT1, fc_of_subset hT0, ← Finset.mul_prod_erase (insert i n.support) _ (Finset.mem_insert_self i _), ← Finset.mul_prod_erase (insert i n.support) (fun x => (((n x).factorial : ℕ) : K)) (Finset.mem_insert_self i _)]`.

Establish `e : ∏ x ∈ (insert i n.support).erase i, ((((n + Finsupp.single i 1 : σ →₀ ℕ) x).factorial : ℕ) : K) = ∏ x ∈ (insert i n.support).erase i, (((n x).factorial : ℕ) : K)` using `Finset.prod_congr rfl (fun x hx => by`. Rewrite using `[Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm (Finset.ne_of_mem_erase hx)), add_zero])`. Rewrite using `[e, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fc_add_single [DecidableEq σ] (n : σ →₀ ℕ) (i : σ) :
    (fc (n + Finsupp.single i 1) : K) = ((n i : K) + 1) * fc n := by
  have hT1 : (n + Finsupp.single i 1).support ⊆ insert i n.support := by
    intro k hk
    by_cases hki : k = i
    · rw [hki]; exact Finset.mem_insert_self i _
    · rw [Finset.mem_insert]
      right
      rw [Finsupp.mem_support_iff] at hk ⊢
      simpa [Finsupp.single_apply, Ne.symm hki] using hk
  have hT0 : n.support ⊆ insert i n.support := Finset.subset_insert _ _
  rw [fc_of_subset hT1, fc_of_subset hT0, ← Finset.mul_prod_erase (insert i n.support) _ (Finset.mem_insert_self i _),
    ← Finset.mul_prod_erase (insert i n.support) (fun x => (((n x).factorial : ℕ) : K)) (Finset.mem_insert_self i _)]
  have e : ∏ x ∈ (insert i n.support).erase i, ((((n + Finsupp.single i 1 : σ →₀ ℕ) x).factorial : ℕ) : K) =
      ∏ x ∈ (insert i n.support).erase i, (((n x).factorial : ℕ) : K) :=
    Finset.prod_congr rfl (fun x hx => by
      rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm (Finset.ne_of_mem_erase hx)), add_zero])
  rw [e, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  push_cast
  ring

/- English proof (translation)
Rewrite using `[MvPowerSeries.coeff_pderiv, fc_add_single]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fc_coeff_pderiv [DecidableEq σ] (f : MvPowerSeries σ K) (n : σ →₀ ℕ) (i : σ) :
    fc n * coeff n (pderiv K i f) = fc (n + Finsupp.single i 1) * coeff (n + Finsupp.single i 1) f := by
  rw [MvPowerSeries.coeff_pderiv, fc_add_single]
  ring

variable (R : Subring K)

/- English proof (translation)
Unfold `fc`. Conclude with `prod_mem (fun x _ => natCast_mem R _)`.
-/
theorem fc_mem (n : σ →₀ ℕ) : (fc n : K) ∈ R := by
  unfold fc
  exact prod_mem (fun x _ => natCast_mem R _)

/- English proof (translation)
Establish `e` using `hf 0`. Rewrite `e` using `[fc_zero, one_mul]`. Simplify using `using e`.
-/
theorem hur_cc {f : MvPowerSeries σ K} (hf : Hur R f) : constantCoeff f ∈ R := by
  have e := hf 0
  rw [fc_zero, one_mul] at e
  simpa using e

/- English proof (translation)
Use extensionality with `k`. Distinguish the cases in `hk : i = k`. Substitute `hk` using the available equality. Simplify using `only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_eq_same]`. Use linear arithmetic over natural numbers and integers.

Simplify using `only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply, if_neg hk]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem sub_single_one_add_single_one_of_ne_zero (n : σ →₀ ℕ) (i : σ) (hi : n i ≠ 0) :
    n - Finsupp.single i 1 + Finsupp.single i 1 = n := by
  classical
  ext k
  by_cases hk : i = k
  · subst hk
    simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_eq_same]
    omega
  · simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply, if_neg hk]
    omega

/- English proof (translation)
It suffices to establish `H : ∀ n : σ →₀ ℕ, ∀ f, Q f → fc n * coeff n f ∈ R from fun f hf n => H n f hf`. Introduce `n`. Use the proof step `induction' n using WellFoundedLT.induction with n ih`. Introduce `f hf`. Distinguish the cases in `hn : n = 0`.

Substitute `hn` using the available equality. Rewrite using `[fc_zero, one_mul]`. Simplify using `using h0 f hf`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, n i ≠ 0 := by`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Conclude with `hn (Finsupp.ext hc)`. Establish `hlt : n - Finsupp.single i 1 < n`. Use `lt_of_le_of_ne tsub_le_self (fun heq => ?_)` and prove the remaining obligations. Establish `e` using `congrArg (fun g => g i) heq`.

Simplify using `only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same] at e`. Use linear arithmetic over natural numbers and integers. Take `⟨a, b, ha, hb, hab⟩` from `hd f hf i`. Rewrite using `[← sub_single_one_add_single_one_of_ne_zero n i hi, ← fc_coeff_pderiv, hab, map_add, mul_add]`. Conclude with `R.add_mem (ih _ hlt a ha) (ih _ hlt b hb)`.
-/
private theorem hur_of_closed_under_pderiv [DecidableEq σ] (Q : MvPowerSeries σ K → Prop)
    (h0 : ∀ f, Q f → constantCoeff f ∈ R)
    (hd : ∀ f, Q f → ∀ i, ∃ a b, Q a ∧ Q b ∧ pderiv K i f = a + b) :
    ∀ f, Q f → Hur R f := by
  suffices H : ∀ n : σ →₀ ℕ, ∀ f, Q f → fc n * coeff n f ∈ R from fun f hf n => H n f hf
  intro n
  induction' n using WellFoundedLT.induction with n ih
  intro f hf
  by_cases hn : n = 0
  · subst hn
    rw [fc_zero, one_mul]
    simpa using h0 f hf
  · obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hn (Finsupp.ext hc)
    have hlt : n - Finsupp.single i 1 < n := by
      refine lt_of_le_of_ne tsub_le_self (fun heq => ?_)
      have e := congrArg (fun g => g i) heq
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same] at e
      omega
    obtain ⟨a, b, ha, hb, hab⟩ := hd f hf i
    rw [← sub_single_one_add_single_one_of_ne_zero n i hi, ← fc_coeff_pderiv, hab, map_add, mul_add]
    exact R.add_mem (ih _ hlt a ha) (ih _ hlt b hb)

/- English proof (translation)
Introduce `f hf`. Use `hur_of_closed_under_pderiv R (fun g => g ∈ S ∨ g = 0) ?_ ?_ f (Or.inl hf)` and prove the remaining obligations. Introduce and unpack `g (hg | rfl)`. Conclude with `h0 g hg`. Rewrite using `[map_zero]`.

Conclude with `R.zero_mem`. Introduce and unpack `g (hg | rfl) i`. Conclude with `⟨pderiv K i g, 0, Or.inl (hd g hg i), Or.inr rfl, (add_zero _).symm⟩`. Conclude with `⟨0, 0, Or.inr rfl, Or.inr rfl, by rw [map_zero, add_zero]⟩`.
-/
theorem hur_of_closed [DecidableEq σ] (S : Set (MvPowerSeries σ K))
    (h0 : ∀ f ∈ S, constantCoeff f ∈ R) (hd : ∀ f ∈ S, ∀ i, pderiv K i f ∈ S) :
    ∀ f ∈ S, Hur R f := by
  intro f hf
  refine hur_of_closed_under_pderiv R (fun g => g ∈ S ∨ g = 0) ?_ ?_ f (Or.inl hf)
  · rintro g (hg | rfl)
    · exact h0 g hg
    · rw [map_zero]; exact R.zero_mem
  · rintro g (hg | rfl) i
    · exact ⟨pderiv K i g, 0, Or.inl (hd g hg i), Or.inr rfl, (add_zero _).symm⟩
    · exact ⟨0, 0, Or.inr rfl, Or.inr rfl, by rw [map_zero, add_zero]⟩

/- English proof (translation)
Introduce `n`. Rewrite using `[map_zero, mul_zero]`. Conclude with `R.zero_mem`.
-/
theorem hur_zero : Hur R (0 : MvPowerSeries σ K) := by
  intro n
  rw [map_zero, mul_zero]
  exact R.zero_mem

/- English proof (translation)
Introduce `n`. Rewrite using `[map_add, mul_add]`. Conclude with `R.add_mem (hf n) (hg n)`.
-/
theorem hur_add {f g : MvPowerSeries σ K} (hf : Hur R f) (hg : Hur R g) : Hur R (f + g) := by
  intro n
  rw [map_add, mul_add]
  exact R.add_mem (hf n) (hg n)

/- English proof (translation)
Introduce `n`. Rewrite using `[map_neg, mul_neg]`. Conclude with `R.neg_mem (hf n)`.
-/
theorem hur_neg {f : MvPowerSeries σ K} (hf : Hur R f) : Hur R (-f) := by
  intro n
  rw [map_neg, mul_neg]
  exact R.neg_mem (hf n)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => rw [Finset.sum_empty]`. Conclude with `hur_zero R`. Consider the case `@insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`.

Conclude with `hur_add R (h a (Finset.mem_insert_self a s)) (ih (fun b hb => h b (Finset.mem_insert_of_mem hb)))`.
-/
theorem hur_sum {α : Type*} (s : Finset α) (f : α → MvPowerSeries σ K) (h : ∀ a ∈ s, Hur R (f a)) :
    Hur R (∑ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact hur_zero R
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact hur_add R (h a (Finset.mem_insert_self a s)) (ih (fun b hb => h b (Finset.mem_insert_of_mem hb)))

/- English proof (translation)
Introduce `n` and use `R.mul_mem (fc_mem R n) (hf n)`.
-/
theorem hur_of_int {f : MvPowerSeries σ K} (hf : ∀ n, coeff n f ∈ R) : Hur R f := fun n => R.mul_mem (fc_mem R n) (hf n)

/- English proof (translation)
Apply `hur_of_int` to reduce the goal to its premises. Introduce `n`. Rewrite using `[MvPowerSeries.coeff_C]`. Use `split_ifs`. Conclude with `hr`.

Conclude with `R.zero_mem`.
-/
theorem hur_C {r : K} (hr : r ∈ R) : Hur R (C r : MvPowerSeries σ K) := by
  classical
  apply hur_of_int
  intro n
  rw [MvPowerSeries.coeff_C]
  split_ifs
  · exact hr
  · exact R.zero_mem

/- English proof (translation)
Apply `hur_of_int` to reduce the goal to its premises. Introduce `n`. Rewrite using `[MvPowerSeries.coeff_X]`. Use `split_ifs`. Conclude with `R.one_mem`.

Conclude with `R.zero_mem`.
-/
theorem hur_X [DecidableEq σ] (i : σ) : Hur R (X i : MvPowerSeries σ K) := by
  apply hur_of_int
  intro n
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · exact R.one_mem
  · exact R.zero_mem

/- English proof (translation)
Introduce `n`. Rewrite using `[fc_coeff_pderiv]`. Conclude with `hf _`.
-/
theorem hur_pderiv [DecidableEq σ] {f : MvPowerSeries σ K} (hf : Hur R f) (i : σ) :
    Hur R (pderiv K i f) := by
  intro n
  rw [fc_coeff_pderiv]
  exact hf _

/- English proof (translation)
Introduce `n`. Rewrite using `[MvPowerSeries.coeff_mul, Finset.mul_sum]`. Use `R.sum_mem (fun p hp => ?_)` and prove the remaining obligations. Establish `hp' : p.1 + p.2 = n` using `Finset.HasAntidiagonal.mem_antidiagonal.mp hp`. Establish `h1 : p.1.support ⊆ n.support`.

Introduce `x hx`. Rewrite `hx`, the goal using `[Finsupp.mem_support_iff]`. Rewrite using `[← hp', Finsupp.add_apply]`. Use linear arithmetic over natural numbers and integers. Establish `h2 : p.2.support ⊆ n.support`.

Introduce `x hx`. Rewrite `hx`, the goal using `[Finsupp.mem_support_iff]`. Rewrite using `[← hp', Finsupp.add_apply]`. Use linear arithmetic over natural numbers and integers. Establish `key : (fc n : K) = (∏ x ∈ n.support, (((n x).choose (p.2 x) : ℕ) : K)) * fc p.1 * fc p.2`.

Rewrite using `[fc_of_subset (Finset.Subset.refl _), fc_of_subset h1, fc_of_subset h2, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl (fun x _ => ?_)` and prove the remaining obligations. Rewrite using `[← hp', Finsupp.add_apply]`. Rewrite using `[← Nat.cast_mul, ← Nat.cast_mul, Nat.add_choose_mul_factorial_mul_factorial]`. Rewrite using `[key, show (∏ x ∈ n.support, (((n x).choose (p.2 x) : ℕ) : K)) * fc p.1 * fc p.2 * (coeff p.1 f * coeff p.2 g) = (∏ x ∈ n.support, (((n x).choose (p.2 x) : ℕ) : K)) * ((fc p.1 * coeff p.1 f) * (fc p.2 * coeff p.2 g)) by ring]`.

Conclude with `R.mul_mem (prod_mem (fun x _ => natCast_mem R _)) (R.mul_mem (hf _) (hg _))`.
-/
theorem hur_mul [DecidableEq σ] {f g : MvPowerSeries σ K} (hf : Hur R f) (hg : Hur R g) : Hur R (f * g) := by
  intro n
  rw [MvPowerSeries.coeff_mul, Finset.mul_sum]
  refine R.sum_mem (fun p hp => ?_)
  have hp' : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have h1 : p.1.support ⊆ n.support := by
    intro x hx
    rw [Finsupp.mem_support_iff] at hx ⊢
    rw [← hp', Finsupp.add_apply]
    omega
  have h2 : p.2.support ⊆ n.support := by
    intro x hx
    rw [Finsupp.mem_support_iff] at hx ⊢
    rw [← hp', Finsupp.add_apply]
    omega
  have key : (fc n : K) = (∏ x ∈ n.support, (((n x).choose (p.2 x) : ℕ) : K)) * fc p.1 * fc p.2 := by
    rw [fc_of_subset (Finset.Subset.refl _), fc_of_subset h1, fc_of_subset h2, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun x _ => ?_)
    rw [← hp', Finsupp.add_apply]
    rw [← Nat.cast_mul, ← Nat.cast_mul, Nat.add_choose_mul_factorial_mul_factorial]
  rw [key, show (∏ x ∈ n.support, (((n x).choose (p.2 x) : ℕ) : K)) * fc p.1 * fc p.2 *
      (coeff p.1 f * coeff p.2 g) =
      (∏ x ∈ n.support, (((n x).choose (p.2 x) : ℕ) : K)) * ((fc p.1 * coeff p.1 f) * (fc p.2 * coeff p.2 g)) by ring]
  exact R.mul_mem (prod_mem (fun x _ => natCast_mem R _)) (R.mul_mem (hf _) (hg _))

/- English proof (translation)
Apply `hur_of_int` to reduce the goal to its premises. Introduce `n`. Rewrite using `[MvPowerSeries.coeff_one]`. Use `split_ifs`. Conclude with `R.one_mem`.

Conclude with `R.zero_mem`.
-/
private theorem hur_one : Hur R (1 : MvPowerSeries σ K) := by
  classical
  apply hur_of_int
  intro n
  rw [MvPowerSeries.coeff_one]
  split_ifs
  · exact R.one_mem
  · exact R.zero_mem

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rw [pow_zero]`. Conclude with `hur_one R`. Consider the case `succ k ih => rw [pow_succ]`. Conclude with `hur_mul R ih hf`.
-/
theorem hur_pow [DecidableEq σ] {f : MvPowerSeries σ K} (hf : Hur R f) (k : ℕ) : Hur R (f ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact hur_one R
  | succ k ih => rw [pow_succ]; exact hur_mul R ih hf

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => rw [Finset.prod_empty]`. Conclude with `hur_one R`. Consider the case `@insert a s ha ih`. Rewrite using `[Finset.prod_insert ha]`.

Conclude with `hur_mul R (h a (Finset.mem_insert_self a s)) (ih (fun b hb => h b (Finset.mem_insert_of_mem hb)))`.
-/
theorem hur_prod [DecidableEq σ] {α : Type*} (s : Finset α) (f : α → MvPowerSeries σ K)
    (h : ∀ a ∈ s, Hur R (f a)) : Hur R (∏ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty]; exact hur_one R
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact hur_mul R (h a (Finset.mem_insert_self a s)) (ih (fun b hb => h b (Finset.mem_insert_of_mem hb)))

/- English proof (translation)
Establish `hC : ∀ (c : K) (i : σ), pderiv K i (C c : MvPowerSeries σ K) = 0`. Introduce `c i`. Use extensionality with `n`. Rewrite using `[MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_C, if_neg, zero_mul, map_zero]`. Introduce `h`.

Establish `e` using `congrArg (fun g => g i) h`. Simplify using `at e`. Use `hur_of_closed_under_pderiv R (fun h => ∃ (j : ℕ) (g : MvPowerSeries σ K), Hur R g ∧ h = C ((j.factorial : K))⁻¹ * f ^ j * g) ?_ ?_ _ ⟨k, 1, hur_one R, by rw [mul_one]⟩` and prove the remaining obligations. Introduce and unpack `h ⟨j, g, hg, rfl⟩`. Consider the cases of `j with`.

Consider the case `zero`. Simplify using `only [Nat.factorial_zero, Nat.cast_one, inv_one, map_one, pow_zero, one_mul]`. Conclude with `hur_cc R hg`. Consider the case `succ j`. Rewrite using `[map_mul, map_mul, map_pow, hf0, zero_pow (Nat.succ_ne_zero j), mul_zero, zero_mul]`.

Conclude with `R.zero_mem`. Introduce and unpack `h ⟨j, g, hg, rfl⟩ i`. Consider the cases of `j with`. Consider the case `zero`. Use `⟨C ((Nat.factorial 0 : K))⁻¹ * f ^ 0 * pderiv K i g, 0, ⟨0, _, hur_pderiv R hg i, rfl⟩, ⟨0, 0, hur_zero R, by simp⟩, ?_⟩` and prove the remaining obligations.

Simplify using the standard rewrite rules. Consider the case `succ j`. Use `⟨C ((j.factorial : K))⁻¹ * f ^ j * (pderiv K i f * g), C (((j + 1).factorial : K))⁻¹ * f ^ (j + 1) * pderiv K i g, ⟨j, _, hur_mul R (hur_pderiv R hf i) hg, rfl⟩, ⟨j + 1, _, hur_pderiv R hg i, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `hc : C (((j + 1).factorial : K))⁻¹ * (((j + 1 : ℕ) : MvPowerSeries σ K)) = C ((j.factorial : K))⁻¹`. Rewrite using `[show (((j + 1 : ℕ) : MvPowerSeries σ K)) = C ((j + 1 : ℕ) : K) from (map_natCast _ _).symm, ← map_mul]`.

Use `congr 1`. Rewrite using `[Nat.factorial_succ, Nat.cast_mul]`. Establish `h1 : ((j + 1 : ℕ) : K) ≠ 0` using `Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j)`. Establish `h2 : ((j.factorial : ℕ) : K) ≠ 0` using `Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[Derivation.leibniz, Derivation.leibniz, Derivation.leibniz_pow, hC, smul_zero, add_zero]`. Simplify using `only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]`. Rewrite using `[← hc]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hur_gamma [DecidableEq σ] [CharZero K] {f : MvPowerSeries σ K} (hf : Hur R f)
    (hf0 : constantCoeff f = 0) (k : ℕ) : Hur R (C ((k.factorial : K))⁻¹ * f ^ k) := by
  have hC : ∀ (c : K) (i : σ), pderiv K i (C c : MvPowerSeries σ K) = 0 := by
    intro c i
    ext n
    rw [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_C, if_neg, zero_mul, map_zero]
    intro h
    have e := congrArg (fun g => g i) h
    simp at e
  refine hur_of_closed_under_pderiv R (fun h => ∃ (j : ℕ) (g : MvPowerSeries σ K), Hur R g ∧ h = C ((j.factorial : K))⁻¹ * f ^ j * g)
    ?_ ?_ _ ⟨k, 1, hur_one R, by rw [mul_one]⟩
  · rintro h ⟨j, g, hg, rfl⟩
    cases j with
    | zero =>
      simp only [Nat.factorial_zero, Nat.cast_one, inv_one, map_one, pow_zero, one_mul]
      exact hur_cc R hg
    | succ j =>
      rw [map_mul, map_mul, map_pow, hf0, zero_pow (Nat.succ_ne_zero j), mul_zero, zero_mul]
      exact R.zero_mem
  · rintro h ⟨j, g, hg, rfl⟩ i
    cases j with
    | zero =>
      refine ⟨C ((Nat.factorial 0 : K))⁻¹ * f ^ 0 * pderiv K i g, 0, ⟨0, _, hur_pderiv R hg i, rfl⟩,
        ⟨0, 0, hur_zero R, by simp⟩, ?_⟩
      simp
    | succ j =>
      refine ⟨C ((j.factorial : K))⁻¹ * f ^ j * (pderiv K i f * g),
        C (((j + 1).factorial : K))⁻¹ * f ^ (j + 1) * pderiv K i g,
        ⟨j, _, hur_mul R (hur_pderiv R hf i) hg, rfl⟩, ⟨j + 1, _, hur_pderiv R hg i, rfl⟩, ?_⟩
      have hc : C (((j + 1).factorial : K))⁻¹ * (((j + 1 : ℕ) : MvPowerSeries σ K)) = C ((j.factorial : K))⁻¹ := by
        rw [show (((j + 1 : ℕ) : MvPowerSeries σ K)) = C ((j + 1 : ℕ) : K) from (map_natCast _ _).symm, ← map_mul]
        congr 1
        rw [Nat.factorial_succ, Nat.cast_mul]
        have h1 : ((j + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j)
        have h2 : ((j.factorial : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
        field_simp
      rw [Derivation.leibniz, Derivation.leibniz, Derivation.leibniz_pow, hC, smul_zero, add_zero]
      simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
      rw [← hc]
      ring

/- English proof (translation)
Establish `hs : HasSubst a` using `hasSubst_of_constantCoeff_zero ha`. Rewrite using `[constantCoeff_subst hs, finsum_eq_single _ 0]`. Simplify using `[coeff_zero_eq_constantCoeff_apply]`. Introduce `d hd`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs'⟩ : ∃ s, d s ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hd (Finsupp.ext h)`. Rewrite using `[map_finsuppProd, Finsupp.prod, Finset.prod_eq_zero (i := s) (Finsupp.mem_support_iff.mpr hs')]`. Simplify using the standard rewrite rules.

Rewrite using `[map_pow, ha, zero_pow hs']`.
-/
theorem cc_subst {τ : Type*} [Finite σ] {a : σ → MvPowerSeries τ K} (ha : ∀ j, constantCoeff (a j) = 0)
    (g : MvPowerSeries σ K) : constantCoeff (subst a g) = constantCoeff g := by
  classical
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  rw [constantCoeff_subst hs, finsum_eq_single _ 0]
  · simp [coeff_zero_eq_constantCoeff_apply]
  · intro d hd
    obtain ⟨s, hs'⟩ : ∃ s, d s ≠ 0 := by
      by_contra h
      push Not at h
      exact hd (Finsupp.ext h)
    rw [map_finsuppProd, Finsupp.prod, Finset.prod_eq_zero (i := s) (Finsupp.mem_support_iff.mpr hs')]
    · simp
    · rw [map_pow, ha, zero_pow hs']

/- English proof (translation)
Set `S : AddSubgroup (MvPowerSeries τ K)` to `AddSubgroup.closure {h | ∃ g b, Hur R g ∧ Hur R b ∧ h = subst a g * b}`. Establish `h0 : ∀ h ∈ S, constantCoeff h ∈ R`. Introduce `h hh`. Proceed by induction on `hh using AddSubgroup.closure_induction with`. Consider the case `mem x hx`.

Take `⟨g, b, hg, hb, rfl⟩` from `hx`. Rewrite using `[map_mul, cc_subst ha0]`. Conclude with `R.mul_mem (hur_cc R hg) (hur_cc R hb)`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`.

Conclude with `R.add_mem hx hy`. Consider the case `neg x _ hx => rw [map_neg]`. Conclude with `R.neg_mem hx`. Establish `hd : ∀ h ∈ S, ∀ i, pderiv K i h ∈ S`. Introduce `h hh i`.

Proceed by induction on `hh using AddSubgroup.closure_induction with`. Consider the case `mem x hx`. Take `⟨g, b, hg, hb, rfl⟩` from `hx`. Establish `e : pderiv K i (subst a g * b) = subst a g * pderiv K i b + ∑ j, subst a (pderiv K j g) * (pderiv K i (a j) * b)`. Rewrite using `[Derivation.leibniz, smul_eq_mul, smul_eq_mul, Formalism.G.LogCR.pderiv_subst ha0, Finset.mul_sum]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `S.add_mem (AddSubgroup.subset_closure ⟨g, _, hg, hur_pderiv R hb i, rfl⟩) (S.sum_mem fun j _ => ?_)` and prove the remaining obligations.

Conclude with `AddSubgroup.subset_closure ⟨_, _, hur_pderiv R hg j, hur_mul R (hur_pderiv R (ha j) i) hb, rfl⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `S.zero_mem`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `S.add_mem hx hy`.

Consider the case `neg x _ hx => rw [map_neg]`. Conclude with `S.neg_mem hx`. Establish `hmem : subst a g * 1 ∈ S` using `AddSubgroup.subset_closure ⟨g, 1, hg, by rw [← map_one (C (σ := τ) (R := K))]; exact hur_C R R.one_mem, rfl⟩`. Establish `key` using `hur_of_closed R (S : Set (MvPowerSeries τ K)) h0 hd`. Use `key _ hmem` as an intermediate fact.

Simplify using `using this`.
-/
theorem hur_subst {τ : Type*} [DecidableEq σ] [DecidableEq τ] [Fintype σ] [Finite τ]
    {a : σ → MvPowerSeries τ K} (ha0 : ∀ j, constantCoeff (a j) = 0) (ha : ∀ j, Hur R (a j))
    {g : MvPowerSeries σ K} (hg : Hur R g) : Hur R (subst a g) := by
  let S : AddSubgroup (MvPowerSeries τ K) :=
    AddSubgroup.closure {h | ∃ g b, Hur R g ∧ Hur R b ∧ h = subst a g * b}
  have h0 : ∀ h ∈ S, constantCoeff h ∈ R := by
    intro h hh
    induction hh using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨g, b, hg, hb, rfl⟩ := hx
      rw [map_mul, cc_subst ha0]
      exact R.mul_mem (hur_cc R hg) (hur_cc R hb)
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact R.add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact R.neg_mem hx
  have hd : ∀ h ∈ S, ∀ i, pderiv K i h ∈ S := by
    intro h hh i
    induction hh using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨g, b, hg, hb, rfl⟩ := hx
      have e : pderiv K i (subst a g * b) = subst a g * pderiv K i b +
          ∑ j, subst a (pderiv K j g) * (pderiv K i (a j) * b) := by
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, Formalism.G.LogCR.pderiv_subst ha0, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [e]
      refine S.add_mem (AddSubgroup.subset_closure ⟨g, _, hg, hur_pderiv R hb i, rfl⟩) (S.sum_mem fun j _ => ?_)
      exact AddSubgroup.subset_closure ⟨_, _, hur_pderiv R hg j, hur_mul R (hur_pderiv R (ha j) i) hb, rfl⟩
    | zero => rw [map_zero]; exact S.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact S.add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact S.neg_mem hx
  have hmem : subst a g * 1 ∈ S :=
    AddSubgroup.subset_closure ⟨g, 1, hg, by rw [← map_one (C (σ := τ) (R := K))]; exact hur_C R R.one_mem, rfl⟩
  have key := hur_of_closed R (S : Set (MvPowerSeries τ K)) h0 hd
  have := key _ hmem
  simpa using this

/- English proof (translation)
Introduce `n`. Establish `e : (fc n : K') = φ (fc n)`. Unfold `fc`. Simplify using `[map_prod, map_natCast]`. Rewrite using `[MvPowerSeries.coeff_map, e, ← map_mul]`.

Conclude with `hR _ (hf n)`.
-/
theorem hur_map {K' : Type*} [Field K'] (φ : K →+* K') (R' : Subring K') (hR : ∀ x ∈ R, φ x ∈ R')
    {f : MvPowerSeries σ K} (hf : Hur R f) : Hur R' (MvPowerSeries.map φ f) := by
  intro n
  have e : (fc n : K') = φ (fc n) := by
    unfold fc
    simp [map_prod, map_natCast]
  rw [MvPowerSeries.coeff_map, e, ← map_mul]
  exact hR _ (hf n)

end Gen

end Formalism.L2.KerInert.Jet

namespace Formalism.L2.KerInert.Jet

open MvPowerSeries Finset

section E

variable {K : Type*} [Field K] (R : Subring K)

/- English proof (translation)
Introduce `n`. Use the proof step `induction' n using Nat.strong_induction_on with n ih`. Rewrite using `[PowerSeries.coeff_inv, h1, inv_one]`. Use `split_ifs`. Conclude with `R.one_mem`.

Rewrite using `[neg_mul, one_mul]`. Use `R.neg_mem (R.sum_mem (fun x _ => ?_))` and prove the remaining obligations. Use `split_ifs with hx`. Conclude with `R.mul_mem (hφ _) (ih _ hx)`. Conclude with `R.zero_mem`.
-/
theorem int_inv {φ : PowerSeries K} (h1 : PowerSeries.constantCoeff φ = 1)
    (hφ : ∀ n, PowerSeries.coeff n φ ∈ R) : ∀ n, PowerSeries.coeff n φ⁻¹ ∈ R := by
  intro n
  induction' n using Nat.strong_induction_on with n ih
  rw [PowerSeries.coeff_inv, h1, inv_one]
  split_ifs
  · exact R.one_mem
  · rw [neg_mul, one_mul]
    refine R.neg_mem (R.sum_mem (fun x _ => ?_))
    split_ifs with hx
    · exact R.mul_mem (hφ _) (ih _ hx)
    · exact R.zero_mem

/- English proof (translation)
Use `set E : PowerSeries K := L.substInvOfIsUnit hL1 with hEdef`. Establish `hE0 : PowerSeries.constantCoeff E = 0` using `PowerSeries.constantCoeff_substInvOfIsUnit _ _`. Establish `hs : PowerSeries.HasSubst E` using `PowerSeries.HasSubst.of_constantCoeff_zero' hE0`. Establish `hLE : PowerSeries.subst E L = PowerSeries.X` using `PowerSeries.subst_substInvOfIsUnit_right (P := L) (hP := hL0) (hP' := hL1)`. Use `set w : PowerSeries K := (PowerSeries.derivative K L)⁻¹ with hw`.

Establish `hwi : ∀ n, PowerSeries.coeff n w ∈ R` using `int_inv R hLd1 hLd`. Establish `hwL : w * PowerSeries.derivative K L = 1` using `PowerSeries.inv_mul_cancel _ (by rw [hLd1]; exact one_ne_zero)`. Establish `hone : PowerSeries.subst E (1 : PowerSeries K) = 1`. Rewrite using `[← PowerSeries.coe_substAlgHom hs, map_one]`. Establish `hdE : PowerSeries.derivative K E = PowerSeries.subst E w`.

Establish `h1 : PowerSeries.subst E (PowerSeries.derivative K L) * PowerSeries.derivative K E = 1`. Use `congrArg (PowerSeries.derivative K) hLE` as an intermediate fact. Rewrite `this` using `[PowerSeries.derivative_subst hs, PowerSeries.derivative_X]`. Then use the resulting hypothesis. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← PowerSeries.subst_mul hs, hwL, hone, one_mul]`.

Use `_ = PowerSeries.subst E w := by rw [mul_assoc, h1, mul_one]`. Set `S : Set (MvPowerSeries Unit K)` to `{F | ∃ h : PowerSeries K, (∀ n, PowerSeries.coeff n h ∈ R) ∧ F = PowerSeries.subst E h}`. Establish `h0 : ∀ F ∈ S, constantCoeff F ∈ R`. Introduce and unpack `F ⟨h, hh, rfl⟩`. Rewrite using `[PowerSeries.subst_def, cc_subst (fun _ => hE0)]`.

Use `hh 0` as an intermediate fact. Rewrite `this` using `[PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Then use the resulting hypothesis. Establish `hd : ∀ F ∈ S, ∀ i, pderiv K i F ∈ S`. Introduce and unpack `F ⟨h, hh, rfl⟩ i`. Use `⟨PowerSeries.derivative K h * w, fun n => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[PowerSeries.coeff_mul]`. Use `R.sum_mem fun x _ => R.mul_mem ?_ (hwi _)` and prove the remaining obligations. Rewrite using `[PowerSeries.coeff_derivative]`. Conclude with `R.mul_mem (hh _) (R.add_mem (natCast_mem R _) R.one_mem)`. Establish `e : pderiv K i (PowerSeries.subst E h : MvPowerSeries Unit K) = PowerSeries.derivative K (PowerSeries.subst E h)` using `rfl`.

Rewrite using `[e, PowerSeries.derivative_subst hs, hdE, PowerSeries.subst_mul hs]`. Establish `hX : (E : MvPowerSeries Unit K) ∈ S` using `⟨PowerSeries.X, fun n => by`. Rewrite using `[PowerSeries.coeff_X]`. Use `split_ifs`. Conclude with `R.one_mem`.

Conclude with `R.zero_mem, by rw [PowerSeries.subst_X hs]⟩`. Conclude with `hur_of_closed R S h0 hd _ hX`.
-/
theorem hur_substInv {L : PowerSeries K} (hL0 : PowerSeries.constantCoeff L = 0)
    (hL1 : IsUnit (PowerSeries.coeff 1 L))
    (hLd1 : PowerSeries.constantCoeff (PowerSeries.derivative K L) = 1)
    (hLd : ∀ n, PowerSeries.coeff n (PowerSeries.derivative K L) ∈ R) :
    Hur R ((L.substInvOfIsUnit hL1 : PowerSeries K) : MvPowerSeries Unit K) := by
  set E : PowerSeries K := L.substInvOfIsUnit hL1 with hEdef
  have hE0 : PowerSeries.constantCoeff E = 0 := PowerSeries.constantCoeff_substInvOfIsUnit _ _
  have hs : PowerSeries.HasSubst E := PowerSeries.HasSubst.of_constantCoeff_zero' hE0
  have hLE : PowerSeries.subst E L = PowerSeries.X :=
    PowerSeries.subst_substInvOfIsUnit_right (P := L) (hP := hL0) (hP' := hL1)
  set w : PowerSeries K := (PowerSeries.derivative K L)⁻¹ with hw
  have hwi : ∀ n, PowerSeries.coeff n w ∈ R := int_inv R hLd1 hLd
  have hwL : w * PowerSeries.derivative K L = 1 :=
    PowerSeries.inv_mul_cancel _ (by rw [hLd1]; exact one_ne_zero)
  have hone : PowerSeries.subst E (1 : PowerSeries K) = 1 := by
    rw [← PowerSeries.coe_substAlgHom hs, map_one]
  have hdE : PowerSeries.derivative K E = PowerSeries.subst E w := by
    have h1 : PowerSeries.subst E (PowerSeries.derivative K L) * PowerSeries.derivative K E = 1 := by
      have := congrArg (PowerSeries.derivative K) hLE
      rwa [PowerSeries.derivative_subst hs, PowerSeries.derivative_X] at this
    calc PowerSeries.derivative K E
        = (PowerSeries.subst E w * PowerSeries.subst E (PowerSeries.derivative K L)) *
            PowerSeries.derivative K E := by
          rw [← PowerSeries.subst_mul hs, hwL, hone, one_mul]
      _ = PowerSeries.subst E w := by rw [mul_assoc, h1, mul_one]
  let S : Set (MvPowerSeries Unit K) :=
    {F | ∃ h : PowerSeries K, (∀ n, PowerSeries.coeff n h ∈ R) ∧ F = PowerSeries.subst E h}
  have h0 : ∀ F ∈ S, constantCoeff F ∈ R := by
    rintro F ⟨h, hh, rfl⟩
    rw [PowerSeries.subst_def, cc_subst (fun _ => hE0)]
    have := hh 0
    rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply] at this
  have hd : ∀ F ∈ S, ∀ i, pderiv K i F ∈ S := by
    rintro F ⟨h, hh, rfl⟩ i
    refine ⟨PowerSeries.derivative K h * w, fun n => ?_, ?_⟩
    · rw [PowerSeries.coeff_mul]
      refine R.sum_mem fun x _ => R.mul_mem ?_ (hwi _)
      rw [PowerSeries.coeff_derivative]
      exact R.mul_mem (hh _) (R.add_mem (natCast_mem R _) R.one_mem)
    · have e : pderiv K i (PowerSeries.subst E h : MvPowerSeries Unit K) =
          PowerSeries.derivative K (PowerSeries.subst E h) := rfl
      rw [e, PowerSeries.derivative_subst hs, hdE, PowerSeries.subst_mul hs]
  have hX : (E : MvPowerSeries Unit K) ∈ S :=
    ⟨PowerSeries.X, fun n => by
      rw [PowerSeries.coeff_X]
      split_ifs
      · exact R.one_mem
      · exact R.zero_mem, by rw [PowerSeries.subst_X hs]⟩
  exact hur_of_closed R S h0 hd _ hX

end E

end Formalism.L2.KerInert.Jet

namespace Formalism.L2.KerInert.Jet

open MvPowerSeries Finset Formalism.MainNotions.G Formalism.BasicNotions Formalism.MainNotions.FormalGroupSystem

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section Logs

variable (p : ℕ) [Fact p.Prime]

instance charZero_fraction_field_witt : CharZero (K0 p) :=
  haveI : CharZero (WW p) := Formalism.FG.witt_char_zero p
  charZero_of_injective_algebraMap (IsFractionRing.injective (WW p) (K0 p))

def Wr : Subring (K0 p) := (algebraMap (WW p) (K0 p)).range

/- English proof (translation)
The claim follows from `RingHom.mem_range_self _ x`.
-/
theorem mem_Wr (x : WW p) : algebraMap (WW p) (K0 p) x ∈ Wr p := RingHom.mem_range_self _ x

/- English proof (translation)
Unfold `logF`. Rewrite using `[PowerSeries.coeff_mk, Finset.sum_mul]`. Use `(Wr p).sum_mem fun j _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Establish `hp : (p : K0 p) ≠ 0` using `by exact_mod_cast (Fact.out : p.Prime).ne_zero`.

Establish `e : ((n : K0 p) + 1) = (p : K0 p) ^ j * (p : K0 p) ^ j`. Rewrite using `[← pow_add, ← two_mul]`. Conclude with `h` after adjusting the coercions. Rewrite using `[e, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero j hp), one_mul]`. Conclude with `(Wr p).pow_mem (natCast_mem _ p) j`.

Rewrite using `[zero_mul]`. Conclude with `(Wr p).zero_mem`.
-/
theorem logF_deriv_int (n : ℕ) : PowerSeries.coeff (n + 1) (logF p) * ((n : K0 p) + 1) ∈ Wr p := by
  unfold logF
  rw [PowerSeries.coeff_mk, Finset.sum_mul]
  refine (Wr p).sum_mem fun j _ => ?_
  split_ifs with h
  · have hp : (p : K0 p) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have e : ((n : K0 p) + 1) = (p : K0 p) ^ j * (p : K0 p) ^ j := by
      rw [← pow_add, ← two_mul]
      exact_mod_cast h
    rw [e, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero j hp), one_mul]
    exact (Wr p).pow_mem (natCast_mem _ p) j
  · rw [zero_mul]
    exact (Wr p).zero_mem

variable (K1 : Type) [Field K1] [Algebra (K0 p) K1] (R1 : Subring K1)
  (hW : ∀ x : WW p, algebraMap (K0 p) K1 (algebraMap (WW p) (K0 p) x) ∈ R1)
include hW

/- English proof (translation)
Take `⟨y, rfl⟩` from `hx`. Conclude with `hW y`.
-/
theorem Wr_to (x : K0 p) (hx : x ∈ Wr p) : algebraMap (K0 p) K1 x ∈ R1 := by
  obtain ⟨y, rfl⟩ := hx
  exact hW y

/- English proof (translation)
Establish `hd : ∀ n, PowerSeries.coeff n (PowerSeries.derivative K1 (Formalism.MainNotions.FormalGroupSystem.Pf.en_L p K1)) = algebraMap (K0 p) K1 (PowerSeries.coeff (n + 1) (logF p) * ((n : K0 p) + 1))`. Introduce `n`. Rewrite using `[PowerSeries.coeff_derivative, Formalism.MainNotions.FormalGroupSystem.Pf.en_L, PowerSeries.coeff_map, map_mul]`. Simplify using the standard rewrite rules. Use `hur_substInv R1 (Formalism.MainNotions.FormalGroupSystem.Pf.en_L_zero p K1) (Formalism.MainNotions.FormalGroupSystem.Pf.en_L_one p K1) ?_ ?_` and prove the remaining obligations.

Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, hd, zero_add, Formalism.MainNotions.FormalGroupSystem.Pf.en_logF_one]`. Simplify using the standard rewrite rules. Introduce `n`. Rewrite using `[hd]`. Conclude with `Wr_to p K1 R1 hW _ (logF_deriv_int p n)`.
-/
theorem hur_en_E : Hur R1 ((Formalism.MainNotions.FormalGroupSystem.Pf.en_E p K1 : PowerSeries K1) : MvPowerSeries Unit K1) := by
  have hd : ∀ n, PowerSeries.coeff n (PowerSeries.derivative K1 (Formalism.MainNotions.FormalGroupSystem.Pf.en_L p K1)) =
      algebraMap (K0 p) K1 (PowerSeries.coeff (n + 1) (logF p) * ((n : K0 p) + 1)) := by
    intro n
    rw [PowerSeries.coeff_derivative, Formalism.MainNotions.FormalGroupSystem.Pf.en_L, PowerSeries.coeff_map, map_mul]
    simp
  refine hur_substInv R1 (Formalism.MainNotions.FormalGroupSystem.Pf.en_L_zero p K1) (Formalism.MainNotions.FormalGroupSystem.Pf.en_L_one p K1) ?_ ?_
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hd, zero_add,
      Formalism.MainNotions.FormalGroupSystem.Pf.en_logF_one]
    simp
  · intro n
    rw [hd]
    exact Wr_to p K1 R1 hW _ (logF_deriv_int p n)

/- English proof (translation)
Establish `hE` using `hur_en_E p K1 R1 hW`. Establish `hEc : ∀ i, Hur R1 (Formalism.MainNotions.FormalGroupSystem.Pf.en_Ec p K1 i : MvPowerSeries ι K1)`. Introduce `i`. Unfold `Formalism.MainNotions.FormalGroupSystem.Pf.en_Ec`. Rewrite using `[PowerSeries.subst_def]`.

Conclude with `hur_subst R1 (fun _ => constantCoeff_X i) (fun _ => hur_X R1 i) hE`. Rewrite using `[← Formalism.MainNotions.FormalGroupSystem.Pf.en_Ec_inParamK p K1 U]`. Conclude with `hur_subst R1 (Formalism.MainNotions.FormalGroupSystem.Pf.en_Ec_zero p K1) hEc (hur_of_int R1 hU)`.
-/
theorem hur_of_inParam {ι : Type} [Fintype ι] [DecidableEq ι] {U : MvPowerSeries ι K1}
    (hU : IntR R1 (inParamK p K1 U)) : Hur R1 U := by
  have hE := hur_en_E p K1 R1 hW
  have hEc : ∀ i, Hur R1 (Formalism.MainNotions.FormalGroupSystem.Pf.en_Ec p K1 i : MvPowerSeries ι K1) := by
    intro i
    unfold Formalism.MainNotions.FormalGroupSystem.Pf.en_Ec
    rw [PowerSeries.subst_def]
    exact hur_subst R1 (fun _ => constantCoeff_X i) (fun _ => hur_X R1 i) hE
  rw [← Formalism.MainNotions.FormalGroupSystem.Pf.en_Ec_inParamK p K1 U]
  exact hur_subst R1 (Formalism.MainNotions.FormalGroupSystem.Pf.en_Ec_zero p K1) hEc (hur_of_int R1 hU)

end Logs

section Exp

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Introduce `n` and use `by have e : coeff n (expS p f) = ∑ k ∈ range (n.degree + 1), coeff n (C ((k.factorial : K0 p))⁻¹ * f ^ k) := by simp only [coeff_C_mul] rfl rw [e, Finset.mul_sum] exact (Wr p).sum_mem fun k _ => hur_gamma (Wr p) hf hf0 k n`.
-/
theorem hur_expS {ι : Type} [DecidableEq ι] {f : MvPowerSeries ι (K0 p)} (hf : Hur (Wr p) f)
    (hf0 : constantCoeff f = 0) : Hur (Wr p) (expS p f) := fun n => by
  have e : coeff n (expS p f) =
      ∑ k ∈ range (n.degree + 1), coeff n (C ((k.factorial : K0 p))⁻¹ * f ^ k) := by
    simp only [coeff_C_mul]
    rfl
  rw [e, Finset.mul_sum]
  exact (Wr p).sum_mem fun k _ => hur_gamma (Wr p) hf hf0 k n

/- English proof (translation)
Introduce `n` and use `by obtain ⟨y, hy⟩ := h.2 n refine ⟨y, ?_⟩ rw [hy, fc] push_cast rfl`.
-/
theorem hur_be {be : MvPowerSeries (Fin 2) (K0 p)} (h : BeJetInt p be) : Hur (Wr p) be := fun n => by
  obtain ⟨y, hy⟩ := h.2 n
  refine ⟨y, ?_⟩
  rw [hy, fc]
  push_cast
  rfl

/- English proof (translation)
Establish `h0 : ∀ j : Fin 2, constantCoeff ((![X a, X b] : Fin 2 → MvPowerSeries τ (K0 p)) j) = 0`. Apply the tactic sequence `intro j; fin_cases j <;> simp`. Establish `h1 : ∀ j : Fin 2, Hur (Wr p) ((![X a, X b] : Fin 2 → MvPowerSeries τ (K0 p)) j)`. Apply the tactic sequence `intro j; fin_cases j <;> simp [hur_X]`. Use `⟨hur_subst (Wr p) h0 h1 (hur_be h), ?_⟩` and prove the remaining obligations.

Unfold `sub2`. Rewrite using `[cc_subst h0]`. Conclude with `h.1`.
-/
theorem hurwitz_substitute_two_series {τ : Type} [DecidableEq τ] [Finite τ] {be : MvPowerSeries (Fin 2) (K0 p)}
    (h : BeJetInt p be) (a b : τ) :
    Hur (Wr p) (sub2 p be (X a) (X b)) ∧ constantCoeff (sub2 p be (X a) (X b) : MvPowerSeries τ (K0 p)) = 0 := by
  have h0 : ∀ j : Fin 2, constantCoeff ((![X a, X b] : Fin 2 → MvPowerSeries τ (K0 p)) j) = 0 := by
    intro j; fin_cases j <;> simp
  have h1 : ∀ j : Fin 2, Hur (Wr p) ((![X a, X b] : Fin 2 → MvPowerSeries τ (K0 p)) j) := by
    intro j; fin_cases j <;> simp [hur_X]
  refine ⟨hur_subst (Wr p) h0 h1 (hur_be h), ?_⟩
  unfold sub2
  rw [cc_subst h0]
  exact h.1

end Exp

end Formalism.L2.KerInert.Jet

namespace Formalism.L2.KerInert.Jet

open MvPowerSeries Finset Formalism.MainNotions.G Formalism.BasicNotions Formalism.MainNotions.FormalGroupSystem

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Unfold `Pend.PhAt`. Use `⟨hur_sum (Wr p) _ _ fun e _ => (hurwitz_substitute_two_series h _ _).1, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum]`. Conclude with `Finset.sum_eq_zero fun e _ => (hurwitz_substitute_two_series h _ _).2`.
-/
theorem hur_PhAt {X : Sys p} (Y : Pend X) (h : BeJetInt p Y.be) (j : ℕ) (v : X.Pl) :
    Hur (Wr p) (Y.PhAt j v) ∧ constantCoeff (Y.PhAt j v) = 0 := by
  classical
  unfold Pend.PhAt
  refine ⟨hur_sum (Wr p) _ _ fun e _ => (hurwitz_substitute_two_series h _ _).1, ?_⟩
  rw [map_sum]
  exact Finset.sum_eq_zero fun e _ => (hurwitz_substitute_two_series h _ _).2

/- English proof (translation)
Break down `e with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩` into its components or cases. Use `all_goals`. Simplify using `only [Sys.coordZA]`. Use `⟨hur_sum _ _ _ fun s _ => hur_mul _ (hur_C _ (Y.witt_mem_integers_Cp _)) (hur_X _ _), ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem hur_coordZA {X : Sys p} (Y : Pend X) (j : ℕ) (e : X.EA j ⊕ X.EA j) :
    Hur Y.Oc (X.coordZA Y.Kc j e) ∧ constantCoeff (X.coordZA Y.Kc j e) = 0 := by
  classical
  rcases e with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩
  all_goals
    simp only [Sys.coordZA]
    refine ⟨hur_sum _ _ _ fun s _ => hur_mul _ (hur_C _ (Y.witt_mem_integers_Cp _)) (hur_X _ _), ?_⟩
    simp

/- English proof (translation)
Introduce `a b _ hab`. Establish `ha : a ≤ 0`. Establish `: (a : ℝ) ≤ 0` using `by simpa using hab`. Conclude with `this` after adjusting the coercions. Establish `e : (p : Y.Kc) ^ (-a) = (p : Y.Kc) ^ ((-a).toNat)`.

Rewrite using `[← zpow_natCast, Int.toNat_of_nonneg (by omega)]`. Rewrite using `[e]`. Conclude with `Y.Oc.mul_mem (Y.Oc.pow_mem hx b) (Y.Oc.pow_mem (natCast_mem _ p) _)`.
-/
theorem geC_zero_of_mem {X : Sys p} (Y : Pend X) {x : Y.Kc} (hx : x ∈ Y.Oc) : Y.geC x 0 := by
  intro a b _ hab
  have ha : a ≤ 0 := by
    have : (a : ℝ) ≤ 0 := by simpa using hab
    exact_mod_cast this
  have e : (p : Y.Kc) ^ (-a) = (p : Y.Kc) ^ ((-a).toNat) := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (by omega)]
  rw [e]
  exact Y.Oc.mul_mem (Y.Oc.pow_mem hx b) (Y.Oc.pow_mem (natCast_mem _ p) _)

/- English proof (translation)
Introduce `p _ X Y h v j _ U hU I n`. Apply `geC_zero_of_mem` to reduce the goal to its premises. Establish `hexp : Hur Y.Oc (MvPowerSeries.map (algebraMap (K0 p) Y.Kc) (expS p (-Y.PhAt j v)))`. Take `⟨h1, h2⟩` from `hur_PhAt Y h j v`. Conclude with `hur_map (Wr p) (algebraMap (K0 p) Y.Kc) Y.Oc (Wr_to p Y.Kc Y.Oc Y.witt_mem_integers_Cp) (hur_expS (hur_neg _ h1) (by rw [map_neg, h2, neg_zero]))`.

Establish `hUh : Hur Y.Oc U` using `hur_of_inParam p Y.Kc Y.Oc Y.witt_mem_integers_Cp hU`. Establish `hF : Hur Y.Oc (X.ThZA Y.Kc j (MvPowerSeries.map (algebraMap (K0 p) Y.Kc) (expS p (-Y.PhAt j v)) * U))`. Unfold `Sys.ThZA`. Conclude with `hur_subst Y.Oc (fun e => (hur_coordZA Y j e).2) (fun e => (hur_coordZA Y j e).1) (hur_mul _ hexp hUh)`. Unfold `applyD`.

Rewrite using `[MvPolynomial.coeff_sum]`. Use `Y.Oc.sum_mem fun m _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_smul, MvPolynomial.coeff_map, smul_eq_mul]`. Use `Y.Oc.mul_mem (hF m) ?_` and prove the remaining obligations. Rewrite using `[eq_intCast]`.

Conclude with `intCast_mem _ _`.
-/
theorem jets_low_order_at_zero : LowAtZero := by
  intro p _ X Y h v j _ U hU I n
  classical
  apply geC_zero_of_mem
  have hexp : Hur Y.Oc (MvPowerSeries.map (algebraMap (K0 p) Y.Kc) (expS p (-Y.PhAt j v))) := by
    obtain ⟨h1, h2⟩ := hur_PhAt Y h j v
    exact hur_map (Wr p) (algebraMap (K0 p) Y.Kc) Y.Oc (Wr_to p Y.Kc Y.Oc Y.witt_mem_integers_Cp)
      (hur_expS (hur_neg _ h1) (by rw [map_neg, h2, neg_zero]))
  have hUh : Hur Y.Oc U := hur_of_inParam p Y.Kc Y.Oc Y.witt_mem_integers_Cp hU
  have hF : Hur Y.Oc (X.ThZA Y.Kc j
      (MvPowerSeries.map (algebraMap (K0 p) Y.Kc) (expS p (-Y.PhAt j v)) * U)) := by
    unfold Sys.ThZA
    exact hur_subst Y.Oc (fun e => (hur_coordZA Y j e).2) (fun e => (hur_coordZA Y j e).1)
      (hur_mul _ hexp hUh)
  unfold applyD
  rw [MvPolynomial.coeff_sum]
  refine Y.Oc.sum_mem fun m _ => ?_
  rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_map, smul_eq_mul]
  refine Y.Oc.mul_mem (hF m) ?_
  rw [eq_intCast]
  exact intCast_mem _ _

/- English proof (translation)
Introduce `_ p _ X Y h v j hj` and use `jets_low_order_at_zero p X Y h v j hj`.
-/
theorem adm11OfIntegralJets : Adm11OfIntegralJets := fun _ p _ X Y h v j hj => jets_low_order_at_zero p X Y h v j hj

end Formalism.L2.KerInert.Jet

namespace Formalism.L2.KerInert.Jet

open MvPowerSeries Finset Formalism.MainNotions.G Formalism.BasicNotions Formalism.MainNotions.FormalGroupSystem

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section Gen2

variable {K : Type*} [Field K] {σ : Type*} (R : Subring K)

/- English proof (translation)
Introduce `n`. Distinguish the cases in `hn : n = 0`. Substitute `hn` using the available equality. Rewrite using `[fc_zero, one_mul]`. Simplify using `using h0`.

Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, n i ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hn (Finsupp.ext hc)`. Rewrite using `[← sub_single_one_add_single_one_of_ne_zero n i hi, ← fc_coeff_pderiv]`.

Conclude with `hd i _`.
-/
theorem hur_of_pderiv [DecidableEq σ] {f : MvPowerSeries σ K} (h0 : constantCoeff f ∈ R)
    (hd : ∀ i, Hur R (pderiv K i f)) : Hur R f := by
  intro n
  by_cases hn : n = 0
  · subst hn
    rw [fc_zero, one_mul]
    simpa using h0
  · obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hn (Finsupp.ext hc)
    rw [← sub_single_one_add_single_one_of_ne_zero n i hi, ← fc_coeff_pderiv]
    exact hd i _

/- English proof (translation)
Rewrite using `[show ((k : MvPowerSeries σ K)) = C (k : K) from (map_natCast _ k).symm]`. Conclude with `hur_C R (natCast_mem R k)`.
-/
theorem hur_natCast [DecidableEq σ] (k : ℕ) : Hur R (k : MvPowerSeries σ K) := by
  rw [show ((k : MvPowerSeries σ K)) = C (k : K) from (map_natCast _ k).symm]
  exact hur_C R (natCast_mem R k)

/- English proof (translation)
Establish `hEi : E * E⁻¹ = 1` using `MvPowerSeries.mul_inv_cancel E (by rw [h1]; exact one_ne_zero)`. Establish `hiE : E⁻¹ * E = 1` using `MvPowerSeries.inv_mul_cancel E (by rw [h1]; exact one_ne_zero)`. Establish `hD : ∀ i, pderiv K i E⁻¹ = -(E⁻¹ ^ 2 * pderiv K i E)`. Introduce `i`. Establish `e` using `congrArg (pderiv K i) hEi`.

Rewrite `e` using `[Derivation.leibniz, Derivation.map_one_eq_zero, smul_eq_mul, smul_eq_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hc1 : constantCoeff E⁻¹ = 1` using `by rw [MvPowerSeries.constantCoeff_inv, h1, inv_one]`. Use `hur_of_closed_under_pderiv R (fun h => ∃ (j : ℕ) (g : MvPowerSeries σ K), Hur R g ∧ h = E⁻¹ ^ j * g) ?_ ?_ E⁻¹ ⟨1, 1, hur_one R, by rw [pow_one, mul_one]⟩` as an intermediate fact. Conclude with `this`.

Introduce and unpack `h ⟨j, g, hg, rfl⟩`. Rewrite using `[map_mul, map_pow, hc1, one_pow, one_mul]`. Conclude with `hur_cc R hg`. Introduce and unpack `h ⟨j, g, hg, rfl⟩ i`. Use `⟨E⁻¹ ^ j * pderiv K i g, E⁻¹ ^ (j + 1) * (-((j : MvPowerSeries σ K) * (pderiv K i E * g))), ⟨j, _, hur_pderiv R hg i, rfl⟩, ⟨j + 1, _, hur_neg R (hur_mul R (hur_natCast R j) (hur_mul R (hur_pderiv R hE i) hg)), rfl⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[Derivation.leibniz, Derivation.leibniz_pow, hD]`. Simplify using `only [smul_eq_mul, nsmul_eq_mul]`. Consider the cases of `j with`. Consider the case `zero => simp`. Consider the case `succ j`.

Simplify using `only [Nat.add_sub_cancel]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hur_inv [DecidableEq σ] {E : MvPowerSeries σ K} (hE : Hur R E) (h1 : constantCoeff E = 1) :
    Hur R E⁻¹ := by
  have hEi : E * E⁻¹ = 1 := MvPowerSeries.mul_inv_cancel E (by rw [h1]; exact one_ne_zero)
  have hiE : E⁻¹ * E = 1 := MvPowerSeries.inv_mul_cancel E (by rw [h1]; exact one_ne_zero)
  have hD : ∀ i, pderiv K i E⁻¹ = -(E⁻¹ ^ 2 * pderiv K i E) := by
    intro i
    have e := congrArg (pderiv K i) hEi
    rw [Derivation.leibniz, Derivation.map_one_eq_zero, smul_eq_mul, smul_eq_mul] at e
    calc pderiv K i E⁻¹ = (E⁻¹ * E) * pderiv K i E⁻¹ := by rw [hiE, one_mul]
      _ = E⁻¹ * (E * pderiv K i E⁻¹) := by ring
      _ = E⁻¹ * (-(E⁻¹ * pderiv K i E)) := by rw [eq_neg_of_add_eq_zero_left e]
      _ = -(E⁻¹ ^ 2 * pderiv K i E) := by ring
  have hc1 : constantCoeff E⁻¹ = 1 := by rw [MvPowerSeries.constantCoeff_inv, h1, inv_one]
  have := hur_of_closed_under_pderiv R (fun h => ∃ (j : ℕ) (g : MvPowerSeries σ K), Hur R g ∧ h = E⁻¹ ^ j * g) ?_ ?_ E⁻¹
    ⟨1, 1, hur_one R, by rw [pow_one, mul_one]⟩
  · exact this
  · rintro h ⟨j, g, hg, rfl⟩
    rw [map_mul, map_pow, hc1, one_pow, one_mul]
    exact hur_cc R hg
  · rintro h ⟨j, g, hg, rfl⟩ i
    refine ⟨E⁻¹ ^ j * pderiv K i g, E⁻¹ ^ (j + 1) * (-((j : MvPowerSeries σ K) * (pderiv K i E * g))),
      ⟨j, _, hur_pderiv R hg i, rfl⟩,
      ⟨j + 1, _, hur_neg R (hur_mul R (hur_natCast R j) (hur_mul R (hur_pderiv R hE i) hg)), rfl⟩, ?_⟩
    rw [Derivation.leibniz, Derivation.leibniz_pow, hD]
    simp only [smul_eq_mul, nsmul_eq_mul]
    cases j with
    | zero => simp
    | succ j =>
      simp only [Nat.add_sub_cancel]
      push_cast
      ring

end Gen2

section Simeq

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[Formalism.L2.Th1.C.coeff_mvExp hf (N := n.degree + 1) (Nat.lt_succ_self _)]`. Both sides reduce to the same expression.
-/
theorem expS_eq_mvExp {ι : Type} {f : MvPowerSeries ι (K0 p)} (hf : constantCoeff f = 0) :
    expS p f = Formalism.L2.Th1.C.mvExp f := by
  ext n
  rw [Formalism.L2.Th1.C.coeff_mvExp hf (N := n.degree + 1) (Nat.lt_succ_self _)]
  rfl

/- English proof (translation)
Unfold `inParam inParamK`. Simplify using `[Algebra.algebraMap_self, PowerSeries.map_id]`.
-/
theorem inParam_eq {ι : Type} (f : MvPowerSeries ι (K0 p)) : inParam p f = inParamK p (K0 p) f := by
  unfold inParam inParamK
  simp [Algebra.algebraMap_self, PowerSeries.map_id]

/- English proof (translation)
Take `⟨hF0, hh, _, he⟩` from `h`. Establish `hW : ∀ x : WW p, algebraMap (K0 p) (K0 p) (algebraMap (WW p) (K0 p) x) ∈ Wr p` using `fun x => by`. Rewrite using `[Algebra.algebraMap_self, RingHom.id_apply]`. Conclude with `mem_Wr p x`. Establish `hG0 : constantCoeff (inParamK p (K0 p) (f - g)) = 0`.

Rewrite using `[Formalism.MainNotions.FormalGroupSystem.Pf.en_inParamK_eq, cc_subst (Formalism.MainNotions.FormalGroupSystem.Pf.en_aL_zero p (K0 p))]`. Conclude with `hF0`. Establish `hE : inParamK p (K0 p) (Formalism.L2.Th1.C.mvExp (f - g)) = 1 + MvPowerSeries.map (algebraMap (WW p) (K0 p)) hh`. Rewrite using `[Formalism.MainNotions.FormalGroupSystem.Pf.en_inParamK_eq, Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.substMv_mvExp hF0 (Formalism.MainNotions.FormalGroupSystem.Pf.en_aL_zero p (K0 p)), ← Formalism.MainNotions.FormalGroupSystem.Pf.en_inParamK_eq, ← expS_eq_mvExp hG0, ← inPara …`. Establish `hint : IntR (Wr p) (inParamK p (K0 p) (Formalism.L2.Th1.C.mvExp (f - g)))`.

Introduce `n`. Rewrite using `[hE, map_add, coeff_map, coeff_one]`. Use `(Wr p).add_mem ?_ (mem_Wr p _)` and prove the remaining obligations. Use `split_ifs`. Conclude with `(Wr p).one_mem`.

Conclude with `(Wr p).zero_mem`. Establish `hEh : Hur (Wr p) (Formalism.L2.Th1.C.mvExp (f - g))` using `hur_of_inParam p (K0 p) (Wr p) hW hint`. Establish `h1 : constantCoeff (Formalism.L2.Th1.C.mvExp (f - g)) = 1` using `Formalism.L2.Th1.C.constantCoeff_mvExp hF0`. Establish `hEi : Hur (Wr p) (Formalism.L2.Th1.C.mvExp (f - g))⁻¹` using `hur_inv _ hEh h1`. Use `hur_of_pderiv _ (by rw [hF0]; exact (Wr p).zero_mem) fun i => ?_` and prove the remaining obligations.

Establish `e : pderiv (K0 p) i (f - g) = pderiv (K0 p) i (Formalism.L2.Th1.C.mvExp (f - g)) * (Formalism.L2.Th1.C.mvExp (f - g))⁻¹`. Rewrite using `[Formalism.L2.Th1.C.pderiv_mvExp hF0, mul_assoc, MvPowerSeries.mul_inv_cancel _ (by rw [h1]; exact one_ne_zero), mul_one]`. Rewrite using `[e]`. Conclude with `hur_mul _ (hur_pderiv _ hEh i) hEi`.
-/
theorem hur_of_simeq {ι : Type} [Fintype ι] [DecidableEq ι] {f g : MvPowerSeries ι (K0 p)}
    (h : Simeq p f g) : Hur (Wr p) (f - g) := by
  obtain ⟨hF0, hh, _, he⟩ := h
  have hW : ∀ x : WW p, algebraMap (K0 p) (K0 p) (algebraMap (WW p) (K0 p) x) ∈ Wr p := fun x => by
    rw [Algebra.algebraMap_self, RingHom.id_apply]
    exact mem_Wr p x
  have hG0 : constantCoeff (inParamK p (K0 p) (f - g)) = 0 := by
    rw [Formalism.MainNotions.FormalGroupSystem.Pf.en_inParamK_eq, cc_subst (Formalism.MainNotions.FormalGroupSystem.Pf.en_aL_zero p (K0 p))]
    exact hF0
  have hE : inParamK p (K0 p) (Formalism.L2.Th1.C.mvExp (f - g)) =
      1 + MvPowerSeries.map (algebraMap (WW p) (K0 p)) hh := by
    rw [Formalism.MainNotions.FormalGroupSystem.Pf.en_inParamK_eq,
      Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.substMv_mvExp hF0 (Formalism.MainNotions.FormalGroupSystem.Pf.en_aL_zero p (K0 p)),
      ← Formalism.MainNotions.FormalGroupSystem.Pf.en_inParamK_eq, ← expS_eq_mvExp hG0, ← inParam_eq, he]
  have hint : IntR (Wr p) (inParamK p (K0 p) (Formalism.L2.Th1.C.mvExp (f - g))) := by
    intro n
    rw [hE, map_add, coeff_map, coeff_one]
    refine (Wr p).add_mem ?_ (mem_Wr p _)
    split_ifs
    · exact (Wr p).one_mem
    · exact (Wr p).zero_mem
  have hEh : Hur (Wr p) (Formalism.L2.Th1.C.mvExp (f - g)) := hur_of_inParam p (K0 p) (Wr p) hW hint
  have h1 : constantCoeff (Formalism.L2.Th1.C.mvExp (f - g)) = 1 := Formalism.L2.Th1.C.constantCoeff_mvExp hF0
  have hEi : Hur (Wr p) (Formalism.L2.Th1.C.mvExp (f - g))⁻¹ := hur_inv _ hEh h1
  refine hur_of_pderiv _ (by rw [hF0]; exact (Wr p).zero_mem) fun i => ?_
  have e : pderiv (K0 p) i (f - g) =
      pderiv (K0 p) i (Formalism.L2.Th1.C.mvExp (f - g)) * (Formalism.L2.Th1.C.mvExp (f - g))⁻¹ := by
    rw [Formalism.L2.Th1.C.pderiv_mvExp hF0, mul_assoc,
      MvPowerSeries.mul_inv_cancel _ (by rw [h1]; exact one_ne_zero), mul_one]
  rw [e]
  exact hur_mul _ (hur_pderiv _ hEh i) hEi

end Simeq

end Formalism.L2.KerInert.Jet

namespace Formalism.L2.KerInert.Jet

open MvPowerSeries Finset Formalism.MainNotions.G Formalism.BasicNotions Formalism.MainNotions.FormalGroupSystem

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section Two

variable {K : Type*} [Field K] {τ : Type*} [Finite τ]

/- English proof (translation)
Apply the tactic sequence `rw [Formalism.G.LogCR.pderiv_subst (fun j => by fin_cases j <;> simpa), Fin.sum_univ_two]`. Both sides reduce to the same expression.
-/
theorem pd2 (g : MvPowerSeries (Fin 2) K) {u w : MvPowerSeries τ K} (hu : constantCoeff u = 0)
    (hw : constantCoeff w = 0) (i : τ) :
    pderiv K i (subst ![u, w] g) =
      subst ![u, w] (pderiv K 0 g) * pderiv K i u + subst ![u, w] (pderiv K 1 g) * pderiv K i w := by
  rw [Formalism.G.LogCR.pderiv_subst (fun j => by fin_cases j <;> simpa), Fin.sum_univ_two]
  rfl

/- English proof (translation)
Introduce `j`. Apply the tactic sequence `fin_cases j <;> simp [hu, hw]`.
-/
theorem cc2 {u w : MvPowerSeries τ K} (hu : constantCoeff u = 0) (hw : constantCoeff w = 0) :
    ∀ j : Fin 2, constantCoeff ((![u, w] : Fin 2 → MvPowerSeries τ K) j) = 0 := by
  intro j
  fin_cases j <;> simp [hu, hw]

end Two

section Jets

variable {p : ℕ} [Fact p.Prime]

local notation "KK" => K0 p

/- English proof (translation)
The claim follows from `constantCoeff_X i`.
-/
theorem constantCoeff_X_fin_three (i : Fin 3) : constantCoeff (X i : MvPowerSeries (Fin 3) KK) = 0 := constantCoeff_X i

/- English proof (translation)
Establish `h01 : constantCoeff (X 0 + X 1 : MvPowerSeries (Fin 3) KK) = 0` using `by simp`. Unfold `sub2`. Simplify using `only [sub_zero, map_sub]`. Rewrite using `[pd2 _ h01 (constantCoeff_X_fin_three 2), pd2 _ (constantCoeff_X_fin_three 0) (constantCoeff_X_fin_three 2), pd2 _ (constantCoeff_X_fin_three 1) (constantCoeff_X_fin_three 2)]`. Simplify using `only [map_add, pderiv_X_self, pderiv_X_of_ne (show (0 : Fin 3) ≠ 1 by decide), pderiv_X_of_ne (show (2 : Fin 3) ≠ 1 by decide), mul_zero, add_zero, mul_one, zero_add, sub_zero]`.

Rewrite using `[pd2 _ h01 (constantCoeff_X_fin_three 2), pd2 _ (constantCoeff_X_fin_three 1) (constantCoeff_X_fin_three 2)]`. Simplify using `[pderiv_X_self, pderiv_X_of_ne (show (1 : Fin 3) ≠ 0 by decide), pderiv_X_of_ne (show (2 : Fin 3) ≠ 0 by decide)]`.
-/
theorem second_deriv_additive_first (be : MvPowerSeries (Fin 2) KK) :
    pderiv KK 0 (pderiv KK 1 (sub2 p be (X 0 + X 1) (X 2) - sub2 p be (X 0) (X 2) - sub2 p be (X 1) (X 2) -
      (0 : MvPowerSeries (Fin 3) KK))) =
      subst ![(X 0 + X 1 : MvPowerSeries (Fin 3) KK), X 2] (pderiv KK 0 (pderiv KK 0 be)) := by
  have h01 : constantCoeff (X 0 + X 1 : MvPowerSeries (Fin 3) KK) = 0 := by simp
  unfold sub2
  simp only [sub_zero, map_sub]
  rw [pd2 _ h01 (constantCoeff_X_fin_three 2), pd2 _ (constantCoeff_X_fin_three 0) (constantCoeff_X_fin_three 2), pd2 _ (constantCoeff_X_fin_three 1) (constantCoeff_X_fin_three 2)]
  simp only [map_add, pderiv_X_self, pderiv_X_of_ne (show (0 : Fin 3) ≠ 1 by decide),
    pderiv_X_of_ne (show (2 : Fin 3) ≠ 1 by decide), mul_zero, add_zero, mul_one, zero_add, sub_zero]
  rw [pd2 _ h01 (constantCoeff_X_fin_three 2), pd2 _ (constantCoeff_X_fin_three 1) (constantCoeff_X_fin_three 2)]
  simp [pderiv_X_self, pderiv_X_of_ne (show (1 : Fin 3) ≠ 0 by decide),
    pderiv_X_of_ne (show (2 : Fin 3) ≠ 0 by decide)]

/- English proof (translation)
Establish `h12 : constantCoeff (X 1 + X 2 : MvPowerSeries (Fin 3) KK) = 0` using `by simp`. Unfold `sub2`. Simplify using `only [sub_zero, map_sub]`. Rewrite using `[pd2 _ (constantCoeff_X_fin_three 0) h12, pd2 _ (constantCoeff_X_fin_three 0) (constantCoeff_X_fin_three 1), pd2 _ (constantCoeff_X_fin_three 0) (constantCoeff_X_fin_three 2)]`. Simplify using `only [map_add, pderiv_X_self, pderiv_X_of_ne (show (0 : Fin 3) ≠ 2 by decide), pderiv_X_of_ne (show (1 : Fin 3) ≠ 2 by decide), mul_zero, add_zero, mul_one, zero_add, sub_zero]`.

Rewrite using `[pd2 _ (constantCoeff_X_fin_three 0) h12, pd2 _ (constantCoeff_X_fin_three 0) (constantCoeff_X_fin_three 2)]`. Simplify using `[pderiv_X_self, pderiv_X_of_ne (show (0 : Fin 3) ≠ 1 by decide), pderiv_X_of_ne (show (2 : Fin 3) ≠ 1 by decide)]`.
-/
theorem second_deriv_additive_second (be : MvPowerSeries (Fin 2) KK) :
    pderiv KK 1 (pderiv KK 2 (sub2 p be (X 0) (X 1 + X 2) - sub2 p be (X 0) (X 1) - sub2 p be (X 0) (X 2) -
      (0 : MvPowerSeries (Fin 3) KK))) =
      subst ![(X 0 : MvPowerSeries (Fin 3) KK), X 1 + X 2] (pderiv KK 1 (pderiv KK 1 be)) := by
  have h12 : constantCoeff (X 1 + X 2 : MvPowerSeries (Fin 3) KK) = 0 := by simp
  unfold sub2
  simp only [sub_zero, map_sub]
  rw [pd2 _ (constantCoeff_X_fin_three 0) h12, pd2 _ (constantCoeff_X_fin_three 0) (constantCoeff_X_fin_three 1), pd2 _ (constantCoeff_X_fin_three 0) (constantCoeff_X_fin_three 2)]
  simp only [map_add, pderiv_X_self, pderiv_X_of_ne (show (0 : Fin 3) ≠ 2 by decide),
    pderiv_X_of_ne (show (1 : Fin 3) ≠ 2 by decide), mul_zero, add_zero, mul_one, zero_add, sub_zero]
  rw [pd2 _ (constantCoeff_X_fin_three 0) h12, pd2 _ (constantCoeff_X_fin_three 0) (constantCoeff_X_fin_three 2)]
  simp [pderiv_X_self, pderiv_X_of_ne (show (0 : Fin 3) ≠ 1 by decide),
    pderiv_X_of_ne (show (2 : Fin 3) ≠ 1 by decide)]

/- English proof (translation)
Establish `ha : HasSubst (![u, w] : Fin 2 → MvPowerSeries (Fin 3) KK)` using `hasSubst_of_constantCoeff_zero (cc2 hu hw)`. Establish `hbs : HasSubst b` using `hasSubst_of_constantCoeff_zero hb`. Rewrite using `[subst_comp_subst_apply ha hbs]`. Establish `e : (fun s => subst b ((![u, w] : Fin 2 → MvPowerSeries (Fin 3) KK) s)) = X`. Use function extensionality and compare the values at `s`.

Use `fin_cases s`. Simplify using `using hbu`. Simplify using `using hbw`. Rewrite using `[e, subst_self]`. Both sides reduce to the same expression.
-/
theorem restr (g : MvPowerSeries (Fin 2) KK) (u w : MvPowerSeries (Fin 3) KK) (b : Fin 3 → MvPowerSeries (Fin 2) KK)
    (hu : constantCoeff u = 0) (hw : constantCoeff w = 0) (hb : ∀ j, constantCoeff (b j) = 0)
    (hbu : subst b u = X 0) (hbw : subst b w = X 1) :
    subst b (subst ![u, w] g) = g := by
  have ha : HasSubst (![u, w] : Fin 2 → MvPowerSeries (Fin 3) KK) :=
    hasSubst_of_constantCoeff_zero (cc2 hu hw)
  have hbs : HasSubst b := hasSubst_of_constantCoeff_zero hb
  rw [subst_comp_subst_apply ha hbs]
  have e : (fun s => subst b ((![u, w] : Fin 2 → MvPowerSeries (Fin 3) KK) s)) = X := by
    funext s
    fin_cases s
    · simpa using hbu
    · simpa using hbw
  rw [e, subst_self]
  rfl

end Jets

end Formalism.L2.KerInert.Jet

namespace Formalism.L2.KerInert.Jet

open MvPowerSeries Finset Formalism.MainNotions.G Formalism.BasicNotions Formalism.MainNotions.FormalGroupSystem

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section Conj

variable {p : ℕ} [Fact p.Prime]

local notation "KK" => K0 p

/- English proof (translation)
Establish `hu : constantCoeff (C a' * X 0 : MvPowerSeries (Fin 2) KK) = 0` using `by simp`. Establish `hw : constantCoeff (C b' * X 1 : MvPowerSeries (Fin 2) KK) = 0` using `by simp`. Establish `hX0 : constantCoeff (X 0 : MvPowerSeries (Fin 2) KK) = 0` using `constantCoeff_X 0`. Establish `hX1 : constantCoeff (X 1 : MvPowerSeries (Fin 2) KK) = 0` using `constantCoeff_X 1`. Establish `hu0 : pderiv KK 0 (C a' * X 0 : MvPowerSeries (Fin 2) KK) = C a'`.

Rewrite using `[Derivation.leibniz]`. Simplify using the standard rewrite rules. Establish `hu1 : pderiv KK 1 (C a' * X 0 : MvPowerSeries (Fin 2) KK) = 0`. Rewrite using `[Derivation.leibniz]; simp [pderiv_X_of_ne (show (0 : Fin 2) ≠ 1 by decide)]`. Establish `hw0 : pderiv KK 0 (C b' * X 1 : MvPowerSeries (Fin 2) KK) = 0`.

Rewrite using `[Derivation.leibniz]; simp [pderiv_X_of_ne (show (1 : Fin 2) ≠ 0 by decide)]`. Establish `hw1 : pderiv KK 1 (C b' * X 1 : MvPowerSeries (Fin 2) KK) = C b'`. Rewrite using `[Derivation.leibniz]`. Simplify using the standard rewrite rules. Establish `A1 : pderiv KK 1 (subst ![C a' * X 0, X 1] be : MvPowerSeries (Fin 2) KK) =`.

Substitute `![C a' * X 0, X 1] (pderiv KK 1 be) := by` using the available equality. Rewrite using `[pd2 _ hu hX1, hu1, pderiv_X_self]`. Expand and normalize the polynomial expressions, which then agree. Establish `A0 : pderiv KK 0 (subst ![C a' * X 0, X 1] (pderiv KK 1 be) : MvPowerSeries (Fin 2) KK) =`. Substitute `![C a' * X 0, X 1] (pderiv KK 0 (pderiv KK 1 be)) * C a' := by` using the available equality.

Rewrite using `[pd2 _ hu hX1, hu0, pderiv_X_of_ne (show (1 : Fin 2) ≠ 0 by decide)]; ring`. Establish `B1 : pderiv KK 1 (subst ![X 0, C b' * X 1] be : MvPowerSeries (Fin 2) KK) =`. Substitute `![X 0, C b' * X 1] (pderiv KK 1 be) * C b' := by` using the available equality. Rewrite using `[pd2 _ hX0 hw, pderiv_X_of_ne (show (0 : Fin 2) ≠ 1 by decide), hw1]; ring`. Establish `B0 : pderiv KK 0 (subst ![X 0, C b' * X 1] (pderiv KK 1 be) * C b' : MvPowerSeries (Fin 2) KK) =`.

Substitute `![X 0, C b' * X 1] (pderiv KK 0 (pderiv KK 1 be)) * C b' := by` using the available equality. Rewrite using `[Derivation.leibniz, pd2 _ hX0 hw, pderiv_C, pderiv_X_self, hw0]`. Simplify using `[mul_comm]`. Unfold `sub2`. Rewrite using `[map_sub, map_sub, A1, A0, B1, B0, map_sub, map_mul, map_mul, cc_subst (cc2 hu hX1), cc_subst (cc2 hX0 hw), constantCoeff_C, constantCoeff_C]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem conj_dd (be : MvPowerSeries (Fin 2) KK) (a' b' : KK) :
    constantCoeff (pderiv KK 0 (pderiv KK 1 (sub2 p be (C a' * X 0) (X 1) - sub2 p be (X 0) (C b' * X 1) :
      MvPowerSeries (Fin 2) KK))) =
      constantCoeff (pderiv KK 0 (pderiv KK 1 be)) * (a' - b') := by
  have hu : constantCoeff (C a' * X 0 : MvPowerSeries (Fin 2) KK) = 0 := by simp
  have hw : constantCoeff (C b' * X 1 : MvPowerSeries (Fin 2) KK) = 0 := by simp
  have hX0 : constantCoeff (X 0 : MvPowerSeries (Fin 2) KK) = 0 := constantCoeff_X 0
  have hX1 : constantCoeff (X 1 : MvPowerSeries (Fin 2) KK) = 0 := constantCoeff_X 1
  have hu0 : pderiv KK 0 (C a' * X 0 : MvPowerSeries (Fin 2) KK) = C a' := by
    rw [Derivation.leibniz]; simp
  have hu1 : pderiv KK 1 (C a' * X 0 : MvPowerSeries (Fin 2) KK) = 0 := by
    rw [Derivation.leibniz]; simp [pderiv_X_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
  have hw0 : pderiv KK 0 (C b' * X 1 : MvPowerSeries (Fin 2) KK) = 0 := by
    rw [Derivation.leibniz]; simp [pderiv_X_of_ne (show (1 : Fin 2) ≠ 0 by decide)]
  have hw1 : pderiv KK 1 (C b' * X 1 : MvPowerSeries (Fin 2) KK) = C b' := by
    rw [Derivation.leibniz]; simp
  have A1 : pderiv KK 1 (subst ![C a' * X 0, X 1] be : MvPowerSeries (Fin 2) KK) =
      subst ![C a' * X 0, X 1] (pderiv KK 1 be) := by
    rw [pd2 _ hu hX1, hu1, pderiv_X_self]; ring
  have A0 : pderiv KK 0 (subst ![C a' * X 0, X 1] (pderiv KK 1 be) : MvPowerSeries (Fin 2) KK) =
      subst ![C a' * X 0, X 1] (pderiv KK 0 (pderiv KK 1 be)) * C a' := by
    rw [pd2 _ hu hX1, hu0, pderiv_X_of_ne (show (1 : Fin 2) ≠ 0 by decide)]; ring
  have B1 : pderiv KK 1 (subst ![X 0, C b' * X 1] be : MvPowerSeries (Fin 2) KK) =
      subst ![X 0, C b' * X 1] (pderiv KK 1 be) * C b' := by
    rw [pd2 _ hX0 hw, pderiv_X_of_ne (show (0 : Fin 2) ≠ 1 by decide), hw1]; ring
  have B0 : pderiv KK 0 (subst ![X 0, C b' * X 1] (pderiv KK 1 be) * C b' : MvPowerSeries (Fin 2) KK) =
      subst ![X 0, C b' * X 1] (pderiv KK 0 (pderiv KK 1 be)) * C b' := by
    rw [Derivation.leibniz, pd2 _ hX0 hw, pderiv_C, pderiv_X_self, hw0]; simp [mul_comm]
  unfold sub2
  rw [map_sub, map_sub, A1, A0, B1, B0, map_sub, map_mul, map_mul, cc_subst (cc2 hu hX1),
    cc_subst (cc2 hX0 hw), constantCoeff_C, constantCoeff_C]
  ring

/- English proof (translation)
The claim follows from `(sub_single_one_add_single_one_of_ne_zero n i h).symm`.
-/
theorem decomp (n : Fin 2 →₀ ℕ) (i : Fin 2) (h : n i ≠ 0) : n = (n - Finsupp.single i 1) + Finsupp.single i 1 := (sub_single_one_add_single_one_of_ne_zero n i h).symm

/- English proof (translation)
Establish `hcc : constantCoeff be = 0`. Assume the negation of the conclusion as `hc`. Use `h.ab 0 (by rwa [coeff_zero_eq_constantCoeff_apply])` as an intermediate fact. Simplify using `at this`. Establish `h00 : Hur (Wr p) (pderiv KK 0 (pderiv KK 0 be))`.

Establish `H` using `hur_pderiv _ (hur_pderiv _ (hur_of_simeq h.add1) 1) 0`. Rewrite `H` using `[second_deriv_additive_first]`. Establish `hb0 : ∀ j, constantCoeff ((![X 0, 0, X 1] : Fin 3 → MvPowerSeries (Fin 2) KK) j) = 0`. Apply the tactic sequence `intro j; fin_cases j <;> simp`. Establish `hb : HasSubst (![X 0, 0, X 1] : Fin 3 → MvPowerSeries (Fin 2) KK)` using `hasSubst_of_constantCoeff_zero hb0`.

Apply the tactic sequence `have := hur_subst (Wr p) hb0 (by intro j; fin_cases j <;> simp [hur_X, hur_zero]) H`. Rewrite `this` using `[restr _ _ _ _ (by simp) (by simp) hb0 (by rw [subst_add hb, subst_X hb, subst_X hb]; simp) (by rw [subst_X hb]; simp)]`. Then use the resulting hypothesis. Establish `h11 : Hur (Wr p) (pderiv KK 1 (pderiv KK 1 be))`. Establish `H` using `hur_pderiv _ (hur_pderiv _ (hur_of_simeq h.add2) 2) 1`. Rewrite `H` using `[second_deriv_additive_second]`.

Establish `hb0 : ∀ j, constantCoeff ((![X 0, X 1, 0] : Fin 3 → MvPowerSeries (Fin 2) KK) j) = 0`. Apply the tactic sequence `intro j; fin_cases j <;> simp`. Establish `hb : HasSubst (![X 0, X 1, 0] : Fin 3 → MvPowerSeries (Fin 2) KK)` using `hasSubst_of_constantCoeff_zero hb0`. Apply the tactic sequence `have := hur_subst (Wr p) hb0 (by intro j; fin_cases j <;> simp [hur_X, hur_zero]) H`. Rewrite `this` using `[restr _ _ _ _ (by simp) (by simp) hb0 (by rw [subst_X hb]; simp) (by rw [subst_add hb, subst_X hb, subst_X hb]; simp)]`. Then use the resulting hypothesis.

Establish `h01 : constantCoeff (pderiv KK 0 (pderiv KK 1 be)) ∈ Wr p`. Take `⟨α, hα2, u, hu⟩` from `hα`. Establish `hc` using `hur_cc _ (hur_pderiv _ (hur_pderiv _ (hur_of_simeq (hconj α hα2)) 1) 0)`. Rewrite `hc` using `[conj_dd, ← map_sub, ← hu]`. Establish `e : constantCoeff (pderiv KK 0 (pderiv KK 1 be)) = constantCoeff (pderiv KK 0 (pderiv KK 1 be)) * algebraMap (WW p) KK (u : WW p) * algebraMap (WW p) KK ((u⁻¹ : (WW p)ˣ) : WW p)`.

Rewrite using `[mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]`. Rewrite using `[e]`. Conclude with `(Wr p).mul_mem hc (mem_Wr p _)`. Use `⟨hcc, fun n => ?_⟩` and prove the remaining obligations. It suffices to establish `hs : fc n * coeff n be ∈ Wr p by`.

Take `⟨y, hy⟩` from `hs`. Conclude with `⟨y, by rw [hy]; simp [fc]⟩`. Distinguish the cases in `hz : n 0 = 0 ∨ n 1 = 0`. Establish `: coeff n be = 0`. Assume the negation of the conclusion as `hc`.

Use `h.ab n hc` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[this, mul_zero]`. Conclude with `(Wr p).zero_mem`. Use `push Not at hz`.

Distinguish the cases in `h2 : 2 ≤ n 0`. Establish `e1` using `decomp n 0 hz.1`. Establish `hm : (n - Finsupp.single 0 1 : Fin 2 →₀ ℕ) 0 ≠ 0` using `by simp; omega`. Establish `e2` using `decomp (n - Finsupp.single 0 1) 0 hm`. Rewrite using `[e1, ← fc_coeff_pderiv, e2, ← fc_coeff_pderiv]`.

Conclude with `h00 _`. Distinguish the cases in `h2' : 2 ≤ n 1`. Establish `e1` using `decomp n 1 hz.2`. Establish `hm : (n - Finsupp.single 1 1 : Fin 2 →₀ ℕ) 1 ≠ 0` using `by simp; omega`. Establish `e2` using `decomp (n - Finsupp.single 1 1) 1 hm`.

Rewrite using `[e1, ← fc_coeff_pderiv, e2, ← fc_coeff_pderiv]`. Conclude with `h11 _`. Establish `en : n = (0 + Finsupp.single 0 1) + Finsupp.single 1 1`. Use extensionality with `x`. Apply the tactic sequence `fin_cases x <;> simp <;> omega`.

Rewrite using `[en, ← fc_coeff_pderiv, ← fc_coeff_pderiv, fc_zero, one_mul, coeff_zero_eq_constantCoeff_apply]`. Conclude with `h01`.
-/
theorem beJet_of_prop_conj (hα : ∃ α : WW p, (sigW p)^[2] α = α ∧ IsUnit (α - sigW p α))
    {be : MvPowerSeries (Fin 2) KK} (h : BeProp p be)
    (hconj : ∀ α : WW p, (sigW p)^[2] α = α →
      Simeq p (sub2 p be (C (algebraMap (WW p) KK α) * X 0) (X 1) : MvPowerSeries (Fin 2) KK)
        (sub2 p be (X 0) (C (algebraMap (WW p) KK (sigW p α)) * X 1))) : BeJetInt p be := by
  classical
  have hcc : constantCoeff be = 0 := by
    by_contra hc
    have := h.ab 0 (by rwa [coeff_zero_eq_constantCoeff_apply])
    simp at this
  have h00 : Hur (Wr p) (pderiv KK 0 (pderiv KK 0 be)) := by
    have H := hur_pderiv _ (hur_pderiv _ (hur_of_simeq h.add1) 1) 0
    rw [second_deriv_additive_first] at H
    have hb0 : ∀ j, constantCoeff ((![X 0, 0, X 1] : Fin 3 → MvPowerSeries (Fin 2) KK) j) = 0 := by
      intro j; fin_cases j <;> simp
    have hb : HasSubst (![X 0, 0, X 1] : Fin 3 → MvPowerSeries (Fin 2) KK) := hasSubst_of_constantCoeff_zero hb0
    have := hur_subst (Wr p) hb0 (by intro j; fin_cases j <;> simp [hur_X, hur_zero]) H
    rwa [restr _ _ _ _ (by simp) (by simp) hb0 (by rw [subst_add hb, subst_X hb, subst_X hb]; simp)
      (by rw [subst_X hb]; simp)] at this
  have h11 : Hur (Wr p) (pderiv KK 1 (pderiv KK 1 be)) := by
    have H := hur_pderiv _ (hur_pderiv _ (hur_of_simeq h.add2) 2) 1
    rw [second_deriv_additive_second] at H
    have hb0 : ∀ j, constantCoeff ((![X 0, X 1, 0] : Fin 3 → MvPowerSeries (Fin 2) KK) j) = 0 := by
      intro j; fin_cases j <;> simp
    have hb : HasSubst (![X 0, X 1, 0] : Fin 3 → MvPowerSeries (Fin 2) KK) := hasSubst_of_constantCoeff_zero hb0
    have := hur_subst (Wr p) hb0 (by intro j; fin_cases j <;> simp [hur_X, hur_zero]) H
    rwa [restr _ _ _ _ (by simp) (by simp) hb0 (by rw [subst_X hb]; simp)
      (by rw [subst_add hb, subst_X hb, subst_X hb]; simp)] at this
  have h01 : constantCoeff (pderiv KK 0 (pderiv KK 1 be)) ∈ Wr p := by
    obtain ⟨α, hα2, u, hu⟩ := hα
    have hc := hur_cc _ (hur_pderiv _ (hur_pderiv _ (hur_of_simeq (hconj α hα2)) 1) 0)
    rw [conj_dd, ← map_sub, ← hu] at hc
    have e : constantCoeff (pderiv KK 0 (pderiv KK 1 be)) =
        constantCoeff (pderiv KK 0 (pderiv KK 1 be)) * algebraMap (WW p) KK (u : WW p) *
          algebraMap (WW p) KK ((u⁻¹ : (WW p)ˣ) : WW p) := by
      rw [mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
    rw [e]
    exact (Wr p).mul_mem hc (mem_Wr p _)
  refine ⟨hcc, fun n => ?_⟩
  suffices hs : fc n * coeff n be ∈ Wr p by
    obtain ⟨y, hy⟩ := hs
    exact ⟨y, by rw [hy]; simp [fc]⟩
  by_cases hz : n 0 = 0 ∨ n 1 = 0
  · have : coeff n be = 0 := by
      by_contra hc
      have := h.ab n hc
      omega
    rw [this, mul_zero]
    exact (Wr p).zero_mem
  · push Not at hz
    by_cases h2 : 2 ≤ n 0
    · have e1 := decomp n 0 hz.1
      have hm : (n - Finsupp.single 0 1 : Fin 2 →₀ ℕ) 0 ≠ 0 := by simp; omega
      have e2 := decomp (n - Finsupp.single 0 1) 0 hm
      rw [e1, ← fc_coeff_pderiv, e2, ← fc_coeff_pderiv]
      exact h00 _
    · by_cases h2' : 2 ≤ n 1
      · have e1 := decomp n 1 hz.2
        have hm : (n - Finsupp.single 1 1 : Fin 2 →₀ ℕ) 1 ≠ 0 := by simp; omega
        have e2 := decomp (n - Finsupp.single 1 1) 1 hm
        rw [e1, ← fc_coeff_pderiv, e2, ← fc_coeff_pderiv]
        exact h11 _
      · have en : n = (0 + Finsupp.single 0 1) + Finsupp.single 1 1 := by
          ext x
          fin_cases x <;> simp <;> omega
        rw [en, ← fc_coeff_pderiv, ← fc_coeff_pderiv, fc_zero, one_mul, coeff_zero_eq_constantCoeff_apply]
        exact h01

end Conj

end Formalism.L2.KerInert.Jet

namespace Formalism.L2.KerInert.Jet

open MvPowerSeries Finset Formalism.MainNotions.G Formalism.BasicNotions Formalism.MainNotions.FormalGroupSystem

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section Transfer

variable (p : ℕ) [Fact p.Prime] (K1 : Type) [Field K1] [Algebra (K0 p) K1]

/- English proof (translation)
Rewrite using `[rename_eq_subst]`. Both sides reduce to the same expression.
-/
theorem aL_eq_rename {ι : Type} (s : ι) :
    Formalism.MainNotions.FormalGroupSystem.Pf.en_aL p K1 s = rename (fun _ : Unit => s) (Formalism.MainNotions.FormalGroupSystem.Pf.en_L p K1) := by
  rw [rename_eq_subst]
  rfl

/- English proof (translation)
Rewrite using `[Formalism.MainNotions.FormalGroupSystem.Pf.en_aL_zero]; exact IsNilpotent.zero coeff_zero d := by`. Use `d.support.finite_toSet.subset fun s hs => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq] at hs`. Rewrite `hs` using `[aL_eq_rename]`. Assume the negation of the conclusion as `hsd`.

Establish `hd : d ∉ Set.range (Finsupp.mapDomain (fun _ : Unit => s))`. Introduce and unpack `⟨u, rfl⟩`. Rewrite `hsd` using `[Finset.mem_coe, Finsupp.mem_support_iff, not_not]`. Establish `hu : u = Finsupp.single () (u ())` using `Finsupp.unique_single u`. Rewrite `hsd` using `[hu, Finsupp.mapDomain_single, Finsupp.single_eq_same]`.

Rewrite `hs` using `[hu, Finsupp.mapDomain_single, hsd, Finsupp.single_zero, coeff_zero_eq_constantCoeff_apply, constantCoeff_rename]`. Conclude with `hs (Formalism.MainNotions.FormalGroupSystem.Pf.en_L_zero p K1)`. Conclude with `hs (coeff_rename_eq_zero _ _ hd)`.
-/
theorem hasSubst_aL_any {ι : Type} : HasSubst (Formalism.MainNotions.FormalGroupSystem.Pf.en_aL p K1 : ι → MvPowerSeries ι K1) where
  const_coeff s := by rw [Formalism.MainNotions.FormalGroupSystem.Pf.en_aL_zero]; exact IsNilpotent.zero
  coeff_zero d := by
    refine d.support.finite_toSet.subset fun s hs => ?_
    simp only [Set.mem_setOf_eq] at hs
    rw [aL_eq_rename] at hs
    by_contra hsd
    have hd : d ∉ Set.range (Finsupp.mapDomain (fun _ : Unit => s)) := by
      rintro ⟨u, rfl⟩
      rw [Finset.mem_coe, Finsupp.mem_support_iff, not_not] at hsd
      have hu : u = Finsupp.single () (u ()) := Finsupp.unique_single u
      rw [hu, Finsupp.mapDomain_single, Finsupp.single_eq_same] at hsd
      rw [hu, Finsupp.mapDomain_single, hsd, Finsupp.single_zero, coeff_zero_eq_constantCoeff_apply,
        constantCoeff_rename] at hs
      exact hs (Formalism.MainNotions.FormalGroupSystem.Pf.en_L_zero p K1)
    exact hs (coeff_rename_eq_zero _ _ hd)

/- English proof (translation)
Rewrite using `[Formalism.MainNotions.FormalGroupSystem.Pf.en_inParamK_eq, Formalism.MainNotions.FormalGroupSystem.Pf.en_inParamK_eq, rename_eq_subst, rename_eq_subst, subst_comp_subst_apply (HasSubst.X_comp f) (hasSubst_aL_any p K1), subst_comp_subst_apply (Formalism.MainNotions.FormalGroupSys …`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `only [Function.comp_apply, subst_X (hasSubst_aL_any p K1)]`. Rewrite using `[aL_eq_rename, aL_eq_rename, ← rename_eq_subst, rename_rename]`.

Both sides reduce to the same expression.
-/
theorem inParamK_rename {σ ι : Type} [Finite σ] (f : σ → ι) [Filter.TendstoCofinite f]
    (F : MvPowerSeries σ K1) : inParamK p K1 (rename f F) = rename f (inParamK p K1 F) := by
  rw [Formalism.MainNotions.FormalGroupSystem.Pf.en_inParamK_eq, Formalism.MainNotions.FormalGroupSystem.Pf.en_inParamK_eq, rename_eq_subst, rename_eq_subst,
    subst_comp_subst_apply (HasSubst.X_comp f) (hasSubst_aL_any p K1),
    subst_comp_subst_apply (Formalism.MainNotions.FormalGroupSystem.Pf.en_aL_hs p K1) (HasSubst.X_comp f)]
  congr 1
  funext i
  simp only [Function.comp_apply, subst_X (hasSubst_aL_any p K1)]
  rw [aL_eq_rename, aL_eq_rename, ← rename_eq_subst, rename_rename]
  rfl

/- English proof (translation)
Use `show (∑ k ∈ (Finsupp.embDomain e x).support, (Finsupp.embDomain e x) k) = ∑ k ∈ x.support, x k`. Rewrite using `[Finsupp.support_embDomain, Finset.sum_map]`. Simplify using `[Finsupp.embDomain_apply]`.
-/
theorem degree_embDomain {σ τ : Type} (e : σ ↪ τ) (x : σ →₀ ℕ) :
    (Finsupp.embDomain e x).degree = x.degree := by
  show (∑ k ∈ (Finsupp.embDomain e x).support, (Finsupp.embDomain e x) k) = ∑ k ∈ x.support, x k
  rw [Finsupp.support_embDomain, Finset.sum_map]
  simp [Finsupp.embDomain_apply]

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[coeff_killCompl]`. Use `show ∑ k ∈ range ((Finsupp.embDomain e x).degree + 1), _ = ∑ k ∈ range (x.degree + 1), _`. Rewrite using `[degree_embDomain]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[← map_pow, coeff_killCompl]`.
-/
theorem killCompl_expS {σ τ : Type} (e : σ ↪ τ) (G : MvPowerSeries τ (K0 p)) :
    killCompl e (expS p G) = expS p (killCompl e G) := by
  ext x
  rw [coeff_killCompl]
  show ∑ k ∈ range ((Finsupp.embDomain e x).degree + 1), _ = ∑ k ∈ range (x.degree + 1), _
  rw [degree_embDomain]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← map_pow, coeff_killCompl]

/- English proof (translation)
Unfold `sub2`. Rewrite using `[rename_eq_subst, subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (cc2 hu hw)) (HasSubst.X_comp f)]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Apply the tactic sequence `fin_cases j <;> simp [← rename_eq_subst]`.
-/
theorem rename_substitute_two_series {τ : Type} (f : Fin 2 → τ) [Filter.TendstoCofinite f] (be : MvPowerSeries (Fin 2) (K0 p))
    {u w : MvPowerSeries (Fin 2) (K0 p)} (hu : constantCoeff u = 0) (hw : constantCoeff w = 0) :
    rename f (sub2 p be u w) = sub2 p be (rename f u) (rename f w) := by
  unfold sub2
  rw [rename_eq_subst, subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (cc2 hu hw)) (HasSubst.X_comp f)]
  congr 1
  funext j
  fin_cases j <;> simp [← rename_eq_subst]

/- English proof (translation)
Conclude with `h.conj α hα2`.
-/
theorem conj_frobenius_two_variables {be : MvPowerSeries (Fin 2) (K0 p)} (h : BeProp p be) (α : WW p) (hα2 : (sigW p)^[2] α = α) :
    Simeq p (sub2 p be (C (algebraMap (WW p) (K0 p) α) * X 0) (X 1) : MvPowerSeries (Fin 2) (K0 p))
      (sub2 p be (X 0) (C (algebraMap (WW p) (K0 p) (sigW p α)) * X 1)) := by
  exact h.conj α hα2

/- English proof (translation)
Establish `hp1 : 1 < p` using `(Fact.out : p.Prime).one_lt`. Set `_ : Fintype (GaloisField p 2)` to `Fintype.ofFinite _`. Establish `hcard : Fintype.card (GaloisField p 2) = p ^ 2`. Rewrite using `[← Nat.card_eq_fintype_card]; exact GaloisField.card p 2 (by norm_num)`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x : GaloisField p 2, x ^ p ≠ x := by`.

Assume the negation of the conclusion as `hall`. Use `push Not at hall`. Establish `hpoly : (Polynomial.X ^ p - Polynomial.X : Polynomial (GaloisField p 2)) ≠ 0` using `FiniteField.X_pow_card_sub_X_ne_zero _ hp1`. Establish `hle` using `Polynomial.card_le_degree_of_subset_roots (p := Polynomial.X ^ p - Polynomial.X) (Z := (Finset.univ : Finset (GaloisField p 2))) (fun y _ => by`. Rewrite using `[Polynomial.mem_roots hpoly]`.

Simplify using `[hall y])`. Rewrite `hle` using `[Finset.card_univ, hcard, FiniteField.X_pow_card_sub_X_natDegree_eq _ hp1]`. Establish `: p < p ^ 2` using `by nlinarith`. Use linear arithmetic over natural numbers and integers. Set `φ : GaloisField p 2 →ₐ[ZMod p] kb p` to `IsAlgClosed.lift`.

Use `set ζ : kb p := φ x`. Establish `hζ2 : ζ ^ (p ^ 2) = ζ`. Rewrite using `[← map_pow, ← hcard, FiniteField.pow_card]`. Establish `hζ1 : ζ ^ p ≠ ζ`. Introduce `h`.

Apply `hx` to reduce the goal to its premises. Apply `φ.toRingHom.injective` to reduce the goal to its premises. Simplify using `using h`. Establish `hs : ∀ y : kb p, sigW p (WittVector.teichmuller p y) = WittVector.teichmuller p (y ^ p)`. Introduce `y`.

Use extensionality with `n`. Rewrite using `[sigW, WittVector.coeff_frobenius_charP]`. Break down `n with _ | n` into its components or cases. Rewrite using `[WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero]`. Rewrite using `[WittVector.teichmuller_coeff_pos p _ (n + 1) (Nat.succ_pos n), WittVector.teichmuller_coeff_pos p _ (n + 1) (Nat.succ_pos n), zero_pow (Fact.out : p.Prime).ne_zero]`.

Use `⟨WittVector.teichmuller p ζ, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Function.iterate_succ_apply, Function.iterate_one, hs, hs, ← pow_mul, ← sq, hζ2]`. Apply `WittVector.isUnit_of_coeff_zero_ne_zero` to reduce the goal to its premises. Establish `e : (WittVector.teichmuller p ζ - sigW p (WittVector.teichmuller p ζ)).coeff 0 = (WittVector.teichmuller p ζ).coeff 0 - (sigW p (WittVector.teichmuller p ζ)).coeff 0`. Simplify `map_sub WittVector.constantCoeff (WittVector.teichmuller p ζ) (sigW p (WittVector.teichmuller p ζ))` using `[WittVector.constantCoeff_apply]`.

Rewrite using `[e, hs, WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero]`. Conclude with `sub_ne_zero.mpr (Ne.symm hζ1)`.
-/
theorem exists_alpha : ∃ α : WW p, (sigW p)^[2] α = α ∧ IsUnit (α - sigW p α) := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  let _ : Fintype (GaloisField p 2) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField p 2) = p ^ 2 := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card p 2 (by norm_num)
  obtain ⟨x, hx⟩ : ∃ x : GaloisField p 2, x ^ p ≠ x := by
    by_contra hall
    push Not at hall
    have hpoly : (Polynomial.X ^ p - Polynomial.X : Polynomial (GaloisField p 2)) ≠ 0 :=
      FiniteField.X_pow_card_sub_X_ne_zero _ hp1
    have hle := Polynomial.card_le_degree_of_subset_roots (p := Polynomial.X ^ p - Polynomial.X)
      (Z := (Finset.univ : Finset (GaloisField p 2))) (fun y _ => by
        rw [Polynomial.mem_roots hpoly]
        simp [hall y])
    rw [Finset.card_univ, hcard, FiniteField.X_pow_card_sub_X_natDegree_eq _ hp1] at hle
    have : p < p ^ 2 := by nlinarith
    omega
  let φ : GaloisField p 2 →ₐ[ZMod p] kb p := IsAlgClosed.lift
  set ζ : kb p := φ x
  have hζ2 : ζ ^ (p ^ 2) = ζ := by
    rw [← map_pow, ← hcard, FiniteField.pow_card]
  have hζ1 : ζ ^ p ≠ ζ := by
    intro h
    apply hx
    apply φ.toRingHom.injective
    simpa using h
  have hs : ∀ y : kb p, sigW p (WittVector.teichmuller p y) = WittVector.teichmuller p (y ^ p) := by
    intro y
    ext n
    rw [sigW, WittVector.coeff_frobenius_charP]
    rcases n with _ | n
    · rw [WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero]
    · rw [WittVector.teichmuller_coeff_pos p _ (n + 1) (Nat.succ_pos n), WittVector.teichmuller_coeff_pos p _ (n + 1) (Nat.succ_pos n),
        zero_pow (Fact.out : p.Prime).ne_zero]
  refine ⟨WittVector.teichmuller p ζ, ?_, ?_⟩
  · rw [Function.iterate_succ_apply, Function.iterate_one, hs, hs, ← pow_mul, ← sq, hζ2]
  · apply WittVector.isUnit_of_coeff_zero_ne_zero
    have e : (WittVector.teichmuller p ζ - sigW p (WittVector.teichmuller p ζ)).coeff 0 =
        (WittVector.teichmuller p ζ).coeff 0 - (sigW p (WittVector.teichmuller p ζ)).coeff 0 := by
      simpa [WittVector.constantCoeff_apply] using
        map_sub WittVector.constantCoeff (WittVector.teichmuller p ζ) (sigW p (WittVector.teichmuller p ζ))
    rw [e, hs, WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero]
    exact sub_ne_zero.mpr (Ne.symm hζ1)

end Transfer

/- English proof (translation)
Unfold `BeJetOfProp`. Introduce `p _ be h`. Conclude with `beJet_of_prop_conj (exists_alpha p) h (fun α hα => conj_frobenius_two_variables p h α hα)`.
-/
theorem beJet_of_prop : BeJetOfProp := by
  unfold BeJetOfProp
  intro p _ be h
  exact beJet_of_prop_conj (exists_alpha p) h (fun α hα => conj_frobenius_two_variables p h α hα)

end Formalism.L2.KerInert.Jet

namespace Formalism.L2.KerInert.Jet

/- English proof (translation)
Unfold `Adm11OfBeProp`. Introduce `D p _ X Y h`. Conclude with `adm11OfIntegralJets D p X Y (beJet_of_prop p Y.be h)`.
-/
theorem adm11OfBeProp : Adm11OfBeProp := by
  unfold Adm11OfBeProp
  intro D p _ X Y h
  exact adm11OfIntegralJets D p X Y (beJet_of_prop p Y.be h)

end Formalism.L2.KerInert.Jet
