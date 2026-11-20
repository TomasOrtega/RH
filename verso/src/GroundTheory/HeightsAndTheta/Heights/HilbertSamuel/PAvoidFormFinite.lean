import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsAvoidFormFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreRepresentatives
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

namespace AvoidFormFinite

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def bdeg (m : (Σ k, ι k) →₀ ℕ) : K → ℕ := fun k => ∑ i, m ⟨k, i⟩

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `[bdeg, Finset.sum_add_distrib]`.
-/
theorem bdeg_add (m n : (Σ k, ι k) →₀ ℕ) : bdeg (m + n) = bdeg m + bdeg n := by
  funext k
  simp [bdeg, Finset.sum_add_distrib]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h m hm`. Use function extensionality and compare the values at `k`. Conclude with `h m (mem_support_iff.mpr hm) k`. Introduce `h m hm k`.

Conclude with `congrFun (h m (mem_support_iff.mp hm)) k`.
-/
theorem isMultiHomog_iff {s : MRingOver ℂ ι} {a : K → ℕ} :
    IsMultiHomog s a ↔ ∀ m, coeff m s ≠ 0 → bdeg m = a := by
  constructor
  · intro h m hm
    funext k
    exact h m (mem_support_iff.mpr hm) k
  · intro h m hm k
    exact congrFun (h m (mem_support_iff.mp hm)) k

/- English proof (translation)
Use function extensionality and compare the values at `k`. Conclude with `hs m hm k`.
-/
theorem bdeg_of_mem {s : MRingOver ℂ ι} {a : K → ℕ} (hs : IsMultiHomog s a) {m : (Σ k, ι k) →₀ ℕ}
    (hm : m ∈ s.support) : bdeg m = a := by
  funext k
  exact hs m hm k

/- English proof (translation)
Rewrite using `[isMultiHomog_iff]`. Introduce `n hn`. Rewrite `hn` using `[coeff_monomial]`. Use `split_ifs at hn with h`. Rewrite using `[h]`.

Conclude with `absurd rfl hn`.
-/
theorem isMultiHomog_monomial (m : (Σ k, ι k) →₀ ℕ) (c : ℂ) :
    IsMultiHomog (monomial m c : MRingOver ℂ ι) (bdeg m) := by
  classical
  rw [isMultiHomog_iff]
  intro n hn
  rw [coeff_monomial] at hn
  split_ifs at hn with h
  · rw [h]
  · exact absurd rfl hn

/- English proof (translation)
Rewrite `hf`, `hg`, the goal using `[isMultiHomog_iff]`. Introduce `m hm`. Rewrite `hm` using `[coeff_mul]`. Take `⟨x, hx, hx0⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hm`. Rewrite `hx` using `[Finset.HasAntidiagonal.mem_antidiagonal]`.

Rewrite using `[← hx, bdeg_add, hf x.1 (left_ne_zero_of_mul hx0), hg x.2 (right_ne_zero_of_mul hx0)]`.
-/
theorem isMultiHomog_mul {f g : MRingOver ℂ ι} {a b : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by
  classical
  rw [isMultiHomog_iff] at hf hg ⊢
  intro m hm
  rw [coeff_mul] at hm
  obtain ⟨x, hx, hx0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  rw [← hx, bdeg_add, hf x.1 (left_ne_zero_of_mul hx0), hg x.2 (right_ne_zero_of_mul hx0)]

/- English proof (translation)
Rewrite using `[isMultiHomog_iff]`. Introduce `m hm`. Rewrite `hm` using `[coeff_one]`. Use `split_ifs at hm with h`. Substitute `h` using the available equality.

Use function extensionality and compare the values at `k`. Simplify using `[bdeg]`. Conclude with `absurd rfl hm`.
-/
theorem isMultiHomog_one : IsMultiHomog (1 : MRingOver ℂ ι) 0 := by
  classical
  rw [isMultiHomog_iff]
  intro m hm
  rw [coeff_one] at hm
  split_ifs at hm with h
  · subst h
    funext k
    simp [bdeg]
  · exact absurd rfl hm

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using isMultiHomog_one`. Consider the case `succ n ih`. Rewrite using `[pow_succ, succ_nsmul]`. Conclude with `isMultiHomog_mul ih hf`.
-/
theorem isMultiHomog_pow {f : MRingOver ℂ ι} {a : K → ℕ} (hf : IsMultiHomog f a) (n : ℕ) :
    IsMultiHomog (f ^ n) (n • a) := by
  induction n with
  | zero => simpa using isMultiHomog_one
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact isMultiHomog_mul ih hf

/- English proof (translation)
Rewrite `hf`, `hg`, the goal using `[isMultiHomog_iff]`. Introduce `m hm`. Rewrite `hm` using `[coeff_add]`. Distinguish the cases in `h0 : coeff m f = 0`. Rewrite `hm` using `[h0, zero_add]`.

Conclude with `hg m hm`. Conclude with `hf m h0`.
-/
theorem isMultiHomog_add {f g : MRingOver ℂ ι} {a : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g a) : IsMultiHomog (f + g) a := by
  rw [isMultiHomog_iff] at hf hg ⊢
  intro m hm
  rw [coeff_add] at hm
  by_cases h0 : coeff m f = 0
  · rw [h0, zero_add] at hm
    exact hg m hm
  · exact hf m h0

/- English proof (translation)
Introduce `m hm`. Simplify using `at hm`.
-/
theorem isMultiHomog_zero (a : K → ℕ) : IsMultiHomog (0 : MRingOver ℂ ι) a := by
  intro m hm
  simp at hm

/- English proof (translation)
Rewrite `hf`, the goal using `[isMultiHomog_iff]`. Introduce `m hm`. Rewrite `hm` using `[coeff_C_mul]`. Conclude with `hf m (right_ne_zero_of_mul hm)`.
-/
theorem isMultiHomog_C_mul {f : MRingOver ℂ ι} {a : K → ℕ} (hf : IsMultiHomog f a) (c : ℂ) :
    IsMultiHomog (C c * f) a := by
  rw [isMultiHomog_iff] at hf ⊢
  intro m hm
  rw [coeff_C_mul] at hm
  exact hf m (right_ne_zero_of_mul hm)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using isMultiHomog_zero a`. Consider the case `@insert j s hj ih`. Rewrite using `[Finset.sum_insert hj]`. Conclude with `isMultiHomog_add (h j (Finset.mem_insert_self _ _)) (ih fun x hx => h x (Finset.mem_insert_of_mem hx))`.
-/
theorem isMultiHomog_sum {α : Type} (s : Finset α) (f : α → MRingOver ℂ ι) {a : K → ℕ}
    (h : ∀ j ∈ s, IsMultiHomog (f j) a) : IsMultiHomog (∑ j ∈ s, f j) a := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isMultiHomog_zero a
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact isMultiHomog_add (h j (Finset.mem_insert_self _ _))
      (ih fun x hx => h x (Finset.mem_insert_of_mem hx))

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using isMultiHomog_one`. Consider the case `@insert j s hj ih`. Rewrite using `[Finset.prod_insert hj, Finset.sum_insert hj]`. Conclude with `isMultiHomog_mul (h j (Finset.mem_insert_self _ _)) (ih fun x hx => h x (Finset.mem_insert_of_mem hx))`.
-/
theorem isMultiHomog_prod {α : Type} (s : Finset α) (f : α → MRingOver ℂ ι) (a : α → K → ℕ)
    (h : ∀ j ∈ s, IsMultiHomog (f j) (a j)) : IsMultiHomog (∏ j ∈ s, f j) (∑ j ∈ s, a j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isMultiHomog_one
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact isMultiHomog_mul (h j (Finset.mem_insert_self _ _))
      (ih fun x hx => h x (Finset.mem_insert_of_mem hx))

open Classical in

def wt (p : Σ k, ι k) : K → ℕ := fun k => if p.1 = k then 1 else 0

/- English proof (translation)
Use function extensionality and compare the values at `k`. Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype m (fun i c => c • wt i) (fun _ => zero_smul _ _)]`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, wt, bdeg]`. Rewrite using `[Fintype.sum_sigma, Finset.sum_eq_single k (fun b _ hb => by simp [hb]) (by simp)]`. Simplify using the standard rewrite rules.
-/
theorem weight_wt (m : (Σ k, ι k) →₀ ℕ) : Finsupp.weight wt m = bdeg m := by
  classical
  funext k
  rw [Finsupp.weight_apply, Finsupp.sum_fintype m (fun i c => c • wt i) (fun _ => zero_smul _ _)]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, wt, bdeg]
  rw [Fintype.sum_sigma, Finset.sum_eq_single k (fun b _ hb => by simp [hb]) (by simp)]
  simp

def cmp (D : K → ℕ) : MRingOver ℂ ι →ₗ[ℂ] MRingOver ℂ ι := weightedHomogeneousComponent wt D

/- English proof (translation)
Rewrite using `[cmp, coeff_weightedHomogeneousComponent, weight_wt]`.
-/
theorem coeff_cmp (D : K → ℕ) (p : MRingOver ℂ ι) (m : (Σ k, ι k) →₀ ℕ) :
    coeff m (cmp D p) = if bdeg m = D then coeff m p else 0 := by
  classical
  rw [cmp, coeff_weightedHomogeneousComponent, weight_wt]

/- English proof (translation)
Rewrite using `[isMultiHomog_iff]`. Introduce `m hm`. Rewrite `hm` using `[coeff_cmp]`. Assume the negation of the conclusion as `h`. Conclude with `hm (if_neg h)`.
-/
theorem isMultiHomog_cmp (D : K → ℕ) (p : MRingOver ℂ ι) : IsMultiHomog (cmp D p) D := by
  rw [isMultiHomog_iff]
  intro m hm
  rw [coeff_cmp] at hm
  by_contra h
  exact hm (if_neg h)

/- English proof (translation)
Rewrite `hh` using `[isMultiHomog_iff]`. Use extensionality with `m`. Rewrite using `[coeff_cmp]`. Distinguish the cases in `hm : coeff m h = 0`. Apply the tactic sequence `split_ifs <;> simp [hm]`.

Distinguish the cases in `hb : b = D`. Substitute `hb` using the available equality. Simplify using `[hh m hm]`. Rewrite using `[if_neg hb, coeff_zero, if_neg (by rw [hh m hm]; exact hb)]`.
-/
theorem cmp_of_homog {h : MRingOver ℂ ι} {b : K → ℕ} (hh : IsMultiHomog h b) (D : K → ℕ) :
    cmp D h = if b = D then h else 0 := by
  rw [isMultiHomog_iff] at hh
  ext m
  rw [coeff_cmp]
  by_cases hm : coeff m h = 0
  · split_ifs <;> simp [hm]
  · by_cases hb : b = D
    · subst hb
      simp [hh m hm]
    · rw [if_neg hb, coeff_zero, if_neg (by rw [hh m hm]; exact hb)]

open Classical in

/- English proof (translation)
Rewrite `hq` using `[isMultiHomog_iff]`. Use extensionality with `m`. Rewrite using `[coeff_cmp]`. Apply the tactic sequence `by_cases hdD : d ≤ D <;> by_cases hm : bdeg m = D <;> simp only [hdD, hm, if_true, if_false]`. Rewrite using `[coeff_mul, coeff_mul]`.

Use `Finset.sum_congr rfl fun x hx => ?_` and prove the remaining obligations. Rewrite using `[coeff_cmp]`. Distinguish the cases in `hq0 : coeff x.2 q = 0`. Simplify using `[hq0]`. Rewrite `hx` using `[Finset.HasAntidiagonal.mem_antidiagonal]`.

Establish `h2` using `hq x.2 hq0`. Rewrite using `[if_pos]`. Use function extensionality and compare the values at `k`. Establish `h3` using `congrFun hm k`. Establish `h4` using `hdD k`.

Rewrite `h3` using `[← hx, bdeg_add, h2]`. Simplify using `only [Pi.add_apply] at h3`. Simplify using `only [Pi.sub_apply]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[coeff_mul]`.

Use `symm`. Use `Finset.sum_eq_zero fun x hx => ?_` and prove the remaining obligations. Rewrite using `[coeff_cmp]`. Distinguish the cases in `hq0 : coeff x.2 q = 0`. Simplify using `[hq0]`.

Rewrite `hx` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Establish `h2` using `hq x.2 hq0`. Rewrite using `[if_neg, zero_mul]`. Introduce `h1`. Apply `hm` to reduce the goal to its premises.

Use function extensionality and compare the values at `k`. Establish `h3` using `congrFun h1 k`. Establish `h4` using `hdD k`. Rewrite using `[← hx, bdeg_add, h2]`. Simplify using `only [Pi.add_apply, Pi.sub_apply] at h3 ⊢`.

Rewrite using `[h3]`. Conclude with `Nat.sub_add_cancel h4`. Rewrite using `[coeff_zero, coeff_mul]`. Use `Finset.sum_eq_zero fun x hx => ?_` and prove the remaining obligations. Distinguish the cases in `hq0 : coeff x.2 q = 0`.

Simplify using `[hq0]`. It suffices to derive a contradiction. Rewrite `hx` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Establish `h2` using `hq x.2 hq0`. Apply `hdD` to reduce the goal to its premises.

Introduce `k`. Establish `h3` using `congrFun hm k`. Rewrite `h3` using `[← hx, bdeg_add, h2]`. Simplify using `only [Pi.add_apply] at h3`. Rewrite using `[← h3]`.

Conclude with `Nat.le_add_left _ _`. Rewrite using `[coeff_zero]`.
-/
theorem cmp_mul {q : MRingOver ℂ ι} {d : K → ℕ} (hq : IsMultiHomog q d) (D : K → ℕ)
    (p : MRingOver ℂ ι) : cmp D (p * q) = if d ≤ D then cmp (D - d) p * q else 0 := by
  classical
  rw [isMultiHomog_iff] at hq
  ext m
  rw [coeff_cmp]
  by_cases hdD : d ≤ D <;> by_cases hm : bdeg m = D <;> simp only [hdD, hm, if_true, if_false]
  · rw [coeff_mul, coeff_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [coeff_cmp]
    by_cases hq0 : coeff x.2 q = 0
    · simp [hq0]
    · rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      have h2 := hq x.2 hq0
      rw [if_pos]
      funext k
      have h3 := congrFun hm k
      have h4 := hdD k
      rw [← hx, bdeg_add, h2] at h3
      simp only [Pi.add_apply] at h3
      simp only [Pi.sub_apply]
      omega
  · rw [coeff_mul]
    symm
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [coeff_cmp]
    by_cases hq0 : coeff x.2 q = 0
    · simp [hq0]
    · rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      have h2 := hq x.2 hq0
      rw [if_neg, zero_mul]
      intro h1
      apply hm
      funext k
      have h3 := congrFun h1 k
      have h4 := hdD k
      rw [← hx, bdeg_add, h2]
      simp only [Pi.add_apply, Pi.sub_apply] at h3 ⊢
      rw [h3]
      exact Nat.sub_add_cancel h4
  · rw [coeff_zero, coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    by_cases hq0 : coeff x.2 q = 0
    · simp [hq0]
    · exfalso
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      have h2 := hq x.2 hq0
      apply hdD
      intro k
      have h3 := congrFun hm k
      rw [← hx, bdeg_add, h2] at h3
      simp only [Pi.add_apply] at h3
      rw [← h3]
      exact Nat.le_add_left _ _
  · rw [coeff_zero]

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Introduce `D`. Take `⟨b, hb⟩` from `hS x hx`. Rewrite using `[cmp_of_homog hb]`.

Use `split_ifs`. Conclude with `hz x hx`. Simplify using the standard rewrite rules. Consider the case `zero => intro D`. Simplify using the standard rewrite rules.

Consider the case `add x y _ _ hx hy => intro D`. Rewrite using `[map_add, map_add, hx, hy, add_zero]`. Consider the case `smul a x _ hx`. Introduce `D`. Rewrite using `[smul_eq_mul, as_sum a, Finset.sum_mul, map_sum, map_sum]`.

Use `Finset.sum_eq_zero fun ν _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm, cmp_mul (isMultiHomog_monomial ν _)]`. Use `split_ifs`. Rewrite using `[map_mul, hx, zero_mul]`. Simplify using the standard rewrite rules.
-/
theorem eval_cmp_eq_zero {S : Set (MRingOver ℂ ι)} (hS : ∀ s ∈ S, ∃ a, IsMultiHomog s a)
    {z : (Σ k, ι k) → ℂ} (hz : ∀ s ∈ S, eval z s = 0) {x : MRingOver ℂ ι} (hx : x ∈ Ideal.span S) :
    ∀ D : K → ℕ, eval z (cmp D x) = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    intro D
    obtain ⟨b, hb⟩ := hS x hx
    rw [cmp_of_homog hb]
    split_ifs
    · exact hz x hx
    · simp
  | zero => intro D; simp
  | add x y _ _ hx hy => intro D; rw [map_add, map_add, hx, hy, add_zero]
  | smul a x _ hx =>
    intro D
    rw [smul_eq_mul, as_sum a, Finset.sum_mul, map_sum, map_sum]
    refine Finset.sum_eq_zero fun ν _ => ?_
    rw [mul_comm, cmp_mul (isMultiHomog_monomial ν _)]
    split_ifs
    · rw [map_mul, hx, zero_mul]
    · simp

open Classical in

def spike (j : ∀ k, ι k) (f : K → ℕ) : (Σ k, ι k) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun p => if p.2 = j p.1 then f p.1 else 0)

open Classical in
/- English proof (translation)
Simplify using `only [spike, Finsupp.coe_equivFunOnFinite_symm]`.
-/
theorem spike_apply (j : ∀ k, ι k) (f : K → ℕ) (p : Σ k, ι k) :
    spike j f p = if p.2 = j p.1 then f p.1 else 0 := by
  classical
  simp only [spike, Finsupp.coe_equivFunOnFinite_symm]

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `[bdeg, spike_apply]`.
-/
theorem bdeg_spike (j : ∀ k, ι k) (f : K → ℕ) : bdeg (spike j f) = f := by
  classical
  funext k
  simp [bdeg, spike_apply]

/- English proof (translation)
Rewrite using `[eval_monomial, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_eq_single (j k) (fun i _ hi => by simp [spike_apply, hi]) (by simp)]`. Simplify using `[spike_apply]`.
-/
theorem eval_spike (j : ∀ k, ι k) (f : K → ℕ) (z : (Σ k, ι k) → ℂ) :
    eval z (monomial (spike j f) 1) = ∏ k, z ⟨k, j k⟩ ^ f k := by
  classical
  rw [eval_monomial, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_eq_single (j k) (fun i _ hi => by simp [spike_apply, hi]) (by simp)]
  simp [spike_apply]

/- English proof (translation)
Establish `key : ∀ c : (∀ k, ι k), ∃ n : ℕ, (monomial (spike c (fun _ => 1)) (1 : ℂ)) ^ n ∈ Ideal.span (insert G S)`. Introduce `c`. Establish `hmem : monomial (spike c (fun _ => 1)) (1 : ℂ) ∈ vanishingIdeal ℂ (zeroLocus ℂ (Ideal.span (insert G S)))`. Rewrite using `[mem_vanishingIdeal_iff]`. Introduce `x hx`.

Rewrite `hx` using `[mem_zeroLocus_iff]`. Establish `hxJ : ∀ p ∈ Ideal.span (insert G S), eval x p = 0` using `fun p hp => by`. Simplify `hx p hp` using `[coe_aeval_eq_eval]`. Establish `hG` using `hxJ G (Ideal.subset_span (Set.mem_insert _ _))`. Establish `hS : ∀ s ∈ S, eval x s = 0` using `fun s hs => hxJ s (Ideal.subset_span (Set.mem_insert_of_mem _ hs))`.

Establish `hnc : ¬ ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0` using `fun hc => hcone x hc hS hG`. Use `push_neg at hnc`. Take `⟨k, hk⟩` from `hnc`. Establish `h0 : eval x (monomial (spike c (fun _ => 1)) (1 : ℂ)) = 0`. Rewrite using `[eval_spike]`.

Conclude with `Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])`. Simplify `h0` using `[coe_aeval_eq_eval]`. Rewrite `hmem` using `[vanishingIdeal_zeroLocus_eq_radical]`. Conclude with `hmem`. Use `choose n hn using key`.

Use `⟨∑ c, n c, fun c => ?_⟩` and prove the remaining obligations. Establish `hle : n c ≤ ∑ c, n c` using `Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)`. Establish `heq : monomial (spike c (fun _ => ∑ c, n c)) (1 : ℂ) = (monomial (spike c (fun _ => 1)) 1) ^ n c * (monomial (spike c (fun _ => 1)) 1) ^ (∑ c, n c - n c)`. Establish `hexp : (∑ c, n c) • spike c (fun _ => 1) = spike c (fun _ => ∑ c, n c)`. Use extensionality with `p`.

Rewrite using `[Finsupp.smul_apply, spike_apply, spike_apply, smul_eq_mul]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[← pow_add, Nat.add_sub_cancel' hle, monomial_pow, one_pow, hexp]`. Rewrite using `[heq]`. Conclude with `Ideal.mul_mem_right _ _ (hn c)`.
-/
theorem exists_pow_mem {S : Set (MRingOver ℂ ι)} {G : MRingOver ℂ ι}
    (hcone : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (∀ s ∈ S, eval z s = 0) → eval z G ≠ 0) :
    ∃ r : ℕ, ∀ c : (∀ k, ι k), monomial (spike c (fun _ => r)) (1 : ℂ) ∈ Ideal.span (insert G S) := by
  classical
  have key : ∀ c : (∀ k, ι k), ∃ n : ℕ,
      (monomial (spike c (fun _ => 1)) (1 : ℂ)) ^ n ∈ Ideal.span (insert G S) := by
    intro c
    have hmem : monomial (spike c (fun _ => 1)) (1 : ℂ) ∈
        vanishingIdeal ℂ (zeroLocus ℂ (Ideal.span (insert G S))) := by
      rw [mem_vanishingIdeal_iff]
      intro x hx
      rw [mem_zeroLocus_iff] at hx
      have hxJ : ∀ p ∈ Ideal.span (insert G S), eval x p = 0 := fun p hp => by
        simpa [coe_aeval_eq_eval] using hx p hp
      have hG := hxJ G (Ideal.subset_span (Set.mem_insert _ _))
      have hS : ∀ s ∈ S, eval x s = 0 := fun s hs =>
        hxJ s (Ideal.subset_span (Set.mem_insert_of_mem _ hs))
      have hnc : ¬ ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0 := fun hc => hcone x hc hS hG
      push_neg at hnc
      obtain ⟨k, hk⟩ := hnc
      have h0 : eval x (monomial (spike c (fun _ => 1)) (1 : ℂ)) = 0 := by
        rw [eval_spike]
        exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])
      simpa [coe_aeval_eq_eval] using h0
    rw [vanishingIdeal_zeroLocus_eq_radical] at hmem
    exact hmem
  choose n hn using key
  refine ⟨∑ c, n c, fun c => ?_⟩
  have hle : n c ≤ ∑ c, n c := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
  have heq : monomial (spike c (fun _ => ∑ c, n c)) (1 : ℂ) =
      (monomial (spike c (fun _ => 1)) 1) ^ n c * (monomial (spike c (fun _ => 1)) 1) ^ (∑ c, n c - n c) := by
    have hexp : (∑ c, n c) • spike c (fun _ => 1) = spike c (fun _ => ∑ c, n c) := by
      ext p
      rw [Finsupp.smul_apply, spike_apply, spike_apply, smul_eq_mul]
      split_ifs <;> simp
    rw [← pow_add, Nat.add_sub_cancel' hle, monomial_pow, one_pow, hexp]
  rw [heq]
  exact Ideal.mul_mem_right _ _ (hn c)

/- English proof (translation)
Take `⟨r, hr⟩` from `exists_pow_mem hcone`. Use `⟨r * ∑ k, Fintype.card (ι k), fun M hM μ hμ => ?_⟩` and prove the remaining obligations. Establish `hc : ∀ k, ∃ i, r ≤ μ ⟨k, i⟩`. Introduce `k`. Assume the negation of the conclusion as `hne`.

Use `push_neg at hne`. Establish `h1 : bdeg μ k ≤ Fintype.card (ι k) * r`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : Fintype.card (ι k) ≤ ∑ k, Fintype.card (ι k)` using `Finset.single_le_sum (f := fun k => Fintype.card (ι k)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)`. Establish `h3 : bdeg μ k = (M + 1) * e k` using `by rw [hμ]; simp`.

Establish `h4` using `he k`. Establish `h5 : Fintype.card (ι k) * r ≤ (∑ k, Fintype.card (ι k)) * r` using `Nat.mul_le_mul_right r h2`. Establish `h6 : (M + 1) * 1 ≤ (M + 1) * e k` using `Nat.mul_le_mul_left (M + 1) h4`. Use the polynomial consequences of the given equalities and inequalities. Use `choose c hc using hc`.

Establish `hle : spike c (fun _ => r) ≤ μ`. Rewrite using `[Finsupp.le_def]`. Introduce and unpack `⟨k, i⟩`. Rewrite using `[spike_apply]`. Use `split_ifs with h`.

Simplify using `only at h`. Substitute `h` using the available equality. Conclude with `hc k`. Conclude with `Nat.zero_le _`. Establish `hmem : monomial μ (1 : ℂ) ∈ Ideal.span (insert G S)`.

Establish `: monomial μ (1 : ℂ) = monomial (spike c (fun _ => r)) 1 * monomial (μ - spike c (fun _ => r)) 1`. Rewrite using `[monomial_mul, mul_one, add_tsub_cancel_of_le hle]`. Rewrite using `[this]`. Conclude with `Ideal.mul_mem_right _ _ (hr c)`. Take `⟨a, s, hs, hμa⟩` from `Ideal.mem_span_insert.1 hmem`.

Establish `heD : e ≤ (M + 1) • e` using `fun k => by`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hDe : (M + 1) • e - e = M • e`. Use function extensionality and compare the values at `k`.

Simplify using `only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[add_mul, one_mul, Nat.add_sub_cancel]`. Use `⟨cmp (M • e) a, isMultiHomog_cmp _ _, fun z hz => ?_⟩` and prove the remaining obligations. Establish `h1 : monomial μ (1 : ℂ) = cmp ((M + 1) • e) (a * G) + cmp ((M + 1) • e) s`. Rewrite using `[← map_add, ← hμa, cmp_of_homog (isMultiHomog_monomial μ 1), if_pos hμ]`.

Rewrite using `[h1, map_add, cmp_mul hG, if_pos heD, hDe, map_mul, eval_cmp_eq_zero hS hz hs, add_zero]`.
-/
theorem rel_one {S : Set (MRingOver ℂ ι)} {G : MRingOver ℂ ι} {e : K → ℕ}
    (hS : ∀ s ∈ S, ∃ a, IsMultiHomog s a) (hG : IsMultiHomog G e) (he : ∀ k, 1 ≤ e k)
    (hcone : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (∀ s ∈ S, eval z s = 0) → eval z G ≠ 0) :
    ∃ N₀ : ℕ, ∀ M : ℕ, N₀ ≤ M → ∀ μ : (Σ k, ι k) →₀ ℕ, bdeg μ = (M + 1) • e →
      ∃ h : MRingOver ℂ ι, IsMultiHomog h (M • e) ∧
        ∀ z : (Σ k, ι k) → ℂ, (∀ s ∈ S, eval z s = 0) → eval z (monomial μ (1 : ℂ)) = eval z h * eval z G := by
  classical
  obtain ⟨r, hr⟩ := exists_pow_mem hcone
  refine ⟨r * ∑ k, Fintype.card (ι k), fun M hM μ hμ => ?_⟩
  have hc : ∀ k, ∃ i, r ≤ μ ⟨k, i⟩ := by
    intro k
    by_contra hne
    push_neg at hne
    have h1 : bdeg μ k ≤ Fintype.card (ι k) * r := by
      calc bdeg μ k = ∑ i, μ ⟨k, i⟩ := rfl
        _ ≤ ∑ _i : ι k, r := Finset.sum_le_sum fun i _ => (hne i).le
        _ = Fintype.card (ι k) * r := by simp
    have h2 : Fintype.card (ι k) ≤ ∑ k, Fintype.card (ι k) :=
      Finset.single_le_sum (f := fun k => Fintype.card (ι k)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    have h3 : bdeg μ k = (M + 1) * e k := by rw [hμ]; simp
    have h4 := he k
    have h5 : Fintype.card (ι k) * r ≤ (∑ k, Fintype.card (ι k)) * r := Nat.mul_le_mul_right r h2
    have h6 : (M + 1) * 1 ≤ (M + 1) * e k := Nat.mul_le_mul_left (M + 1) h4
    nlinarith
  choose c hc using hc
  have hle : spike c (fun _ => r) ≤ μ := by
    rw [Finsupp.le_def]
    rintro ⟨k, i⟩
    rw [spike_apply]
    split_ifs with h
    · simp only at h
      subst h
      exact hc k
    · exact Nat.zero_le _
  have hmem : monomial μ (1 : ℂ) ∈ Ideal.span (insert G S) := by
    have : monomial μ (1 : ℂ) = monomial (spike c (fun _ => r)) 1 * monomial (μ - spike c (fun _ => r)) 1 := by
      rw [monomial_mul, mul_one, add_tsub_cancel_of_le hle]
    rw [this]
    exact Ideal.mul_mem_right _ _ (hr c)
  obtain ⟨a, s, hs, hμa⟩ := Ideal.mem_span_insert.1 hmem
  have heD : e ≤ (M + 1) • e := fun k => by
    simp only [Pi.smul_apply, smul_eq_mul]
    nlinarith
  have hDe : (M + 1) • e - e = M • e := by
    funext k
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [add_mul, one_mul, Nat.add_sub_cancel]
  refine ⟨cmp (M • e) a, isMultiHomog_cmp _ _, fun z hz => ?_⟩
  have h1 : monomial μ (1 : ℂ) = cmp ((M + 1) • e) (a * G) + cmp ((M + 1) • e) s := by
    rw [← map_add, ← hμa, cmp_of_homog (isMultiHomog_monomial μ 1), if_pos hμ]
  rw [h1, map_add, cmp_mul hG, if_pos heD, hDe, map_mul, eval_cmp_eq_zero hS hz hs, add_zero]

/- English proof (translation)
Take `⟨t, rfl⟩` from `Nat.exists_eq_add_of_le hM`. Use `⟨monomial μ 1 * G ^ t, ?_, fun z _ => ?_⟩` and prove the remaining obligations. Use `isMultiHomog_mul (isMultiHomog_monomial μ 1) (isMultiHomog_pow hG t)` as an intermediate fact. Rewrite `this` using `[hμ, ← add_smul]`. Conclude with `this`.

Rewrite using `[map_mul, map_pow, pow_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rel_direct {S : Set (MRingOver ℂ ι)} {G : MRingOver ℂ ι} {e : K → ℕ} (hG : IsMultiHomog G e)
    {N₀ M : ℕ} (hM : M ≤ N₀) (μ : (Σ k, ι k) →₀ ℕ) (hμ : bdeg μ = M • e) :
    ∃ h : MRingOver ℂ ι, IsMultiHomog h (N₀ • e) ∧ ∀ z : (Σ k, ι k) → ℂ, (∀ s ∈ S, eval z s = 0) →
      eval z (monomial μ (1 : ℂ)) * eval z G ^ N₀ = eval z h * eval z G ^ M := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hM
  refine ⟨monomial μ 1 * G ^ t, ?_, fun z _ => ?_⟩
  · have := isMultiHomog_mul (isMultiHomog_monomial μ 1) (isMultiHomog_pow hG t)
    rw [hμ, ← add_smul] at this
    exact this
  · rw [map_mul, map_pow, pow_add]
    ring

/- English proof (translation)
Use `conv_lhs => rw [as_sum p]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun ν _ => ?_` and prove the remaining obligations. Rewrite using `[eval_monomial, eval_monomial]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eval_eq_sum_support (p : MRingOver ℂ ι) (z : (Σ k, ι k) → ℂ) :
    eval z p = ∑ ν ∈ p.support, coeff ν p * eval z (monomial ν 1) := by
  conv_lhs => rw [as_sum p]
  rw [map_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [eval_monomial, eval_monomial]
  ring

/- English proof (translation)
Proceed by induction on `M with`. Consider the case `zero => exact fun μ hμ => rel_direct hG (Nat.zero_le _) μ hμ`. Consider the case `succ M ih`. Introduce `μ hμ`. Distinguish the cases in `hM : M + 1 ≤ N₀`.

Conclude with `rel_direct hG hM μ hμ`. Take `⟨h₁, hh₁, hev⟩` from `hN₀ M (by omega) μ hμ choose! H hH hHev using ih`. Use `⟨∑ ν ∈ h₁.support, C (coeff ν h₁) * H ν, isMultiHomog_sum _ _ fun ν hν => isMultiHomog_C_mul (hH ν (bdeg_of_mem hh₁ hν)) _, fun z hz => ?_⟩` and prove the remaining obligations. Rewrite using `[hev z hz, eval_eq_sum_support h₁ z, map_sum]`. Simplify using `only [map_mul, eval_C]`.

Rewrite using `[Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun ν hν => ?_` and prove the remaining obligations. Use `hHev ν (bdeg_of_mem hh₁ hν) z hz` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation.
-/
theorem rel_all {S : Set (MRingOver ℂ ι)} {G : MRingOver ℂ ι} {e : K → ℕ} (hG : IsMultiHomog G e) (N₀ : ℕ)
    (hN₀ : ∀ M : ℕ, N₀ ≤ M → ∀ μ : (Σ k, ι k) →₀ ℕ, bdeg μ = (M + 1) • e →
      ∃ h : MRingOver ℂ ι, IsMultiHomog h (M • e) ∧
        ∀ z : (Σ k, ι k) → ℂ, (∀ s ∈ S, eval z s = 0) → eval z (monomial μ (1 : ℂ)) = eval z h * eval z G)
    (M : ℕ) : ∀ μ : (Σ k, ι k) →₀ ℕ, bdeg μ = M • e →
      ∃ h : MRingOver ℂ ι, IsMultiHomog h (N₀ • e) ∧ ∀ z : (Σ k, ι k) → ℂ, (∀ s ∈ S, eval z s = 0) →
        eval z (monomial μ (1 : ℂ)) * eval z G ^ N₀ = eval z h * eval z G ^ M := by
  induction M with
  | zero => exact fun μ hμ => rel_direct hG (Nat.zero_le _) μ hμ
  | succ M ih =>
    intro μ hμ
    by_cases hM : M + 1 ≤ N₀
    · exact rel_direct hG hM μ hμ
    · obtain ⟨h₁, hh₁, hev⟩ := hN₀ M (by omega) μ hμ
      choose! H hH hHev using ih
      refine ⟨∑ ν ∈ h₁.support, C (coeff ν h₁) * H ν,
        isMultiHomog_sum _ _ fun ν hν => isMultiHomog_C_mul (hH ν (bdeg_of_mem hh₁ hν)) _, fun z hz => ?_⟩
      rw [hev z hz, eval_eq_sum_support h₁ z, map_sum]
      simp only [map_mul, eval_C]
      rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun ν hν => ?_
      have := hHev ν (bdeg_of_mem hh₁ hν) z hz
      calc coeff ν h₁ * eval z (monomial ν 1) * eval z G * eval z G ^ N₀
          = coeff ν h₁ * (eval z (monomial ν 1) * eval z G ^ N₀) * eval z G := by ring
        _ = _ := by rw [this]; ring

def Mon (D : K → ℕ) : Set ((Σ k, ι k) →₀ ℕ) := {ν | bdeg ν = D}

/- English proof (translation)
Apply `(Set.finite_Icc (0 : (Σ k, ι k) →₀ ℕ) (Finsupp.equivFunOnFinite.symm fun p => D p.1)).subset` to reduce the goal to its premises. Introduce `ν hν`. Establish `hν' : bdeg ν = D` using `hν`. Use `⟨zero_le, ?_⟩` and prove the remaining obligations. Rewrite using `[Finsupp.le_def]`.

Introduce and unpack `⟨k, i⟩`. Simplify using `only [Finsupp.coe_equivFunOnFinite_symm]`. Rewrite using `[← hν']`. Conclude with `Finset.single_le_sum (f := fun i => ν ⟨k, i⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)`.
-/
theorem mon_finite (D : K → ℕ) : (Mon (ι := ι) D).Finite := by
  classical
  apply (Set.finite_Icc (0 : (Σ k, ι k) →₀ ℕ) (Finsupp.equivFunOnFinite.symm fun p => D p.1)).subset
  intro ν hν
  have hν' : bdeg ν = D := hν
  refine ⟨zero_le, ?_⟩
  rw [Finsupp.le_def]
  rintro ⟨k, i⟩
  simp only [Finsupp.coe_equivFunOnFinite_symm]
  rw [← hν']
  exact Finset.single_le_sum (f := fun i => ν ⟨k, i⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

instance (D : K → ℕ) : Finite (Mon (ι := ι) D) := (mon_finite D).to_subtype

noncomputable instance (D : K → ℕ) : Fintype (Mon (ι := ι) D) := Fintype.ofFinite _

/- English proof (translation)
Rewrite using `[eval_eq_sum_support, ← Finset.sum_subtype (mon_finite D).toFinset (fun x => Set.Finite.mem_toFinset _) (fun ν => coeff ν h * eval z (monomial ν 1))]`. Apply `Finset.sum_subset` to reduce the goal to its premises. Introduce `ν hν`. Rewrite using `[Set.Finite.mem_toFinset]`. Conclude with `bdeg_of_mem hh hν`.

Introduce `ν _ hν`. Rewrite `hν` using `[mem_support_iff, not_not]`. Rewrite using `[hν, zero_mul]`.
-/
theorem eval_eq_sum_mon {h : MRingOver ℂ ι} {D : K → ℕ} (hh : IsMultiHomog h D) (z : (Σ k, ι k) → ℂ) :
    eval z h = ∑ ν : Mon (ι := ι) D, coeff ν.1 h * eval z (monomial ν.1 1) := by
  classical
  rw [eval_eq_sum_support, ← Finset.sum_subtype (mon_finite D).toFinset (fun x => Set.Finite.mem_toFinset _)
    (fun ν => coeff ν h * eval z (monomial ν 1))]
  apply Finset.sum_subset
  · intro ν hν
    rw [Set.Finite.mem_toFinset]
    exact bdeg_of_mem hh hν
  · intro ν _ hν
    rw [mem_support_iff, not_not] at hν
    rw [hν, zero_mul]

def phi (G : MRingOver ℂ ι) (e : K → ℕ) (N₀ : ℕ) (z : (Σ k, ι k) → ℂ) : Mon (ι := ι) (N₀ • e) → ℂ :=
  fun ν => eval z (monomial ν.1 1) / eval z G ^ N₀

/- English proof (translation)
Take `⟨N₀, hN₀⟩` from `rel_one hS hG he hcone`. Use `⟨N₀, fun M F hF => ?_⟩` and prove the remaining obligations. Establish `hrel` using `rel_all hG N₀ hN₀ M`. Use `choose! H hH hHev using hrel`. Use `⟨fun ν => ∑ μ ∈ F.support, coeff μ F * coeff ν.1 (H μ), fun z hz hGz => ?_⟩` and prove the remaining obligations.

Establish `hGM : eval z G ^ M ≠ 0` using `pow_ne_zero _ hGz`. Establish `hGN : eval z G ^ N₀ ≠ 0` using `pow_ne_zero _ hGz`. Rewrite using `[eval_eq_sum_support F, Finset.sum_div]`. Simplify using `only [phi, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun μ hμ => ?_` and prove the remaining obligations. Establish `hμd` using `bdeg_of_mem hF hμ`. Establish `e1 : eval z (monomial μ 1) / eval z G ^ M = eval z (H μ) / eval z G ^ N₀`. Rewrite using `[div_eq_div_iff hGM hGN]`. Conclude with `hHev μ hμd z hz`.

Rewrite using `[mul_div_assoc, e1, eval_eq_sum_mon (hH μ hμd), Finset.sum_div, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun ν _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_rep {S : Set (MRingOver ℂ ι)} {G : MRingOver ℂ ι} {e : K → ℕ}
    (hS : ∀ s ∈ S, ∃ a, IsMultiHomog s a) (hG : IsMultiHomog G e) (he : ∀ k, 1 ≤ e k)
    (hcone : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (∀ s ∈ S, eval z s = 0) → eval z G ≠ 0) :
    ∃ N₀ : ℕ, ∀ (M : ℕ) (F : MRingOver ℂ ι), IsMultiHomog F (M • e) →
      ∃ d : Mon (ι := ι) (N₀ • e) → ℂ, ∀ z : (Σ k, ι k) → ℂ, (∀ s ∈ S, eval z s = 0) → eval z G ≠ 0 →
        eval z F / eval z G ^ M = ∑ ν, d ν * phi G e N₀ z ν := by
  obtain ⟨N₀, hN₀⟩ := rel_one hS hG he hcone
  refine ⟨N₀, fun M F hF => ?_⟩
  have hrel := rel_all hG N₀ hN₀ M
  choose! H hH hHev using hrel
  refine ⟨fun ν => ∑ μ ∈ F.support, coeff μ F * coeff ν.1 (H μ), fun z hz hGz => ?_⟩
  have hGM : eval z G ^ M ≠ 0 := pow_ne_zero _ hGz
  have hGN : eval z G ^ N₀ ≠ 0 := pow_ne_zero _ hGz
  rw [eval_eq_sum_support F, Finset.sum_div]
  simp only [phi, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hμd := bdeg_of_mem hF hμ
  have e1 : eval z (monomial μ 1) / eval z G ^ M = eval z (H μ) / eval z G ^ N₀ := by
    rw [div_eq_div_iff hGM hGN]
    exact hHev μ hμd z hz
  rw [mul_div_assoc, e1, eval_eq_sum_mon (hH μ hμd), Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  ring

/- English proof (translation)
Use function extensionality and compare the values at `ν`. Simplify using `only [phi]`. Rewrite using `[FibreRepresentatives.eval_smul (isMultiHomog_monomial ν.1 1) r w, FibreRepresentatives.eval_smul hG r w]`. Establish `hν : bdeg ν.1 = N₀ • e` using `ν.2`. Rewrite using `[hν]`.

Establish `hP : (∏ k, r k ^ e k) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hr k)`. Establish `hpow : (∏ k, r k ^ (N₀ • e) k) = (∏ k, r k ^ e k) ^ N₀`. Rewrite using `[← Finset.prod_pow]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, smul_eq_mul, mul_comm, pow_mul]`.

Rewrite using `[hpow, mul_pow, mul_div_mul_left _ _ (pow_ne_zero _ hP)]`.
-/
theorem phi_smul {G : MRingOver ℂ ι} {e : K → ℕ} (hG : IsMultiHomog G e) (N₀ : ℕ) (r : K → ℂ)
    (hr : ∀ k, r k ≠ 0) (w : (Σ k, ι k) → ℂ) :
    phi G e N₀ (fun p => r p.1 * w p) = phi G e N₀ w := by
  funext ν
  simp only [phi]
  rw [FibreRepresentatives.eval_smul (isMultiHomog_monomial ν.1 1) r w, FibreRepresentatives.eval_smul hG r w]
  have hν : bdeg ν.1 = N₀ • e := ν.2
  rw [hν]
  have hP : (∏ k, r k ^ e k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hr k)
  have hpow : (∏ k, r k ^ (N₀ • e) k) = (∏ k, r k ^ e k) ^ N₀ := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, mul_comm, pow_mul]
  rw [hpow, mul_pow, mul_div_mul_left _ _ (pow_ne_zero _ hP)]

open Classical in

/- English proof (translation)
Use `isMultiHomog_monomial (ι := ι) (Finsupp.single (⟨k, a⟩ : Σ k, ι k) 1) (1 : ℂ)` as an intermediate fact. Rewrite using `[show (X ⟨k, a⟩ : MRingOver ℂ ι) = monomial (Finsupp.single ⟨k, a⟩ 1) 1 from rfl]`. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k'`. Distinguish the cases in `h : k' = k`.

Substitute `h` using the available equality. Simplify using `[bdeg, Finsupp.single_apply]`. Simplify using `only [if_neg h, bdeg]`. Use `symm`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Finsupp.single_apply, if_neg]`. Introduce `h'`. Conclude with `h (congrArg Sigma.fst h').symm`.
-/
theorem isMultiHomog_X (k : K) (a : ι k) :
    IsMultiHomog (X ⟨k, a⟩ : MRingOver ℂ ι) (fun k' => if k' = k then 1 else 0) := by
  classical
  have := isMultiHomog_monomial (ι := ι) (Finsupp.single (⟨k, a⟩ : Σ k, ι k) 1) (1 : ℂ)
  rw [show (X ⟨k, a⟩ : MRingOver ℂ ι) = monomial (Finsupp.single ⟨k, a⟩ 1) 1 from rfl]
  convert this using 1
  funext k'
  by_cases h : k' = k
  · subst h
    simp [bdeg, Finsupp.single_apply]
  · simp only [if_neg h, bdeg]
    symm
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro h'
    exact h (congrArg Sigma.fst h').symm

/- English proof (translation)
Establish `hmin : ∃ k a b, z ⟨k, a⟩ * w ⟨k, b⟩ ≠ z ⟨k, b⟩ * w ⟨k, a⟩`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Apply `hn` to reduce the goal to its premises. Use `choose i hi using hw`.

Use `⟨fun k => z ⟨k, i k⟩ / w ⟨k, i k⟩, fun k h0 => ?_, ?_⟩` and prove the remaining obligations. Rewrite `h0` using `[div_eq_zero_iff]`. Break down `h0 with h0 | h0` into its components or cases. Take `⟨a, ha⟩` from `hz k`. Use `hc k a (i k)` as an intermediate fact.

Rewrite `this` using `[h0, zero_mul]`. Conclude with `ha ((mul_eq_zero.1 this).resolve_right (hi k))`. Conclude with `hi k h0`. Use function extensionality and compare the values at `⟨k, a⟩`. Simplify using `only`.

Rewrite using `[div_mul_eq_mul_div, eq_div_iff (hi k)]`. Conclude with `hc k a (i k)`. Take `⟨k, a, b, hab⟩` from `hmin`. Use `choose j hj using hz`. Set `δ : K → ℕ` to `fun k' => if k' = k then 1 else 0`.

Set `L : MRingOver ℂ ι` to `C (w ⟨k, b⟩) * X ⟨k, a⟩ + C (-w ⟨k, a⟩) * X ⟨k, b⟩`. Establish `hL : IsMultiHomog L δ` using `isMultiHomog_add (isMultiHomog_C_mul (isMultiHomog_X k a) _) (isMultiHomog_C_mul (isMultiHomog_X k b) _)`. Use `⟨L * monomial (spike j (e - δ)) 1, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `isMultiHomog_mul hL (isMultiHomog_monomial (spike j (e - δ)) (1 : ℂ))` as an intermediate fact. Rewrite `this` using `[bdeg_spike]`.

Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k'`. Use `he k'` as an intermediate fact. Simplify using `only [Pi.add_apply, Pi.sub_apply, δ]`. Apply the tactic sequence `split_ifs <;> omega`.

Rewrite using `[map_mul]`. Apply `mul_eq_zero_of_left` to reduce the goal to its premises. Simplify using `only [L, map_add, map_mul, eval_C, eval_X]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_mul]`.

Use `mul_ne_zero ?_ ?_` and prove the remaining obligations. Simplify using `only [L, map_add, map_mul, eval_C, eval_X]`. Introduce `h`. Apply `hab` to reduce the goal to its premises. Take the linear combination `h`.

Rewrite using `[eval_spike]`. Conclude with `Finset.prod_ne_zero_iff.2 fun k' _ => pow_ne_zero _ (hj k')`.
-/
theorem exists_sep {e : K → ℕ} (he : ∀ k, 1 ≤ e k) {z w : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0)
    (hn : ¬ ∃ r : K → ℂ, (∀ k, r k ≠ 0) ∧ z = fun p => r p.1 * w p) :
    ∃ Q : MRingOver ℂ ι, IsMultiHomog Q e ∧ eval w Q = 0 ∧ eval z Q ≠ 0 := by
  classical
  have hmin : ∃ k a b, z ⟨k, a⟩ * w ⟨k, b⟩ ≠ z ⟨k, b⟩ * w ⟨k, a⟩ := by
    by_contra hc
    push_neg at hc
    apply hn
    choose i hi using hw
    refine ⟨fun k => z ⟨k, i k⟩ / w ⟨k, i k⟩, fun k h0 => ?_, ?_⟩
    · rw [div_eq_zero_iff] at h0
      rcases h0 with h0 | h0
      · obtain ⟨a, ha⟩ := hz k
        have := hc k a (i k)
        rw [h0, zero_mul] at this
        exact ha ((mul_eq_zero.1 this).resolve_right (hi k))
      · exact hi k h0
    · funext ⟨k, a⟩
      simp only
      rw [div_mul_eq_mul_div, eq_div_iff (hi k)]
      exact hc k a (i k)
  obtain ⟨k, a, b, hab⟩ := hmin
  choose j hj using hz
  let δ : K → ℕ := fun k' => if k' = k then 1 else 0
  let L : MRingOver ℂ ι := C (w ⟨k, b⟩) * X ⟨k, a⟩ + C (-w ⟨k, a⟩) * X ⟨k, b⟩
  have hL : IsMultiHomog L δ :=
    isMultiHomog_add (isMultiHomog_C_mul (isMultiHomog_X k a) _) (isMultiHomog_C_mul (isMultiHomog_X k b) _)
  refine ⟨L * monomial (spike j (e - δ)) 1, ?_, ?_, ?_⟩
  · have := isMultiHomog_mul hL (isMultiHomog_monomial (spike j (e - δ)) (1 : ℂ))
    rw [bdeg_spike] at this
    convert this using 1
    funext k'
    have := he k'
    simp only [Pi.add_apply, Pi.sub_apply, δ]
    split_ifs <;> omega
  · rw [map_mul]
    apply mul_eq_zero_of_left
    simp only [L, map_add, map_mul, eval_C, eval_X]
    ring
  · rw [map_mul]
    refine mul_ne_zero ?_ ?_
    · simp only [L, map_add, map_mul, eval_C, eval_X]
      intro h
      apply hab
      linear_combination h
    · rw [eval_spike]
      exact Finset.prod_ne_zero_iff.2 fun k' _ => pow_ne_zero _ (hj k')

end AvoidFormFinite

open AvoidFormFinite in

/- English proof (translation)
Introduce `K _ ι _ S G e he hG hS hcone`. Take `⟨N₀, hrep⟩` from `exists_rep hS hG he hcone`. Set `P : ((Σ k, ι k) → ℂ) → Prop` to `fun z => (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧ ∀ s ∈ S, eval z s = 0`. Set `V : Set (Mon (ι` to `ι) (N₀ • e) → ℂ) := Set.range (fun z : {z // P z} => phi G e N₀ z.1)`. Establish `horb : ∀ z t, P z → P t → phi G e N₀ z = phi G e N₀ t → ∃ r : K → ℂ, (∀ k, r k ≠ 0) ∧ z = fun p => r p.1 * t p`.

Introduce `z t hz ht hzt`. Assume the negation of the conclusion as `hn`. Take `⟨Q, hQ, hQt, hQz⟩` from `exists_sep he hz.1 ht.1 hn`. Take `⟨d, hd⟩` from `hrep 1 Q (by rw [one_smul]; exact hQ)`. Establish `h1` using `hd z hz.2 (hcone z hz.1 hz.2)`.

Establish `h2` using `hd t ht.2 (hcone t ht.1 ht.2)`. Rewrite `h1` using `[hzt, ← h2, hQt, zero_div, div_eq_zero_iff]`. Break down `h1 with h1 | h1` into its components or cases. Conclude with `hQz h1`. Conclude with `pow_ne_zero _ (hcone z hz.1 hz.2) h1`.

Use `choose pre hpre0 using fun v : V => v.2`. Establish `hpre : ∀ v : V, phi G e N₀ (pre v).1 = v` using `fun v => hpre0 v`. Establish `hli : LinearIndependent ℂ (fun v : V => (v : Mon (ι` using `ι) (N₀ • e) → ℂ)) := by`. Rewrite using `[linearIndependent_iff']`. Introduce `s g hsum i hi`.

Establish `hsep : ∀ j ∈ s.erase i, ∃ Q : MRingOver ℂ ι, IsMultiHomog Q e ∧ eval (pre j).1 Q = 0 ∧ eval (pre i).1 Q ≠ 0`. Introduce `j hj`. Use `exists_sep he (pre i).2.1 (pre j).2.1 ?_` and prove the remaining obligations. Introduce and unpack `⟨r, hr, hrz⟩`. Apply `(Finset.mem_erase.1 hj).1` to reduce the goal to its premises.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hpre j, ← hpre i, hrz, phi_smul hG N₀ r hr]`. Use `choose! Q hQe hQz hQi using hsep`. Establish `hF` using `isMultiHomog_prod (s.erase i) Q (fun _ => e) hQe`. Rewrite `hF` using `[Finset.sum_const]`.

Take `⟨d, hd⟩` from `hrep _ _ hF`. Establish `hval : ∀ v : V, ∑ ν, d ν * (v : Mon (ι` using `ι) (N₀ • e) → ℂ) ν = eval (pre v).1 (∏ j ∈ s.erase i, Q j) / eval (pre v).1 G ^ (s.erase i).card := by`. Introduce `v`. Rewrite using `[hd _ (pre v).2.2 (hcone _ (pre v).2.1 (pre v).2.2), hpre v]`. Establish `h0 : ∑ v ∈ s, g v * (eval (pre v).1 (∏ j ∈ s.erase i, Q j) / eval (pre v).1 G ^ (s.erase i).card) = 0`.

Repeatedly rewrite using `[← hval]`. Establish `hz : ∀ ν, ∑ v ∈ s, g v * (v : Mon (ι` using `ι) (N₀ • e) → ℂ) ν = 0 := fun ν => by`. Use `congrFun hsum ν` as an intermediate fact. Simplify `this` using `[Finset.sum_apply]`. Combine the equalities or inequalities in the displayed calculation.

Repeatedly rewrite using `[Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring` and prove the remaining obligations. Use `_ = 0 := by simp [hz]`. Rewrite using `[Finset.sum_eq_single i (fun v hv hvi => by`.

Rewrite `h0` using `[map_prod, Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hvi, hv⟩) (hQz v (Finset.mem_erase.2 ⟨hvi, hv⟩)), zero_div, mul_zero]) (fun h => absurd hi h)]`. Break down `mul_eq_zero.1 h0 with h | h` into its components or cases. Conclude with `h`. It suffices to derive a contradiction. Rewrite `h` using `[div_eq_zero_iff]`.

Break down `h with h | h` into its components or cases. Rewrite `h` using `[map_prod]`. Conclude with `(Finset.prod_ne_zero_iff.2 fun j hj => hQi j hj) h`. Conclude with `pow_ne_zero _ (hcone _ (pre i).2.1 (pre i).2.2) h`. Use `haveI : Finite V := hli.finite_of_isNoetherian`.

Use `haveI := Fintype.ofFinite V`. Use `⟨Finset.univ.image fun v => (pre v).1, fun z hz hzS => ?_⟩` and prove the remaining obligations. Set `v : V` to `⟨phi G e N₀ z, ⟨z, hz, hzS⟩, rfl⟩`. Conclude with `⟨(pre v).1, Finset.mem_image_of_mem _ (Finset.mem_univ v), horb z (pre v).1 ⟨hz, hzS⟩ (pre v).2 (hpre v).symm⟩`.
-/
theorem AvoidFormFinite.proof : AvoidFormFinite.Statement := by
  intro K _ ι _ S G e he hG hS hcone
  classical
  obtain ⟨N₀, hrep⟩ := exists_rep hS hG he hcone
  let P : ((Σ k, ι k) → ℂ) → Prop := fun z => (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧ ∀ s ∈ S, eval z s = 0
  let V : Set (Mon (ι := ι) (N₀ • e) → ℂ) := Set.range (fun z : {z // P z} => phi G e N₀ z.1)
  have horb : ∀ z t, P z → P t → phi G e N₀ z = phi G e N₀ t →
      ∃ r : K → ℂ, (∀ k, r k ≠ 0) ∧ z = fun p => r p.1 * t p := by
    intro z t hz ht hzt
    by_contra hn
    obtain ⟨Q, hQ, hQt, hQz⟩ := exists_sep he hz.1 ht.1 hn
    obtain ⟨d, hd⟩ := hrep 1 Q (by rw [one_smul]; exact hQ)
    have h1 := hd z hz.2 (hcone z hz.1 hz.2)
    have h2 := hd t ht.2 (hcone t ht.1 ht.2)
    rw [hzt, ← h2, hQt, zero_div, div_eq_zero_iff] at h1
    rcases h1 with h1 | h1
    · exact hQz h1
    · exact pow_ne_zero _ (hcone z hz.1 hz.2) h1
  choose pre hpre0 using fun v : V => v.2
  have hpre : ∀ v : V, phi G e N₀ (pre v).1 = v := fun v => hpre0 v
  have hli : LinearIndependent ℂ (fun v : V => (v : Mon (ι := ι) (N₀ • e) → ℂ)) := by
    rw [linearIndependent_iff']
    intro s g hsum i hi
    have hsep : ∀ j ∈ s.erase i, ∃ Q : MRingOver ℂ ι, IsMultiHomog Q e ∧ eval (pre j).1 Q = 0 ∧
        eval (pre i).1 Q ≠ 0 := by
      intro j hj
      refine exists_sep he (pre i).2.1 (pre j).2.1 ?_
      rintro ⟨r, hr, hrz⟩
      apply (Finset.mem_erase.1 hj).1
      apply Subtype.ext
      rw [← hpre j, ← hpre i, hrz, phi_smul hG N₀ r hr]
    choose! Q hQe hQz hQi using hsep
    have hF := isMultiHomog_prod (s.erase i) Q (fun _ => e) hQe
    rw [Finset.sum_const] at hF
    obtain ⟨d, hd⟩ := hrep _ _ hF
    have hval : ∀ v : V, ∑ ν, d ν * (v : Mon (ι := ι) (N₀ • e) → ℂ) ν =
        eval (pre v).1 (∏ j ∈ s.erase i, Q j) / eval (pre v).1 G ^ (s.erase i).card := by
      intro v
      rw [hd _ (pre v).2.2 (hcone _ (pre v).2.1 (pre v).2.2), hpre v]
    have h0 : ∑ v ∈ s, g v * (eval (pre v).1 (∏ j ∈ s.erase i, Q j) /
        eval (pre v).1 G ^ (s.erase i).card) = 0 := by
      simp_rw [← hval]
      have hz : ∀ ν, ∑ v ∈ s, g v * (v : Mon (ι := ι) (N₀ • e) → ℂ) ν = 0 := fun ν => by
        have := congrFun hsum ν
        simpa [Finset.sum_apply] using this
      calc ∑ v ∈ s, g v * ∑ ν, d ν * (v : Mon (ι := ι) (N₀ • e) → ℂ) ν
          = ∑ ν, d ν * ∑ v ∈ s, g v * (v : Mon (ι := ι) (N₀ • e) → ℂ) ν := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
        _ = 0 := by simp [hz]
    rw [Finset.sum_eq_single i (fun v hv hvi => by
      rw [map_prod, Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hvi, hv⟩) (hQz v (Finset.mem_erase.2 ⟨hvi, hv⟩)),
        zero_div, mul_zero]) (fun h => absurd hi h)] at h0
    rcases mul_eq_zero.1 h0 with h | h
    · exact h
    · exfalso
      rw [div_eq_zero_iff] at h
      rcases h with h | h
      · rw [map_prod] at h
        exact (Finset.prod_ne_zero_iff.2 fun j hj => hQi j hj) h
      · exact pow_ne_zero _ (hcone _ (pre i).2.1 (pre i).2.2) h
  haveI : Finite V := hli.finite_of_isNoetherian
  haveI := Fintype.ofFinite V
  refine ⟨Finset.univ.image fun v => (pre v).1, fun z hz hzS => ?_⟩
  let v : V := ⟨phi G e N₀ z, ⟨z, hz, hzS⟩, rfl⟩
  exact ⟨(pre v).1, Finset.mem_image_of_mem _ (Finset.mem_univ v),
    horb z (pre v).1 ⟨hz, hzS⟩ (pre v).2 (hpre v).symm⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
