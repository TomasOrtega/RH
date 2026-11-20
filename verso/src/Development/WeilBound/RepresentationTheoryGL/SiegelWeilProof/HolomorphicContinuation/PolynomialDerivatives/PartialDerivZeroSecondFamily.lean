import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.CoeffSmulX

noncomputable section

open MvPolynomial Finsupp

namespace PositivityTheory.Rg.Sw.LC

namespace CoreC

open PositivityTheory.Rg.Sw G

variable {m n : ℕ}

def pE : (Fin m × Fin n × Bool) ≃ (Fin m × Fin n × Bool) where
  toFun k := (k.1, k.2.1, !k.2.2)
  invFun k := (k.1, k.2.1, !k.2.2)
  left_inv k := by simp
  right_inv k := by simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem pE_apply (k : Fin m × Fin n × Bool) : pE k = (k.1, k.2.1, !k.2.2) := rfl

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
@[simp] theorem pE_pE (k : Fin m × Fin n × Bool) : pE (pE k) = k := by simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pE_symm : (pE : (Fin m × Fin n × Bool) ≃ (Fin m × Fin n × Bool)).symm = pE := rfl

/- English proof (translation)
Apply the tactic sequence `obtain ⟨a, i, b⟩ := k; simp only [pE_apply, inF1]; cases b <;> cases ε a <;> simp`.
-/
theorem first_family_partner_iff (ε : Fin m → Bool) (k : Fin m × Fin n × Bool) : inF1 ε (pE k) ↔ ¬ inF1 ε k := by
  obtain ⟨a, i, b⟩ := k; simp only [pE_apply, inF1]; cases b <;> cases ε a <;> simp

/- English proof (translation)
Unfold `F1`. Rewrite using `[Subalgebra.mem_toSubmodule, MvPolynomial.mem_supported]`. Prove the components needed by the constructor for the conclusion. Introduce `h s hs k hk`. Conclude with `h (mem_vars k |>.mpr ⟨s, hs, hk⟩)`.

Introduce `h k hk`. Take `⟨s, hs, hk'⟩` from `(mem_vars k).mp hk`. Conclude with `h s hs k hk'`.
-/
theorem mem_first_family_iff (ε : Fin m → Bool) (p : PX m n) : p ∈ F1 ε ↔ ∀ s ∈ p.support, ∀ k ∈ s.support, inF1 ε k := by
  unfold F1
  rw [Subalgebra.mem_toSubmodule, MvPolynomial.mem_supported]
  constructor
  · intro h s hs k hk; exact h (mem_vars k |>.mpr ⟨s, hs, hk⟩)
  · intro h k hk; obtain ⟨s, hs, hk'⟩ := (mem_vars k).mp hk; exact h s hs k hk'

/- English proof (translation)
Unfold `F2`. Rewrite using `[Subalgebra.mem_toSubmodule, MvPolynomial.mem_supported]`. Prove the components needed by the constructor for the conclusion. Introduce `h s hs k hk`. Conclude with `h (mem_vars k |>.mpr ⟨s, hs, hk⟩)`.

Introduce `h k hk`. Take `⟨s, hs, hk'⟩` from `(mem_vars k).mp hk`. Conclude with `h s hs k hk'`.
-/
theorem mem_second_family_iff (ε : Fin m → Bool) (p : PX m n) : p ∈ F2 ε ↔ ∀ s ∈ p.support, ∀ k ∈ s.support, ¬ inF1 ε k := by
  unfold F2
  rw [Subalgebra.mem_toSubmodule, MvPolynomial.mem_supported]
  constructor
  · intro h s hs k hk; exact h (mem_vars k |>.mpr ⟨s, hs, hk⟩)
  · intro h k hk; obtain ⟨s, hs, hk'⟩ := (mem_vars k).mp hk; exact h s hs k hk'

/- English proof (translation)
Rewrite `hp`, the goal using `[supported_eq_adjoin_X]`. Proceed by induction on `hp using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨j, _, rfl⟩` from `hx`. Rewrite using `[pderiv_X]`.

Distinguish the cases in `h : k = j`. Substitute `h` using the available equality. Simplify using `[Subalgebra.one_mem]`. Simplify using `[Pi.single_apply, Ne.symm h, h]`. Consider the case `algebraMap r => simp`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `mul x y hx' hy' hx hy`. Rewrite using `[Derivation.leibniz, smul_eq_mul, smul_eq_mul]`. Conclude with `add_mem (mul_mem (Algebra.adjoin_le (fun z hz => Algebra.subset_adjoin hz) hx') hy) (mul_mem (Algebra.adjoin_le (fun z hz => Algebra.subset_adjoin hz) hy') hx)`.
-/
theorem pderiv_mem_supported (S : Set (Fin m × Fin n × Bool)) (k) {p : PX m n} (hp : p ∈ supported ℂ S) :
    pderiv k p ∈ supported ℂ S := by
  rw [supported_eq_adjoin_X] at hp ⊢
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, _, rfl⟩ := hx
    rw [pderiv_X]
    by_cases h : k = j
    · subst h; simp [Subalgebra.one_mem]
    · simp [Pi.single_apply, Ne.symm h, h]
  | algebraMap r => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y hx' hy' hx hy =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (mul_mem (Algebra.adjoin_le (fun z hz => Algebra.subset_adjoin hz) hx') hy)
      (mul_mem (Algebra.adjoin_le (fun z hz => Algebra.subset_adjoin hz) hy') hx)

/- English proof (translation)
The claim follows from `pderiv_mem_supported _ k hp`.
-/
theorem partial_deriv_mem_first_family (ε : Fin m → Bool) (k) {p : PX m n} (hp : p ∈ F1 ε) : pderiv k p ∈ F1 ε :=
  pderiv_mem_supported _ k hp

/- English proof (translation)
The claim follows from `pderiv_mem_supported _ k hp`.
-/
theorem partial_deriv_mem_second_family (ε : Fin m → Bool) (k) {p : PX m n} (hp : p ∈ F2 ε) : pderiv k p ∈ F2 ε :=
  pderiv_mem_supported _ k hp

/- English proof (translation)
The claim follows from `Subalgebra.mul_mem _ (MvPolynomial.X_mem_supported.mpr hk) hp`.
-/
theorem variable_mul_mem_first_family (ε : Fin m → Bool) {k} (hk : inF1 ε k) {p : PX m n} (hp : p ∈ F1 ε) : X k * p ∈ F1 ε :=
  Subalgebra.mul_mem _ (MvPolynomial.X_mem_supported.mpr hk) hp

/- English proof (translation)
The claim follows from `Subalgebra.mul_mem _ (MvPolynomial.X_mem_supported.mpr hk) hp`.
-/
theorem variable_mul_mem_second_family (ε : Fin m → Bool) {k} (hk : ¬ inF1 ε k) {p : PX m n} (hp : p ∈ F2 ε) : X k * p ∈ F2 ε :=
  Subalgebra.mul_mem _ (MvPolynomial.X_mem_supported.mpr hk) hp

/- English proof (translation)
Apply `pderiv_eq_zero_of_notMem_vars` to reduce the goal to its premises. Introduce `hv`. Take `⟨s, hs, hks⟩` from `(mem_vars k).mp hv`. Conclude with `hk ((mem_first_family_iff ε p).mp hp s hs k hks)`.
-/
theorem partial_deriv_zero_first_family (ε : Fin m → Bool) {k} (hk : ¬ inF1 ε k) {p : PX m n} (hp : p ∈ F1 ε) : pderiv k p = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro hv
  obtain ⟨s, hs, hks⟩ := (mem_vars k).mp hv
  exact hk ((mem_first_family_iff ε p).mp hp s hs k hks)

/- English proof (translation)
Apply `pderiv_eq_zero_of_notMem_vars` to reduce the goal to its premises. Introduce `hv`. Take `⟨s, hs, hks⟩` from `(mem_vars k).mp hv`. Conclude with `(mem_second_family_iff ε p).mp hp s hs k hks hk`.
-/
theorem partial_deriv_zero_second_family (ε : Fin m → Bool) {k} (hk : inF1 ε k) {p : PX m n} (hp : p ∈ F2 ε) : pderiv k p = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro hv
  obtain ⟨s, hs, hks⟩ := (mem_vars k).mp hv
  exact (mem_second_family_iff ε p).mp hp s hs k hks hk

def piC (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) : ℂ :=
  ∏ a, ∏ i, (((s (a, i, false)).factorial : ℂ) * (2 * c : ℂ) ^ (s (a, i, false)))

def Bal (s : Fin m × Fin n × Bool →₀ ℕ) : Prop := ∀ a i, s (a, i, false) = s (a, i, true)

instance (s : Fin m × Fin n × Bool →₀ ℕ) : Decidable (Bal s) := by unfold Bal; infer_instance

/- English proof (translation)
Unfold `contr`. Use `Finset.sum_subset hp fun s _ hs => ?_` and prove the remaining obligations. Establish `h0 : p.coeff s = 0`. Assume the negation of the conclusion as `h`. Conclude with `hs (MvPolynomial.mem_support_iff.mpr h)`.

Simplify using `[h0]`.
-/
theorem contr_eqS (c : ℝ) (S : Finset (Fin m × Fin n × Bool →₀ ℕ)) {p : PX m n} (hp : p.support ⊆ S) :
    contr c p = ∑ s ∈ S, if Bal s then p.coeff s * piC c s else 0 := by
  unfold contr
  refine Finset.sum_subset hp fun s _ hs => ?_
  have h0 : p.coeff s = 0 := by
    by_contra h; exact hs (MvPolynomial.mem_support_iff.mpr h)
  simp [h0]

/- English proof (translation)
Rewrite using `[contr_eqS c (p.support ∪ q.support) MvPolynomial.support_add, contr_eqS c (p.support ∪ q.support) Finset.subset_union_left, contr_eqS c (p.support ∪ q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp [coeff_add, add_mul]`.
-/
theorem contr_add (c : ℝ) (p q : PX m n) : contr c (p + q) = contr c p + contr c q := by
  classical
  rw [contr_eqS c (p.support ∪ q.support) MvPolynomial.support_add, contr_eqS c (p.support ∪ q.support) Finset.subset_union_left,
    contr_eqS c (p.support ∪ q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> simp [coeff_add, add_mul]

/- English proof (translation)
Rewrite using `[contr_eqS c p.support MvPolynomial.support_smul, contr_eqS c p.support le_rfl, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp [coeff_smul, mul_assoc]`.
-/
theorem contr_smul (c : ℝ) (r : ℂ) (p : PX m n) : contr c (r • p) = r * contr c p := by
  classical
  rw [contr_eqS c p.support MvPolynomial.support_smul, contr_eqS c p.support le_rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> simp [coeff_smul, mul_assoc]

/- English proof (translation)
Proceed by induction on `I using Finset.induction_on with`. Consider the case `empty => simp [contr]`. Consider the case `insert a I ha ih => rw [Finset.sum_insert ha, contr_add, ih, Finset.sum_insert ha]`.
-/
theorem contr_sum (c : ℝ) {ι : Type} (I : Finset ι) (f : ι → PX m n) : contr c (∑ i ∈ I, f i) = ∑ i ∈ I, contr c (f i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [contr]
  | insert a I ha ih => rw [Finset.sum_insert ha, contr_add, ih, Finset.sum_insert ha]

/- English proof (translation)
Rewrite using `[show -p = (-1 : ℂ) • p by simp, contr_smul]; ring`.
-/
theorem contr_neg (c : ℝ) (p : PX m n) : contr c (-p) = -contr c p := by
  rw [show -p = (-1 : ℂ) • p by simp, contr_smul]; ring

/- English proof (translation)
Rewrite using `[sub_eq_add_neg, contr_add, contr_neg]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem contr_sub (c : ℝ) (p q : PX m n) : contr c (p - q) = contr c p - contr c q := by
  rw [sub_eq_add_neg, contr_add, contr_neg]; ring

/- English proof (translation)
Rewrite using `[contr_eqS c {v} ((support_monomial_subset).trans (by simp)), Finset.sum_singleton]`. Simplify using `[coeff_monomial]`.
-/
theorem contr_monomial (c : ℝ) (v : Fin m × Fin n × Bool →₀ ℕ) (d : ℂ) :
    contr c (monomial v d) = if Bal v then d * piC c v else 0 := by
  classical
  rw [contr_eqS c {v} ((support_monomial_subset).trans (by simp)), Finset.sum_singleton]
  simp [coeff_monomial]

/- English proof (translation)
Establish `hs0 : ∀ k, ¬ inF1 ε k → s k = 0` using `fun k hk => by`. Assume the negation of the conclusion as `h`. Conclude with `hk (hs k (Finsupp.mem_support_iff.mpr h))`. Establish `hu0 : ∀ k, inF1 ε k → u k = 0` using `fun k hk => by`. Assume the negation of the conclusion as `h`.

Conclude with `hu k (Finsupp.mem_support_iff.mpr h) hk`. Prove the components needed by the constructor for the conclusion. Introduce `hb`. Use extensionality with `⟨a, i, b⟩`. Rewrite using `[Finsupp.mapDomain_equiv_apply, pE_symm, pE_apply]`.

Establish `hb'` using `hb a i`. Simplify using `only [Finsupp.add_apply] at hb'`. Apply the tactic sequence `cases b <;> cases hεa : ε a`. Establish `h1` using `hs0 (a, i, false) (by simp [inF1, hεa])`. Establish `h2` using `hu0 (a, i, true) (by simp [inF1, hεa])`.

Simplify using `only [Bool.not_false]`. Use linear arithmetic over natural numbers and integers. Establish `h1` using `hu0 (a, i, false) (by simp [inF1, hεa])`. Establish `h2` using `hs0 (a, i, true) (by simp [inF1, hεa])`. Simplify using `only [Bool.not_false]`.

Use linear arithmetic over natural numbers and integers. Establish `h1` using `hu0 (a, i, true) (by simp [inF1, hεa])`. Establish `h2` using `hs0 (a, i, false) (by simp [inF1, hεa])`. Simplify using `only [Bool.not_true]`. Use linear arithmetic over natural numbers and integers.

Establish `h1` using `hs0 (a, i, true) (by simp [inF1, hεa])`. Establish `h2` using `hu0 (a, i, false) (by simp [inF1, hεa])`. Simplify using `only [Bool.not_true]`. Use linear arithmetic over natural numbers and integers. Introduce `h a i`.

Rewrite using `[h]`. Simplify using `only [Finsupp.add_apply, Finsupp.mapDomain_equiv_apply, pE_symm, pE_apply, Bool.not_false, Bool.not_true]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem bal_iff (ε : Fin m → Bool) {s u : Fin m × Fin n × Bool →₀ ℕ} (hs : ∀ k ∈ s.support, inF1 ε k)
    (hu : ∀ k ∈ u.support, ¬ inF1 ε k) : Bal (s + u) ↔ s = u.mapDomain pE := by
  have hs0 : ∀ k, ¬ inF1 ε k → s k = 0 := fun k hk => by
    by_contra h; exact hk (hs k (Finsupp.mem_support_iff.mpr h))
  have hu0 : ∀ k, inF1 ε k → u k = 0 := fun k hk => by
    by_contra h; exact hu k (Finsupp.mem_support_iff.mpr h) hk
  constructor
  · intro hb
    ext ⟨a, i, b⟩
    rw [Finsupp.mapDomain_equiv_apply, pE_symm, pE_apply]
    have hb' := hb a i
    simp only [Finsupp.add_apply] at hb'
    cases b <;> cases hεa : ε a
    · have h1 := hs0 (a, i, false) (by simp [inF1, hεa])
      have h2 := hu0 (a, i, true) (by simp [inF1, hεa])
      simp only [Bool.not_false]; omega
    · have h1 := hu0 (a, i, false) (by simp [inF1, hεa])
      have h2 := hs0 (a, i, true) (by simp [inF1, hεa])
      simp only [Bool.not_false]; omega
    · have h1 := hu0 (a, i, true) (by simp [inF1, hεa])
      have h2 := hs0 (a, i, false) (by simp [inF1, hεa])
      simp only [Bool.not_true]; omega
    · have h1 := hs0 (a, i, true) (by simp [inF1, hεa])
      have h2 := hu0 (a, i, false) (by simp [inF1, hεa])
      simp only [Bool.not_true]; omega
  · intro h a i
    rw [h]
    simp only [Finsupp.add_apply, Finsupp.mapDomain_equiv_apply, pE_symm, pE_apply, Bool.not_false, Bool.not_true]
    ring

/- English proof (translation)
Establish `hu0 : ∀ k, inF1 ε k → u k = 0` using `fun k hk => by`. Assume the negation of the conclusion as `h`. Conclude with `hu k (Finsupp.mem_support_iff.mpr h) hk`. Rewrite using `[wt_univ]`. Use `push_cast`.

Rewrite using `[Fintype.prod_prod_type]`. Unfold `piC`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.prod_prod_type]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Fintype.prod_bool]`. Substitute `h` using the available equality. Simplify using `only [Finsupp.add_apply, Finsupp.mapDomain_equiv_apply, pE_symm, pE_apply, Bool.not_false, Bool.not_true]`. Consider the cases of `hεa : ε a`. Establish `h1` using `hu0 (a, i, true) (by simp [inF1, hεa])`.

Rewrite using `[h1]`. Simplify using the standard rewrite rules. Establish `h1` using `hu0 (a, i, false) (by simp [inF1, hεa])`. Rewrite using `[h1]`. Simplify using `[mul_comm]`.
-/
theorem piC_eq_wt (ε : Fin m → Bool) (c : ℝ) {s u : Fin m × Fin n × Bool →₀ ℕ}
    (hu : ∀ k ∈ u.support, ¬ inF1 ε k) (h : s = u.mapDomain pE) : piC c (s + u) = (wt c s : ℂ) := by
  have hu0 : ∀ k, inF1 ε k → u k = 0 := fun k hk => by
    by_contra h; exact hu k (Finsupp.mem_support_iff.mpr h) hk
  rw [wt_univ]
  push_cast
  rw [Fintype.prod_prod_type]
  unfold piC
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fintype.prod_bool]
  subst h
  simp only [Finsupp.add_apply, Finsupp.mapDomain_equiv_apply, pE_symm, pE_apply, Bool.not_false, Bool.not_true]
  cases hεa : ε a
  · have h1 := hu0 (a, i, true) (by simp [inF1, hεa])
    rw [h1]; simp
  · have h1 := hu0 (a, i, false) (by simp [inF1, hεa])
    rw [h1]; simp [mul_comm]

/- English proof (translation)
Rewrite using `[monomial_mul, contr_monomial]`. Distinguish the cases in `h : s = u.mapDomain pE`. Rewrite using `[if_pos ((bal_iff ε hs hu).mpr h), if_pos h, piC_eq_wt ε c hu h]`. Rewrite using `[if_neg (fun hb => h ((bal_iff ε hs hu).mp hb)), if_neg h]`.
-/
theorem contr_mono (ε : Fin m → Bool) (c : ℝ) {s u : Fin m × Fin n × Bool →₀ ℕ} (hs : ∀ k ∈ s.support, inF1 ε k)
    (hu : ∀ k ∈ u.support, ¬ inF1 ε k) (a b : ℂ) :
    contr c (monomial s a * monomial u b) = if s = u.mapDomain pE then a * b * (wt c s : ℂ) else 0 := by
  rw [monomial_mul, contr_monomial]
  by_cases h : s = u.mapDomain pE
  · rw [if_pos ((bal_iff ε hs hu).mpr h), if_pos h, piC_eq_wt ε c hu h]
  · rw [if_neg (fun hb => h ((bal_iff ε hs hu).mp hb)), if_neg h]

/- English proof (translation)
Use `conv_lhs => rw [h.as_sum, g.as_sum, Finset.sum_mul_sum, contr_sum]`. Use `conv_rhs => rw [h.as_sum, g.as_sum, map_sum, bf_sum_left]`. Use `Finset.sum_congr rfl fun s hs => ?_` and prove the remaining obligations. Rewrite using `[contr_sum, bf_sum_right]`. Use `Finset.sum_congr rfl fun u hu => ?_` and prove the remaining obligations.

Rewrite using `[contr_mono ε c ((mem_first_family_iff ε h).mp hh s hs) ((mem_second_family_iff ε g).mp hg u hu), rename_monomial, bf_monomial]`.
-/
theorem contr_eq_bf (ε : Fin m → Bool) (c : ℝ) {h g : PX m n} (hh : h ∈ F1 ε) (hg : g ∈ F2 ε) :
    contr c (h * g) = bf (fun s => (wt c s : ℂ)) h (rename pE g) := by
  conv_lhs => rw [h.as_sum, g.as_sum, Finset.sum_mul_sum, contr_sum]
  conv_rhs => rw [h.as_sum, g.as_sum, map_sum, bf_sum_left]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [contr_sum, bf_sum_right]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [contr_mono ε c ((mem_first_family_iff ε h).mp hh s hs) ((mem_second_family_iff ε g).mp hg u hu), rename_monomial, bf_monomial]

/- English proof (translation)
Rewrite using `[contr_eq_bf ε c (variable_mul_mem_first_family ε hk hh) hg, contr_eq_bf ε c hh (partial_deriv_mem_second_family ε _ hg), bf_X_mul _ (wt_step c)]`. Use `congr 2`. Use `pderiv_rename (R := ℂ) (τ := Fin m × Fin n × Bool) (σ := Fin m × Fin n × Bool) pE.injective (pE k) g` as an intermediate fact. Rewrite `this` using `[pE_pE]`. Conclude with `this`.
-/
theorem T1 (ε : Fin m → Bool) {c : ℝ} {k} (hk : inF1 ε k) {h g : PX m n} (hh : h ∈ F1 ε) (hg : g ∈ F2 ε) :
    contr c (X k * h * g) = ((2 * c : ℝ) : ℂ) * contr c (h * pderiv (pE k) g) := by
  rw [contr_eq_bf ε c (variable_mul_mem_first_family ε hk hh) hg, contr_eq_bf ε c hh (partial_deriv_mem_second_family ε _ hg), bf_X_mul _ (wt_step c)]
  congr 2
  have := pderiv_rename (R := ℂ) (τ := Fin m × Fin n × Bool) (σ := Fin m × Fin n × Bool) pE.injective (pE k) g
  rw [pE_pE] at this
  exact this

/- English proof (translation)
Rewrite using `[contr_eq_bf ε c (partial_deriv_mem_first_family ε _ hh) hg, contr_eq_bf ε c hh (variable_mul_mem_second_family ε (fun h' => (first_family_partner_iff ε k).mp h' hk) hg), bf_pderiv _ (wt_step c)]`. Use `congr 1`. Rewrite using `[map_mul, rename_X, pE_pE]`.
-/
theorem T2 (ε : Fin m → Bool) {c : ℝ} {k} (hk : inF1 ε k) {h g : PX m n} (hh : h ∈ F1 ε) (hg : g ∈ F2 ε) :
    ((2 * c : ℝ) : ℂ) * contr c (pderiv k h * g) = contr c (h * (X (pE k) * g)) := by
  rw [contr_eq_bf ε c (partial_deriv_mem_first_family ε _ hh) hg,
    contr_eq_bf ε c hh (variable_mul_mem_second_family ε (fun h' => (first_family_partner_iff ε k).mp h' hk) hg), bf_pderiv _ (wt_step c)]
  congr 1
  rw [map_mul, rename_X, pE_pE]

end CoreC

end PositivityTheory.Rg.Sw.LC
