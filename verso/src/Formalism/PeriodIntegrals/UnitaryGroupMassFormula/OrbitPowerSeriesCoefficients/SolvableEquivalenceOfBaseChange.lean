import Mathlib

noncomputable section

open Classical

namespace PI.OrbShared.Tri

open MvPowerSeries Finsupp

variable {K : Type*} [Field K] {σ : Type*} [Finite σ]

def IsTri (c : K) (a : σ → MvPowerSeries σ K) : Prop :=
  ∀ v (n : σ →₀ ℕ), n.degree ≤ 1 → coeff n (a v) = if n = single v 1 then c else 0

def P (a : σ → MvPowerSeries σ K) (d : σ →₀ ℕ) : MvPowerSeries σ K := d.prod fun s e => (a s) ^ e

variable {c : K} {a : σ → MvPowerSeries σ K}

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem IsTri.constantCoeff (ha : IsTri c a) (v : σ) : constantCoeff (a v) = 0 := by
  have h := ha v 0 (by simp)
  rw [← coeff_zero_eq_constantCoeff_apply, h, if_neg (Ne.symm (Finsupp.single_ne_zero.mpr one_ne_zero))]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem IsTri.hasSubst (ha : IsTri c a) : HasSubst a :=
  hasSubst_of_constantCoeff_zero fun v => ha.constantCoeff v

/- English proof (translation)
Move the embeddings inside the algebraic operations. A detailed English derivation is pending.
-/
theorem ord_mul {f g : MvPowerSeries σ K} {m n : ℕ} (hf : (m : ℕ∞) ≤ f.order) (hg : (n : ℕ∞) ≤ g.order) :
    ((m + n : ℕ) : ℕ∞) ≤ (f * g).order := by
  push_cast
  exact (add_le_add hf hg).trans le_order_mul

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ord_add {f g : MvPowerSeries σ K} {n : ℕ} (hf : (n : ℕ∞) ≤ f.order) (hg : (n : ℕ∞) ≤ g.order) :
    (n : ℕ∞) ≤ (f + g).order :=
  (le_min hf hg).trans min_order_le_add

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem ord_pow {f : MvPowerSeries σ K} (hf : 1 ≤ f.order) (n : ℕ) : (n : ℕ∞) ≤ (f ^ n).order := by
  refine le_trans ?_ (le_order_pow n)
  have := nsmul_le_nsmul_right hf n
  simpa using this

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem ord_pow_sub {x y : MvPowerSeries σ K} (hx : 1 ≤ x.order) (hy : 1 ≤ y.order)
    (hxy : ((2 : ℕ) : ℕ∞) ≤ (y - x).order) (n : ℕ) : ((n + 1 : ℕ) : ℕ∞) ≤ (y ^ n - x ^ n).order := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show y ^ (n + 1) - x ^ (n + 1) = y ^ n * (y - x) + (y ^ n - x ^ n) * x by ring]
    apply ord_add
    · have := ord_mul (ord_pow hy n) hxy
      exact le_trans (by norm_cast) this
    · have := ord_mul ih (n := 1) (by simpa using hx)
      exact le_trans (by norm_cast) this

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation.

A detailed English derivation is pending.
-/
theorem ord_prod_sub {ι : Type*} (S : Finset ι) (x y : ι → MvPowerSeries σ K) (d : ι → ℕ)
    (hx : ∀ i, 1 ≤ (x i).order) (hy : ∀ i, 1 ≤ (y i).order)
    (hxy : ∀ i, ((2 : ℕ) : ℕ∞) ≤ (y i - x i).order) :
    ((∑ i ∈ S, d i : ℕ) : ℕ∞) ≤ (∏ i ∈ S, x i ^ d i).order ∧
      ((∑ i ∈ S, d i + 1 : ℕ) : ℕ∞) ≤ (∏ i ∈ S, y i ^ d i - ∏ i ∈ S, x i ^ d i).order := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert j S hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
    refine ⟨ord_mul (ord_pow (hx j) _) ih.1, ?_⟩
    rw [show y j ^ d j * ∏ i ∈ S, y i ^ d i - x j ^ d j * ∏ i ∈ S, x i ^ d i =
      y j ^ d j * (∏ i ∈ S, y i ^ d i - ∏ i ∈ S, x i ^ d i) +
        (y j ^ d j - x j ^ d j) * ∏ i ∈ S, x i ^ d i by ring]
    apply ord_add
    · have := ord_mul (ord_pow (hy j) (d j)) ih.2
      exact le_trans (by norm_cast) this
    · have := ord_mul (ord_pow_sub (hx j) (hy j) (hxy j) (d j)) ih.1
      exact le_trans (by norm_cast <;> omega) this

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem prod_CX (d : σ →₀ ℕ) :
    (d.prod fun s e => (C c * X s : MvPowerSeries σ K) ^ e) = monomial d (c ^ d.degree) := by
  classical
  have key : ∀ S : Finset σ, (∏ s ∈ S, (C c * X s : MvPowerSeries σ K) ^ d s) =
      monomial (∑ s ∈ S, single s (d s)) (c ^ (∑ s ∈ S, d s)) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert j S hj ih =>
      rw [Finset.prod_insert hj, ih, Finset.sum_insert hj, Finset.sum_insert hj, mul_pow, X_pow_eq,
        ← map_pow, ← monomial_zero_eq_C_apply, monomial_mul_monomial, monomial_mul_monomial, zero_add,
        mul_one, pow_add]
  have hs : (∑ s ∈ d.support, single s (d s)) = d := Finsupp.sum_single d
  rw [Finsupp.prod, key, hs]
  rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem IsTri.order_one (ha : IsTri c a) (v : σ) : 1 ≤ (a v).order :=
  one_le_order_iff_constCoeff_eq_zero.mpr (ha.constantCoeff v)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Put the expressions in a common number system so they can be compared. Use linear arithmetic over natural numbers and integers.

Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem IsTri.order_sub (ha : IsTri c a) (v : σ) : ((2 : ℕ) : ℕ∞) ≤ (a v - C c * X v).order := by
  refine le_order fun n hn => ?_
  have hn' : n.degree ≤ 1 := by
    have : (n.degree : ℕ∞) < ((2 : ℕ) : ℕ∞) := hn
    norm_cast at this
    omega
  rw [map_sub, ha v n hn', coeff_C_mul, coeff_X]
  split_ifs <;> simp

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem coeff_P_of_le (ha : IsTri c a) (d e : σ →₀ ℕ) (he : e.degree ≤ d.degree) :
    coeff e (P a d) = if e = d then c ^ d.degree else 0 := by
  have hX : ∀ v, 1 ≤ (C c * X v : MvPowerSeries σ K).order := fun v =>
    one_le_order_iff_constCoeff_eq_zero.mpr (by simp)
  have h := (ord_prod_sub d.support (fun v => C c * X v) a d hX ha.order_one ha.order_sub).2
  have h0 : coeff e (P a d - d.prod fun s e => (C c * X s : MvPowerSeries σ K) ^ e) = 0 := by
    apply coeff_of_lt_order
    refine lt_of_lt_of_le ?_ h
    have : (∑ i ∈ d.support, d i) = d.degree := rfl
    rw [this]
    exact_mod_cast Nat.lt_succ_of_le he
  rw [map_sub, prod_CX, coeff_monomial, sub_eq_zero] at h0
  exact h0

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Express the relevant assertion in an equivalent form by its definition. Separate the alternatives or extract the components of the hypothesis.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. A detailed English derivation is pending.
-/
theorem coeff_subst_tri (ha : IsTri c a) (F : MvPowerSeries σ K) (e : σ →₀ ℕ) :
    coeff e (subst a F) = c ^ e.degree * coeff e F +
      ∑ᶠ d, if d.degree < e.degree then coeff d F * coeff e (P a d) else 0 := by
  rw [coeff_subst ha.hasSubst]
  have hterm : ∀ d : σ →₀ ℕ, coeff d F • coeff e (d.prod fun s e => (a s) ^ e) =
      (if d = e then c ^ e.degree * coeff e F else 0) +
        (if d.degree < e.degree then coeff d F * coeff e (P a d) else 0) := by
    intro d
    change coeff d F * coeff e (P a d) = _
    rcases lt_trichotomy d.degree e.degree with hlt | heq | hgt
    · have hne : d ≠ e := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
      rw [if_neg hne, if_pos hlt, zero_add]
    · rw [if_neg (show ¬ d.degree < e.degree by rw [heq]; exact lt_irrefl _), add_zero,
        coeff_P_of_le ha d e heq.ge]
      by_cases hde : d = e
      · subst hde; simp [mul_comm]
      · rw [if_neg hde, if_neg (Ne.symm hde), mul_zero]
    · have hne : d ≠ e := fun h => by rw [h] at hgt; exact lt_irrefl _ hgt
      rw [if_neg hne, if_neg (not_lt.mpr hgt.le), coeff_P_of_le ha d e hgt.le, if_neg (Ne.symm hne)]
      simp
  simp_rw [hterm]
  rw [finsum_add_distrib]
  · rw [finsum_eq_single _ e (fun d hd => if_neg hd), if_pos rfl]
  · apply Set.Finite.subset (Set.finite_singleton e)
    intro d hd
    by_contra h
    exact hd (if_neg h)
  · apply Set.Finite.subset (Finsupp.finite_of_degree_lt e.degree)
    intro d hd
    by_contra h
    exact hd (if_neg h)

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. A detailed English derivation is pending.
-/
theorem vanish_of_subst (hc : c ≠ 0) (ha : IsTri c a) (F : MvPowerSeries σ K) (n : ℕ)
    (h : ∀ m : σ →₀ ℕ, m.degree < n → coeff m (subst a F) = 0) :
    ∀ m : σ →₀ ℕ, m.degree < n → coeff m F = 0 := by
  have key : ∀ k, ∀ m : σ →₀ ℕ, m.degree = k → k < n → coeff m F = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro m hm hk
      have h1 := h m (hm ▸ hk)
      rw [coeff_subst_tri ha] at h1
      have h2 : (∑ᶠ d, if d.degree < m.degree then coeff d F * coeff m (P a d) else 0) = 0 := by
        apply finsum_eq_zero_of_forall_eq_zero
        intro d
        split_ifs with hd
        · rw [ih d.degree (hm ▸ hd) d rfl (lt_trans (hm ▸ hd) hk), zero_mul]
        · rfl
      rw [h2, add_zero] at h1
      exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ hc)
  exact fun m hm => key _ m rfl hm

def solvable_equivalence_of_base_change (c : K) (a : σ → MvPowerSeries σ K) (G : MvPowerSeries σ K) : ℕ → (σ →₀ ℕ) → K
  | 0 => fun _ => 0
  | k + 1 => fun m => if m.degree = k then
      (c ^ k)⁻¹ * (coeff m G - ∑ᶠ d, if d.degree < k then solvable_equivalence_of_base_change c a G k d * coeff m (P a d) else 0)
    else solvable_equivalence_of_base_change c a G k m

def sol (c : K) (a : σ → MvPowerSeries σ K) (G : MvPowerSeries σ K) : MvPowerSeries σ K :=
  fun m => solvable_equivalence_of_base_change c a G (m.degree + 1) m

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem triangular_solution_stable (G : MvPowerSeries σ K) :
    ∀ k (m : σ →₀ ℕ), m.degree < k → solvable_equivalence_of_base_change c a G k m = solvable_equivalence_of_base_change c a G (m.degree + 1) m := by
  intro k
  induction k with
  | zero => intro m hm; exact absurd hm (Nat.not_lt_zero _)
  | succ k ih =>
    intro m hm
    by_cases hk : m.degree = k
    · rw [hk]
    · have hlt : m.degree < k := by omega
      show (if m.degree = k then _ else solvable_equivalence_of_base_change c a G k m) = _
      rw [if_neg hk, ih m hlt]

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem subst_sol (hc : c ≠ 0) (ha : IsTri c a) (G : MvPowerSeries σ K) : subst a (sol c a G) = G := by
  ext m
  rw [coeff_subst_tri ha]
  have hsol : ∀ d : σ →₀ ℕ, coeff d (sol c a G) = solvable_equivalence_of_base_change c a G (d.degree + 1) d := fun d => rfl
  have hS : (∑ᶠ d, if d.degree < m.degree then coeff d (sol c a G) * coeff m (P a d) else 0) =
      ∑ᶠ d, if d.degree < m.degree then solvable_equivalence_of_base_change c a G m.degree d * coeff m (P a d) else 0 := by
    apply finsum_congr
    intro d
    split_ifs with hd
    · rw [hsol, triangular_solution_stable G m.degree d hd]
    · rfl
  rw [hS, hsol, solvable_equivalence_of_base_change.eq_2]
  beta_reduce
  rw [if_pos rfl, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hc), one_mul, sub_add_cancel]

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem surj (hc : c ≠ 0) (ha : IsTri c a) (G : MvPowerSeries σ K) :
    ∃ F : MvPowerSeries σ K, subst a F = G :=
  ⟨sol c a G, subst_sol hc ha G⟩

end PI.OrbShared.Tri

end
