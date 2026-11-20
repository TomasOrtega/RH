import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvDer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDerivationCoeffEqZeroOfDegreeLtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDerivationFormalGroupLawIsLinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDerivationFormalGroupLawLeibnizStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LawDer.MonoIter

variable {R : Type} [CommRing R] {d : ℕ}

/- English proof (translation)
Simplify using `[Finsupp.degree_eq_sum, Finset.sum_add_distrib]`.
-/
theorem degree_add' (a b : Fin d →₀ ℕ) : (a + b).degree = a.degree + b.degree := by
  simp [Finsupp.degree_eq_sum, Finset.sum_add_distrib]

/- English proof (translation)
Use `degree_add' (a - b) b` as an intermediate fact. Rewrite `this` using `[tsub_add_cancel_of_le h]`. Use linear arithmetic over natural numbers and integers.
-/
theorem degree_tsub {a b : Fin d →₀ ℕ} (h : b ≤ a) : (a - b).degree = a.degree - b.degree := by
  have := degree_add' (a - b) b
  rw [tsub_add_cancel_of_le h] at this
  omega

/- English proof (translation)
Apply the tactic sequence `have ha : HasSubst (Sum.elim (fun i => (X i : MvPowerSeries (Fin d) R)) fun _ : Fin d => 0) := hasSubst_of_constantCoeff_zero (by rintro (j|j) <;> simp)`. Unfold `atZero`. Rewrite using `[constantCoeff_subst ha, finsum_eq_single _ 0]`. Simplify using the standard rewrite rules. Introduce `e he`.

Choose the witnesses or unpack the hypotheses as in `⟨s, hs⟩ : ∃ s, e s ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `he (Finsupp.ext h)`. Establish `: constantCoeff (e.prod fun s n => (Sum.elim (fun i => (X i : MvPowerSeries (Fin d) R)) (fun _ : Fin d => 0) s) ^ n) = 0`.

Rewrite using `[map_finsuppProd, Finsupp.prod]`. Apply `Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hs)` to reduce the goal to its premises. Apply the tactic sequence `rcases s with j | j <;> simp [hs]`. Rewrite using `[this, smul_zero]`.
-/
theorem constantCoeff_atZero (H : MvPowerSeries (Fin d ⊕ Fin d) R) :
    constantCoeff (atZero H) = constantCoeff H := by
  have ha : HasSubst (Sum.elim (fun i => (X i : MvPowerSeries (Fin d) R)) fun _ : Fin d => 0) :=
    hasSubst_of_constantCoeff_zero (by rintro (j|j) <;> simp)
  unfold atZero
  rw [constantCoeff_subst ha, finsum_eq_single _ 0]
  · simp
  · intro e he
    obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext h)
    have : constantCoeff (e.prod fun s n =>
        (Sum.elim (fun i => (X i : MvPowerSeries (Fin d) R)) (fun _ : Fin d => 0) s) ^ n) = 0 := by
      rw [map_finsuppProd, Finsupp.prod]
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hs)
      rcases s with j | j <;> simp [hs]
    rw [this, smul_zero]

/- English proof (translation)
Establish `: ∀ s : Finset (Fin d), (∏ j ∈ s, (X j : MvPowerSeries (Fin d) R) ^ n j) = monomial (∑ j ∈ s, Finsupp.single j (n j)) 1`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [monomial_zero_eq_C_apply]`. Consider the case `insert a s ha ih`.

Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha, ih, X_pow_eq, monomial_mul_monomial, mul_one]`. Establish `hsum : (∑ j, Finsupp.single j (n j)) = Finsupp.equivFunOnFinite.symm n`. Use extensionality with `j`. Rewrite using `[Finsupp.finset_sum_apply, Finset.sum_eq_single j]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Simplify using `[Finsupp.single_apply, hb]`. Simplify using the standard rewrite rules. Rewrite using `[this, hsum]`.
-/
theorem prod_X_pow (n : Fin d → ℕ) :
    (∏ j, (X j : MvPowerSeries (Fin d) R) ^ n j) =
      monomial (Finsupp.equivFunOnFinite.symm n) 1 := by
  have : ∀ s : Finset (Fin d), (∏ j ∈ s, (X j : MvPowerSeries (Fin d) R) ^ n j) =
      monomial (∑ j ∈ s, Finsupp.single j (n j)) 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [monomial_zero_eq_C_apply]
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, X_pow_eq, monomial_mul_monomial, mul_one]
  have hsum : (∑ j, Finsupp.single j (n j)) = Finsupp.equivFunOnFinite.symm n := by
    ext j
    rw [Finsupp.finset_sum_apply, Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [Finsupp.single_apply, hb]
    · simp
  rw [this, hsum]

/- English proof (translation)
Apply the tactic sequence `have ha : HasSubst (Sum.elim (fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) fun j => X j) := hasSubst_of_constantCoeff_zero (by rintro (j|j) <;> simp)`. Establish `key : ∀ c : Fin d ⊕ Fin d →₀ ℕ, (c.prod fun s n => (Sum.elim (fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) (fun j => X j) s) ^ n) = (∏ j, (0 : MvPowerSeries (Fin d) R) ^ c (Sum.inl j)) * monomial (Finsupp.equivFunOnFinite.symm fun j => c (Sum.inr j)) 1`. Introduce `c`. Rewrite using `[Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sum_type]`. Use `congr 1`.

Conclude with `prod_X_pow _`. Establish `h1 : ∀ j : Fin d, (e.mapDomain (Sum.inr : Fin d → Fin d ⊕ Fin d)) (Sum.inl j) = 0` using `fun j => Finsupp.mapDomain_notin_range _ _ (by simp)`. Establish `h2 : ∀ j : Fin d, (e.mapDomain (Sum.inr : Fin d → Fin d ⊕ Fin d)) (Sum.inr j) = e j` using `fun j => Finsupp.mapDomain_apply Sum.inr_injective _ _`. Rewrite using `[coeff_subst ha, finsum_eq_single _ (e.mapDomain Sum.inr)]`. Rewrite using `[key]`.

Establish `h3 : (Finsupp.equivFunOnFinite.symm fun j : Fin d => (e.mapDomain (Sum.inr : Fin d → Fin d ⊕ Fin d)) (Sum.inr j)) = e`. Use extensionality with `j`. Simplify using `[h2]`. Simplify using `[h1, h3]`. Introduce `c hc`.

Rewrite using `[key]`. Distinguish the cases in `h : ∀ j, c (Sum.inl j) = 0`. Establish `hne : (Finsupp.equivFunOnFinite.symm fun j => c (Sum.inr j)) ≠ e`. Introduce `heq`. Apply `hc` to reduce the goal to its premises.

Use extensionality with `(j|j)`. Rewrite using `[h1, h j]`. Rewrite using `[h2, ← heq]`. Simplify using the standard rewrite rules. Simplify using `[h, coeff_monomial, Ne.symm hne]`.

Use `push_neg at h`. Take `⟨j, hj⟩` from `h`. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ j) (zero_pow hj)]`. Simplify using the standard rewrite rules.
-/
theorem coeff_subst_zero_X (H : MvPowerSeries (Fin d ⊕ Fin d) R) (e : Fin d →₀ ℕ) :
    coeff e (subst (Sum.elim (fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) fun j => X j) H) =
      coeff (e.mapDomain Sum.inr) H := by
  have ha : HasSubst (Sum.elim (fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) fun j => X j) :=
    hasSubst_of_constantCoeff_zero (by rintro (j|j) <;> simp)
  have key : ∀ c : Fin d ⊕ Fin d →₀ ℕ, (c.prod fun s n =>
      (Sum.elim (fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) (fun j => X j) s) ^ n) =
      (∏ j, (0 : MvPowerSeries (Fin d) R) ^ c (Sum.inl j)) *
        monomial (Finsupp.equivFunOnFinite.symm fun j => c (Sum.inr j)) 1 := by
    intro c
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sum_type]
    congr 1
    exact prod_X_pow _
  have h1 : ∀ j : Fin d, (e.mapDomain (Sum.inr : Fin d → Fin d ⊕ Fin d)) (Sum.inl j) = 0 := fun j =>
    Finsupp.mapDomain_notin_range _ _ (by simp)
  have h2 : ∀ j : Fin d, (e.mapDomain (Sum.inr : Fin d → Fin d ⊕ Fin d)) (Sum.inr j) = e j := fun j =>
    Finsupp.mapDomain_apply Sum.inr_injective _ _
  rw [coeff_subst ha, finsum_eq_single _ (e.mapDomain Sum.inr)]
  · rw [key]
    have h3 : (Finsupp.equivFunOnFinite.symm fun j : Fin d => (e.mapDomain (Sum.inr : Fin d → Fin d ⊕ Fin d)) (Sum.inr j)) = e := by
      ext j
      simp [h2]
    simp [h1, h3]
  · intro c hc
    rw [key]
    by_cases h : ∀ j, c (Sum.inl j) = 0
    · have hne : (Finsupp.equivFunOnFinite.symm fun j => c (Sum.inr j)) ≠ e := by
        intro heq
        apply hc
        ext (j|j)
        · rw [h1, h j]
        · rw [h2, ← heq]
          simp
      simp [h, coeff_monomial, Ne.symm hne]
    · push_neg at h
      obtain ⟨j, hj⟩ := h
      rw [Finset.prod_eq_zero (Finset.mem_univ j) (zero_pow hj)]
      simp

/- English proof (translation)
Apply the tactic sequence `have hb : HasSubst (Sum.elim (fun i => (X i : MvPowerSeries (Fin d) R)) fun _ : Fin d => 0) := hasSubst_of_constantCoeff_zero (by rintro (j|j) <;> simp)`. Apply the tactic sequence `have hc : HasSubst (Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) R)) (fun j => X (Sum.inl j))) := hasSubst_of_constantCoeff_zero (by rintro (j|j) <;> simp)`. Establish `h1 : subst (Sum.elim (fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) fun j => X j) (μ i) = X i`. Establish `h` using `congrFun hunit i`. Simplify using `only [op, at2] at h`.

Rewrite `h` using `[← hswap i, swap, at2, subst_comp_subst_apply hc hb]`. Rewrite using `[← h]`. Use `congr 1`. Use function extensionality and compare the values at `s`. Apply the tactic sequence `rcases s with j | j <;> simp [subst_X hb]`.

Establish `h2` using `coeff_subst_zero_X (μ i) (Finsupp.single k 1)`. Rewrite `h2` using `[h1, Finsupp.mapDomain_single, coeff_X]`. Rewrite using `[← h2]`. Distinguish the cases in `hki : k = i`. Simplify using `[hki]`.

Rewrite using `[if_neg, if_neg hki]`. Introduce `h`. Conclude with `hki (Finsupp.single_left_injective one_ne_zero h)`.
-/
theorem coeff_inr_of_unit (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hunit : op μ (fun i => (X i : MvPowerSeries (Fin d) R)) (fun _ : Fin d => 0) = fun i => X i)
    (hswap : ∀ i, swap (μ i) = μ i) (i k : Fin d) :
    coeff (Finsupp.single (Sum.inr k) 1) (μ i) = if k = i then 1 else 0 := by
  have hb : HasSubst (Sum.elim (fun i => (X i : MvPowerSeries (Fin d) R)) fun _ : Fin d => 0) :=
    hasSubst_of_constantCoeff_zero (by rintro (j|j) <;> simp)
  have hc : HasSubst (Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) R))
      (fun j => X (Sum.inl j))) :=
    hasSubst_of_constantCoeff_zero (by rintro (j|j) <;> simp)
  have h1 : subst (Sum.elim (fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) fun j => X j) (μ i) = X i := by
    have h := congrFun hunit i
    simp only [op, at2] at h
    rw [← hswap i, swap, at2, subst_comp_subst_apply hc hb] at h
    rw [← h]
    congr 1
    funext s
    rcases s with j | j <;> simp [subst_X hb]
  have h2 := coeff_subst_zero_X (μ i) (Finsupp.single k 1)
  rw [h1, Finsupp.mapDomain_single, coeff_X] at h2
  rw [← h2]
  by_cases hki : k = i
  · simp [hki]
  · rw [if_neg, if_neg hki]
    intro h
    exact hki (Finsupp.single_left_injective one_ne_zero h)

/- English proof (translation)
Establish `hμ : HasSubst μ` using `hasSubst_of_constantCoeff_zero hc`. Establish `hp : ∀ k, constantCoeff (pderiv R (Sum.inr k) (μ i)) = if k = i then 1 else 0`. Introduce `k`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add, coeff_inr_of_unit μ hunit hswap]`. Simplify using the standard rewrite rules.

Simplify using `only [invDer, subst_X hμ, map_sum, smul_eq_C_mul, map_mul, constantCoeff_C, constantCoeff_atZero, hp]`. Simplify using the standard rewrite rules.
-/
theorem constantCoeff_invDer_X (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hc : ∀ i, constantCoeff (μ i) = 0)
    (hunit : op μ (fun i => (X i : MvPowerSeries (Fin d) R)) (fun _ : Fin d => 0) = fun i => X i)
    (hswap : ∀ i, swap (μ i) = μ i) (u : Fin d → R) (i : Fin d) :
    constantCoeff (invDer μ u (X i)) = u i := by
  have hμ : HasSubst μ := hasSubst_of_constantCoeff_zero hc
  have hp : ∀ k, constantCoeff (pderiv R (Sum.inr k) (μ i)) = if k = i then 1 else 0 := by
    intro k
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add, coeff_inr_of_unit μ hunit hswap]
    simp
  simp only [invDer, subst_X hμ, map_sum, smul_eq_C_mul, map_mul, constantCoeff_C,
    constantCoeff_atZero, hp]
  simp

end GlobalTheory.LawDer.MonoIter

namespace GlobalTheory.LawDer.MonoIter

variable {R : Type} [CommRing R] {d : ℕ}

/- English proof (translation)
Take `⟨hadd, hsmul, hC⟩` from `GlobalTheory.T.invariantDerivationFormalGroupLaw_isLinear R d μ hc u`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `α hα`.

Establish `: α = 0` using `(Finsupp.degree_eq_zero_iff α).1 hα`. Substitute `this` using the available equality. Use `⟨0, fun β hβ => by simp, ?_⟩` and prove the remaining obligations. Rewrite using `[monomial_zero_eq_C_apply, hC]`. Simplify using the standard rewrite rules.

Consider the case `succ n ih`. Introduce `α hα`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, α i ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Establish `: α = 0` using `Finsupp.ext h`. Substitute `this` using the available equality. Simplify using `at hα`. Take `⟨α', hα'⟩ : ∃ α', α' = α - Finsupp.single i 1` from `⟨_, rfl⟩`. Establish `hle : Finsupp.single i 1 ≤ α` using `Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hi)`.

Establish `hsplit : α = α' + Finsupp.single i 1` using `by rw [hα', tsub_add_cancel_of_le hle]`. Establish `hdeg : α'.degree = n`. Use `congrArg Finsupp.degree hsplit` as an intermediate fact. Rewrite `this` using `[degree_add', Finsupp.degree_single, hα]`. Use linear arithmetic over natural numbers and integers.

Take `⟨G, hG, hD⟩` from `ih α' hdeg`. Use `set Ri := invDer μ u (X i) - C (u i) with hRi`. Establish `hR : constantCoeff Ri = 0`. Simplify using `[Ri, constantCoeff_invDer_X μ hc hunit hswap]`. Establish `hmono : monomial α (1 : R) = monomial α' 1 * X i`.

Rewrite using `[X_def, monomial_mul_monomial, mul_one, ← hsplit]`. Establish `hterm : ∀ j, ((α' j : R) * u j) • monomial (α' - Finsupp.single j 1) (1 : R) * X i + (if j = i then u i • monomial α' (1 : R) else 0) = ((α j : R) * u j) • monomial (α - Finsupp.single j 1) 1`. Introduce `j`. Establish `hαj : α j = α' j + if j = i then 1 else 0` using `by conv_lhs => rw [hsplit]`. Rewrite using `[Finsupp.add_apply, Finsupp.single_apply]`.

Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h, Ne.symm h]`. Distinguish the cases in `h0 : α' j = 0`.

Distinguish the cases in `hji : j = i`. Substitute `hji` using the available equality. Rewrite using `[← hα', hαj, h0]`. Simplify using the standard rewrite rules. Simplify using `[h0, hαj, hji]`.

Establish `hle' : Finsupp.single j 1 ≤ α'` using `Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 h0)`. Establish `hm : monomial (α' - Finsupp.single j 1) (1 : R) * X i = monomial (α - Finsupp.single j 1) 1`. Establish `he : α' - Finsupp.single j 1 + Finsupp.single i 1 = α - Finsupp.single j 1`. Rewrite using `[hsplit]`. Use extensionality with `k`.

Simplify using `only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]`. Use `Nat.one_le_iff_ne_zero.2 h0` as an intermediate fact. Distinguish the cases in `hk : j = k`. Apply the tactic sequence `subst hk split_ifs <;> omega`. Apply the tactic sequence `split_ifs <;> omega`.

Rewrite using `[X_def, monomial_mul_monomial, mul_one, he]`. Rewrite using `[smul_mul_assoc, hm, hαj]`. Use `split_ifs with hji`. Substitute `hji` using the available equality. Rewrite using `[← hα']`.

Use `push_cast`. Rewrite using `[add_mul, one_mul, add_smul]`. Simplify using the standard rewrite rules. Use `⟨G * X i + monomial α' 1 * Ri, ?_, ?_⟩` and prove the remaining obligations. Introduce `β hβ`.

Rewrite using `[map_add, X_def, coeff_mul_monomial, coeff_monomial_mul]`. Establish `h1 : (if Finsupp.single i 1 ≤ β then coeff (β - Finsupp.single i 1) G * 1 else 0) = 0` using `by split_ifs with h`. Use `degree_add' (β - Finsupp.single i 1) (Finsupp.single i 1)` as an intermediate fact. Rewrite `this` using `[tsub_add_cancel_of_le h, Finsupp.degree_single]`. Rewrite using `[hG _ (by omega), zero_mul]`.

Both sides reduce to the same expression. Establish `h2 : (if α' ≤ β then 1 * coeff (β - α') Ri else 0) = 0` using `by split_ifs with h`. Establish `h3 : β - α' = 0`. Rewrite using `[← Finsupp.degree_eq_zero_iff, degree_tsub h]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[h3, coeff_zero_eq_constantCoeff_apply, hR, mul_zero]`. Both sides reduce to the same expression. Rewrite using `[h1, h2, add_zero]`. Establish `hXi : invDer μ u (X i) = C (u i) + Ri` using `by rw [hRi]; ring`. Rewrite using `[hmono, GlobalTheory.T.invariantDerivationFormalGroupLaw_leibniz R d μ hc hunit u, hD, hXi, ← Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ _)]`.

Rewrite using `[add_mul, Finset.sum_mul, smul_eq_C_mul (monomial α' (1 : R)) (u i)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem invDer_monomial (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hc : ∀ i, constantCoeff (μ i) = 0)
    (hunit : op μ (fun i => (X i : MvPowerSeries (Fin d) R)) (fun _ => 0) = fun i => X i)
    (hswap : ∀ i, swap (μ i) = μ i) (u : Fin d → R) :
    ∀ (n : ℕ) (α : Fin d →₀ ℕ), α.degree = n → ∃ G : MvPowerSeries (Fin d) R,
      (∀ β : Fin d →₀ ℕ, β.degree < n → coeff β G = 0) ∧
      invDer μ u (monomial α 1) =
        ∑ j, ((α j : R) * u j) • monomial (α - Finsupp.single j 1) (1 : R) + G := by
  obtain ⟨hadd, hsmul, hC⟩ := GlobalTheory.T.invariantDerivationFormalGroupLaw_isLinear R d μ hc u
  intro n
  induction n with
  | zero =>
    intro α hα
    have : α = 0 := (Finsupp.degree_eq_zero_iff α).1 hα
    subst this
    refine ⟨0, fun β hβ => by simp, ?_⟩
    rw [monomial_zero_eq_C_apply, hC]
    simp
  | succ n ih =>
    intro α hα
    obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
      by_contra h
      push_neg at h
      have : α = 0 := Finsupp.ext h
      subst this
      simp at hα
    obtain ⟨α', hα'⟩ : ∃ α', α' = α - Finsupp.single i 1 := ⟨_, rfl⟩
    have hle : Finsupp.single i 1 ≤ α := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hi)
    have hsplit : α = α' + Finsupp.single i 1 := by rw [hα', tsub_add_cancel_of_le hle]
    have hdeg : α'.degree = n := by
      have := congrArg Finsupp.degree hsplit
      rw [degree_add', Finsupp.degree_single, hα] at this
      omega
    obtain ⟨G, hG, hD⟩ := ih α' hdeg
    set Ri := invDer μ u (X i) - C (u i) with hRi
    have hR : constantCoeff Ri = 0 := by
      simp [Ri, constantCoeff_invDer_X μ hc hunit hswap]
    have hmono : monomial α (1 : R) = monomial α' 1 * X i := by
      rw [X_def, monomial_mul_monomial, mul_one, ← hsplit]
    have hterm : ∀ j, ((α' j : R) * u j) • monomial (α' - Finsupp.single j 1) (1 : R) * X i +
        (if j = i then u i • monomial α' (1 : R) else 0) =
        ((α j : R) * u j) • monomial (α - Finsupp.single j 1) 1 := by
      intro j
      have hαj : α j = α' j + if j = i then 1 else 0 := by
        conv_lhs => rw [hsplit]
        rw [Finsupp.add_apply, Finsupp.single_apply]
        by_cases h : j = i
        · subst h; simp
        · simp [h, Ne.symm h]
      by_cases h0 : α' j = 0
      · by_cases hji : j = i
        · subst hji
          rw [← hα', hαj, h0]
          simp
        · simp [h0, hαj, hji]
      · have hle' : Finsupp.single j 1 ≤ α' :=
          Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 h0)
        have hm : monomial (α' - Finsupp.single j 1) (1 : R) * X i =
            monomial (α - Finsupp.single j 1) 1 := by
          have he : α' - Finsupp.single j 1 + Finsupp.single i 1 = α - Finsupp.single j 1 := by
            rw [hsplit]
            ext k
            simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
            have := Nat.one_le_iff_ne_zero.2 h0
            by_cases hk : j = k
            · subst hk
              split_ifs <;> omega
            · split_ifs <;> omega
          rw [X_def, monomial_mul_monomial, mul_one, he]
        rw [smul_mul_assoc, hm, hαj]
        split_ifs with hji
        · subst hji
          rw [← hα']
          push_cast
          rw [add_mul, one_mul, add_smul]
        · simp
    refine ⟨G * X i + monomial α' 1 * Ri, ?_, ?_⟩
    · intro β hβ
      rw [map_add, X_def, coeff_mul_monomial, coeff_monomial_mul]
      have h1 : (if Finsupp.single i 1 ≤ β then coeff (β - Finsupp.single i 1) G * 1 else 0) = 0 := by
        split_ifs with h
        · have := degree_add' (β - Finsupp.single i 1) (Finsupp.single i 1)
          rw [tsub_add_cancel_of_le h, Finsupp.degree_single] at this
          rw [hG _ (by omega), zero_mul]
        · rfl
      have h2 : (if α' ≤ β then 1 * coeff (β - α') Ri else 0) = 0 := by
        split_ifs with h
        · have h3 : β - α' = 0 := by
            rw [← Finsupp.degree_eq_zero_iff, degree_tsub h]
            omega
          rw [h3, coeff_zero_eq_constantCoeff_apply, hR, mul_zero]
        · rfl
      rw [h1, h2, add_zero]
    · have hXi : invDer μ u (X i) = C (u i) + Ri := by rw [hRi]; ring
      rw [hmono, GlobalTheory.T.invariantDerivationFormalGroupLaw_leibniz R d μ hc hunit u, hD, hXi, ← Finset.sum_congr rfl (fun j _ => hterm j),
        Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ _)]
      rw [add_mul, Finset.sum_mul, smul_eq_C_mul (monomial α' (1 : R)) (u i)]
      ring

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro m F h β hβ; exact h β (by simpa using hβ)`. Consider the case `succ k ih`. Introduce `m F h β hβ`.

Rewrite using `[Function.iterate_succ_apply]`. Use `ih m _ (fun γ hγ => GlobalTheory.T.invariantDerivation_coeff_eq_zero_of_degree_lt R d μ hc u F (m + k) ?_ γ hγ) β hβ` and prove the remaining obligations. Introduce `δ hδ`. Conclude with `h δ (by omega)`.
-/
theorem iterate_order (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hc : ∀ i, constantCoeff (μ i) = 0) (u : Fin d → R) :
    ∀ (k m : ℕ) (F : MvPowerSeries (Fin d) R), (∀ β : Fin d →₀ ℕ, β.degree < m + k → coeff β F = 0) →
      ∀ β : Fin d →₀ ℕ, β.degree < m → coeff β ((invDer μ u)^[k] F) = 0 := by
  intro k
  induction k with
  | zero => intro m F h β hβ; exact h β (by simpa using hβ)
  | succ k ih =>
    intro m F h β hβ
    rw [Function.iterate_succ_apply]
    refine ih m _ (fun γ hγ => GlobalTheory.T.invariantDerivation_coeff_eq_zero_of_degree_lt R d μ hc u F (m + k) ?_ γ hγ) β hβ
    intro δ hδ
    exact h δ (by omega)

end GlobalTheory.LawDer.MonoIter

namespace GlobalTheory.LawDer.MonoIter

/- English proof (translation)
Introduce `R _ d μ hc hunit hswap u`. Take `⟨hadd, hsmul, hC⟩` from `GlobalTheory.T.invariantDerivationFormalGroupLaw_isLinear R d μ hc u`. Set `L : Module.End R (MvPowerSeries (Fin d) R)` to `{ toFun := invDer μ u, map_add' := hadd, map_smul' := hsmul }`. Establish `hL : ∀ (k : ℕ) (F : MvPowerSeries (Fin d) R), (invDer μ u)^[k] F = (L ^ k) F` using `fun k F => (Module.End.pow_apply L k F).symm`. It suffices to establish `h : ∀ (n : ℕ) (α : Fin d →₀ ℕ), α.degree = n → constantCoeff ((invDer μ u)^[n] (monomial α (1 : R))) = (n.factorial : R) * ∏ i, u i ^ α i from fun α => h _ α rfl`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `α hα`. Establish `: α = 0` using `(Finsupp.degree_eq_zero_iff α).1 hα`.

Substitute `this` using the available equality. Simplify using `[monomial_zero_eq_C_apply]`. Consider the case `succ n ih`. Introduce `α hα`. Take `⟨G, hG, hD⟩` from `invDer_monomial μ hc hunit hswap u (n + 1) α hα`.

Establish `hG0 : constantCoeff ((invDer μ u)^[n] G) = 0`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply]`. Conclude with `iterate_order μ hc u n 1 G (fun β hβ => hG β (by omega)) 0 (by simp)`. Establish `hterm : ∀ j, constantCoeff ((invDer μ u)^[n] (((α j : R) * u j) • monomial (α - Finsupp.single j 1) (1 : R))) = (α j : R) * ((n.factorial : R) * ∏ i, u i ^ α i)`. Introduce `j`.

Rewrite using `[hL, map_smul, ← hL, smul_eq_C_mul, map_mul, constantCoeff_C]`. Distinguish the cases in `h0 : α j = 0`. Simplify using `[h0]`. Establish `hle' : Finsupp.single j 1 ≤ α` using `Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 h0)`. Establish `hdeg : (α - Finsupp.single j 1).degree = n`.

Rewrite using `[degree_tsub hle', Finsupp.degree_single, hα]`. Both sides reduce to the same expression. Rewrite using `[ih _ hdeg]`. Establish `hp : ∏ i, u i ^ α i = u j * ∏ i, u i ^ (α - Finsupp.single j 1 : Fin d →₀ ℕ) i` using `by conv_lhs => rw [← tsub_add_cancel_of_le hle']`. Simplify using `only [Finsupp.add_apply, pow_add, Finset.prod_mul_distrib]`.

Rewrite using `[mul_comm]`. Use `congr 1`. Rewrite using `[Finset.prod_eq_single j]`. Simplify using the standard rewrite rules. Introduce `b _ hb`.

Simplify using `[Finsupp.single_apply, Ne.symm hb]`. Simplify using the standard rewrite rules. Rewrite using `[hp]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Function.iterate_succ_apply, hD, hL, map_add, map_sum, ← hL, map_add, map_sum]`.

Simplify using `only [← hL]`. Rewrite using `[hG0, add_zero, Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.sum_mul]`. Establish `hs : (∑ j, (α j : R)) = ((n + 1 : ℕ) : R)`. Rewrite using `[← Nat.cast_sum, ← Finsupp.degree_eq_sum, hα]`. Rewrite using `[hs, Nat.factorial_succ]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem constantCoeff_iterate_invDer_monomial : ∀ (R : Type) [CommRing R] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) →
    op μ (fun i => (X i : MvPowerSeries (Fin d) R)) (fun _ => 0) = (fun i => X i) →
    (∀ i, swap (μ i) = μ i) → ∀ (u : Fin d → R) (α : Fin d →₀ ℕ),
    constantCoeff ((invDer μ u)^[α.degree] (monomial α (1 : R))) =
      (α.degree.factorial : R) * ∏ i, u i ^ α i := by
  intro R _ d μ hc hunit hswap u
  obtain ⟨hadd, hsmul, hC⟩ := GlobalTheory.T.invariantDerivationFormalGroupLaw_isLinear R d μ hc u
  let L : Module.End R (MvPowerSeries (Fin d) R) :=
    { toFun := invDer μ u, map_add' := hadd, map_smul' := hsmul }
  have hL : ∀ (k : ℕ) (F : MvPowerSeries (Fin d) R), (invDer μ u)^[k] F = (L ^ k) F :=
    fun k F => (Module.End.pow_apply L k F).symm
  suffices h : ∀ (n : ℕ) (α : Fin d →₀ ℕ), α.degree = n →
      constantCoeff ((invDer μ u)^[n] (monomial α (1 : R))) = (n.factorial : R) * ∏ i, u i ^ α i from
    fun α => h _ α rfl
  intro n
  induction n with
  | zero =>
    intro α hα
    have : α = 0 := (Finsupp.degree_eq_zero_iff α).1 hα
    subst this
    simp [monomial_zero_eq_C_apply]
  | succ n ih =>
    intro α hα
    obtain ⟨G, hG, hD⟩ := invDer_monomial μ hc hunit hswap u (n + 1) α hα
    have hG0 : constantCoeff ((invDer μ u)^[n] G) = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply]
      exact iterate_order μ hc u n 1 G (fun β hβ => hG β (by omega)) 0 (by simp)
    have hterm : ∀ j, constantCoeff ((invDer μ u)^[n]
        (((α j : R) * u j) • monomial (α - Finsupp.single j 1) (1 : R))) =
        (α j : R) * ((n.factorial : R) * ∏ i, u i ^ α i) := by
      intro j
      rw [hL, map_smul, ← hL, smul_eq_C_mul, map_mul, constantCoeff_C]
      by_cases h0 : α j = 0
      · simp [h0]
      · have hle' : Finsupp.single j 1 ≤ α :=
          Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 h0)
        have hdeg : (α - Finsupp.single j 1).degree = n := by
          rw [degree_tsub hle', Finsupp.degree_single, hα]
          rfl
        rw [ih _ hdeg]
        have hp : ∏ i, u i ^ α i = u j * ∏ i, u i ^ (α - Finsupp.single j 1 : Fin d →₀ ℕ) i := by
          conv_lhs => rw [← tsub_add_cancel_of_le hle']
          simp only [Finsupp.add_apply, pow_add, Finset.prod_mul_distrib]
          rw [mul_comm]
          congr 1
          rw [Finset.prod_eq_single j]
          · simp
          · intro b _ hb
            simp [Finsupp.single_apply, Ne.symm hb]
          · simp
        rw [hp]
        ring
    rw [Function.iterate_succ_apply, hD, hL, map_add, map_sum, ← hL, map_add, map_sum]
    simp only [← hL]
    rw [hG0, add_zero, Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.sum_mul]
    have hs : (∑ j, (α j : R)) = ((n + 1 : ℕ) : R) := by
      rw [← Nat.cast_sum, ← Finsupp.degree_eq_sum, hα]
    rw [hs, Nat.factorial_succ]
    push_cast
    ring

end GlobalTheory.LawDer.MonoIter
