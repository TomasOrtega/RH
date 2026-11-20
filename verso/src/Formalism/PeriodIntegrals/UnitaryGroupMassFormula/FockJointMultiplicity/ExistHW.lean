import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.JointMultOfSteps
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.ExistGen

open MvPolynomial FockH1Action PI.FJM

noncomputable section

namespace PI.FJMX

variable {p q r s : ℕ}

/- English proof (translation)
Rewrite using `[← Derivation.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]`. Both sides reduce to the same expression.
-/
theorem der_sum_apply {ι : Type*} (t : Finset ι) (D : ι → Derivation ℂ (Pol p q r s) (Pol p q r s))
    (f : Pol p q r s) : (∑ c ∈ t, D c) f = ∑ c ∈ t, D c f := by
  rw [← Derivation.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
  rfl

def der1 (a b : Ix p q) : Derivation ℂ (Pol p q r s) (Pol p q r s) :=
  ∑ c : Ix r s, if linePos (a, c) = true then (X (a, c) : Pol p q r s) • pderiv (b, c)
    else -((X (b, c) : Pol p q r s) • pderiv (a, c))

def der2 (c d : Ix r s) : Derivation ℂ (Pol p q r s) (Pol p q r s) :=
  ∑ a : Ix p q, if linePos (a, c) = true then (X (a, c) : Pol p q r s) • pderiv (a, d)
    else -((X (a, d) : Pol p q r s) • pderiv (a, c))

/- English proof (translation)
Rewrite using `[der1, der_sum_apply, Finset.sum_eq_single v.2]`. Take `⟨v1, v2⟩` from `v`. Distinguish the cases in `h : linePos (a, v2) = true`. Simplify using `only [h, if_true, Derivation.smul_apply, pderiv_X, smul_eq_mul]`. Distinguish the cases in `hb : v1 = b`.

Substitute `hb` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hb]`. Simplify using `only [h, if_false, Derivation.neg_apply, Derivation.smul_apply, pderiv_X, smul_eq_mul]`. Distinguish the cases in `ha : v1 = a`.

Substitute `ha` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, ha]`. Introduce `c _ hc`. Take `⟨v1, v2⟩` from `v`.

Establish `h1 : (v1, v2) ≠ (b, c)` using `fun e => hc (by simp at e; exact e.2.symm)`. Establish `h2 : (v1, v2) ≠ (a, c)` using `fun e => hc (by simp at e; exact e.2.symm)`. Apply the tactic sequence `split_ifs <;> simp [pderiv_X, Pi.single_apply, h1.symm, h2.symm]`. Simplify using the standard rewrite rules.
-/
theorem leftRootDerivation_X (a b : Ix p q) (v : Ln p q r s) :
    der1 a b (X v : Pol p q r s) = if linePos (a, v.2) = true then (if v.1 = b then X (a, v.2) else 0)
      else (if v.1 = a then -X (b, v.2) else 0) := by
  classical
  rw [der1, der_sum_apply, Finset.sum_eq_single v.2]
  · obtain ⟨v1, v2⟩ := v
    by_cases h : linePos (a, v2) = true
    · simp only [h, if_true, Derivation.smul_apply, pderiv_X, smul_eq_mul]
      by_cases hb : v1 = b
      · subst hb; simp
      · simp [Pi.single_apply, hb]
    · simp only [h, if_false, Derivation.neg_apply, Derivation.smul_apply, pderiv_X, smul_eq_mul]
      by_cases ha : v1 = a
      · subst ha; simp
      · simp [Pi.single_apply, ha]
  · intro c _ hc
    obtain ⟨v1, v2⟩ := v
    have h1 : (v1, v2) ≠ (b, c) := fun e => hc (by simp at e; exact e.2.symm)
    have h2 : (v1, v2) ≠ (a, c) := fun e => hc (by simp at e; exact e.2.symm)
    split_ifs <;> simp [pderiv_X, Pi.single_apply, h1.symm, h2.symm]
  · simp

/- English proof (translation)
Rewrite using `[der2, der_sum_apply, Finset.sum_eq_single v.1]`. Take `⟨v1, v2⟩` from `v`. Distinguish the cases in `h : linePos (v1, c) = true`. Simplify using `only [h, if_true, Derivation.smul_apply, pderiv_X, smul_eq_mul]`. Distinguish the cases in `hb : v2 = d`.

Substitute `hb` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hb]`. Simplify using `only [h, if_false, Derivation.neg_apply, Derivation.smul_apply, pderiv_X, smul_eq_mul]`. Distinguish the cases in `ha : v2 = c`.

Substitute `ha` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, ha]`. Introduce `a _ hc`. Take `⟨v1, v2⟩` from `v`.

Establish `h1 : (v1, v2) ≠ (a, d)` using `fun e => hc (by simp at e; exact e.1.symm)`. Establish `h2 : (v1, v2) ≠ (a, c)` using `fun e => hc (by simp at e; exact e.1.symm)`. Apply the tactic sequence `split_ifs <;> simp [pderiv_X, Pi.single_apply, h1.symm, h2.symm]`. Simplify using the standard rewrite rules.
-/
theorem rightRootDerivation_X (c d : Ix r s) (v : Ln p q r s) :
    der2 c d (X v : Pol p q r s) = if linePos (v.1, c) = true then (if v.2 = d then X (v.1, c) else 0)
      else (if v.2 = c then -X (v.1, d) else 0) := by
  classical
  rw [der2, der_sum_apply, Finset.sum_eq_single v.1]
  · obtain ⟨v1, v2⟩ := v
    by_cases h : linePos (v1, c) = true
    · simp only [h, if_true, Derivation.smul_apply, pderiv_X, smul_eq_mul]
      by_cases hb : v2 = d
      · subst hb; simp
      · simp [Pi.single_apply, hb]
    · simp only [h, if_false, Derivation.neg_apply, Derivation.smul_apply, pderiv_X, smul_eq_mul]
      by_cases ha : v2 = c
      · subst ha; simp
      · simp [Pi.single_apply, ha]
  · intro a _ hc
    obtain ⟨v1, v2⟩ := v
    have h1 : (v1, v2) ≠ (a, d) := fun e => hc (by simp at e; exact e.1.symm)
    have h2 : (v1, v2) ≠ (a, c) := fun e => hc (by simp at e; exact e.1.symm)
    split_ifs <;> simp [pderiv_X, Pi.single_apply, h1.symm, h2.symm]
  · simp

/- English proof (translation)
Rewrite using `[rai1, der1, der_sum_apply, LinearMap.sum_apply]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `c _`. Rewrite using `[Module.End.mul_apply, raiB, lowB, ← hblk c]`. Distinguish the cases in `h : linePos (a, c) = true`.

Simplify using `[h, smul_eq_mul]`. Establish `hne : (a, c) ≠ (b, c)` using `fun e => hab (by simp at e; exact e)`. Simplify using `only [h, if_false, Bool.false_eq_true, LinearMap.neg_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, Derivation.neg_apply, Derivation.smul_apply, smul_eq_mul]`. Rewrite using `[pderiv_mul, pderiv_X_of_ne hne.symm]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem leftRootOperator_eq_derivation (a b : Ix p q) (hab : a ≠ b) (hblk : ∀ c : Ix r s, linePos (a, c) = linePos (b, c))
    (f : Pol p q r s) : rai1 (r := r) (s := s) a b f = der1 a b f := by
  classical
  rw [rai1, der1, der_sum_apply, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro c _
  rw [Module.End.mul_apply, raiB, lowB, ← hblk c]
  by_cases h : linePos (a, c) = true
  · simp [h, smul_eq_mul]
  · have hne : (a, c) ≠ (b, c) := fun e => hab (by simp at e; exact e)
    simp only [h, if_false, Bool.false_eq_true, LinearMap.neg_apply, LinearMap.mulLeft_apply,
      Derivation.coeFn_coe, Derivation.neg_apply, Derivation.smul_apply, smul_eq_mul]
    rw [pderiv_mul, pderiv_X_of_ne hne.symm]
    ring

/- English proof (translation)
Rewrite using `[rai2, der2, der_sum_apply, LinearMap.sum_apply]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `a _`. Rewrite using `[Module.End.mul_apply, raiB, lowB, ← hblk a]`. Distinguish the cases in `h : linePos (a, c) = true`.

Simplify using `[h, smul_eq_mul]`. Establish `hne : (a, c) ≠ (a, d)` using `fun e => hcd (by simp at e; exact e)`. Simplify using `only [h, if_false, Bool.false_eq_true, LinearMap.neg_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, Derivation.neg_apply, Derivation.smul_apply, smul_eq_mul]`. Rewrite using `[pderiv_mul, pderiv_X_of_ne hne.symm]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rightRootOperator_eq_derivation (c d : Ix r s) (hcd : c ≠ d) (hblk : ∀ a : Ix p q, linePos (a, c) = linePos (a, d))
    (f : Pol p q r s) : rai2 (p := p) (q := q) c d f = der2 c d f := by
  classical
  rw [rai2, der2, der_sum_apply, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [Module.End.mul_apply, raiB, lowB, ← hblk a]
  by_cases h : linePos (a, c) = true
  · simp [h, smul_eq_mul]
  · have hne : (a, c) ≠ (a, d) := fun e => hcd (by simp at e; exact e)
    simp only [h, if_false, Bool.false_eq_true, LinearMap.neg_apply, LinearMap.mulLeft_apply,
      Derivation.coeFn_coe, Derivation.neg_apply, Derivation.smul_apply, smul_eq_mul]
    rw [pderiv_mul, pderiv_X_of_ne hne.symm]
    ring

section Kill

variable {m k : ℕ}

/- English proof (translation)
Unfold `leadT`. Use `split_ifs with hh`. Apply `deriv_det_eq_zero_rows` to reduce the goal to its premises. Introduce `i`. Break down `h (Fin.castLE hh.1 i) (by simp) with h0 | ⟨i₁, hi₁, hne, e, he⟩` into its components or cases.

Use `left`. Introduce `j`. Simplify using `only [Matrix.submatrix_apply, varMat, Matrix.of_apply]`. Conclude with `h0 _ (by simp)`. Use `right`.

Use `⟨⟨i₁.val, hi₁⟩, ?_, e, ?_⟩` and prove the remaining obligations. Introduce `hc`. Apply `hne` to reduce the goal to its premises. Use `ext`. Simplify using `[← hc]`.

Introduce `j`. Simplify using `only [Matrix.submatrix_apply, varMat, Matrix.of_apply]`. Rewrite using `[he _ (by simp)]`. Both sides reduce to the same expression. Simplify using the standard rewrite rules.
-/
theorem leadT_der_rows (D : Derivation ℂ (Pol p q r s) (Pol p q r s)) (ρ : Fin m → Ix p q)
    (κ : Fin k → Ix r s) (t : ℕ)
    (h : ∀ i₀ : Fin m, i₀.val < t → (∀ j : Fin k, j.val < t → D (X (ρ i₀, κ j)) = 0) ∨
      ∃ i₁ : Fin m, i₁.val < t ∧ i₁ ≠ i₀ ∧ ∃ e : Pol p q r s,
        ∀ j : Fin k, j.val < t → D (X (ρ i₀, κ j)) = e * X (ρ i₁, κ j)) :
    D (leadT (varMat ρ κ) t) = 0 := by
  unfold leadT
  split_ifs with hh
  · apply deriv_det_eq_zero_rows
    intro i
    rcases h (Fin.castLE hh.1 i) (by simp) with h0 | ⟨i₁, hi₁, hne, e, he⟩
    · left
      intro j
      simp only [Matrix.submatrix_apply, varMat, Matrix.of_apply]
      exact h0 _ (by simp)
    · right
      refine ⟨⟨i₁.val, hi₁⟩, ?_, e, ?_⟩
      · intro hc
        apply hne
        ext
        simp [← hc]
      · intro j
        simp only [Matrix.submatrix_apply, varMat, Matrix.of_apply]
        rw [he _ (by simp)]
        rfl
  · simp

/- English proof (translation)
Unfold `leadT`. Use `split_ifs with hh`. Apply `deriv_det_eq_zero` to reduce the goal to its premises. Introduce `j`. Break down `h (Fin.castLE hh.2 j) (by simp) with h0 | ⟨j₁, hj₁, hne, e, he⟩` into its components or cases.

Use `left`. Introduce `i`. Simplify using `only [Matrix.submatrix_apply, varMat, Matrix.of_apply]`. Conclude with `h0 _ (by simp)`. Use `right`.

Use `⟨⟨j₁.val, hj₁⟩, ?_, e, ?_⟩` and prove the remaining obligations. Introduce `hc`. Apply `hne` to reduce the goal to its premises. Use `ext`. Simplify using `[← hc]`.

Introduce `i`. Simplify using `only [Matrix.submatrix_apply, varMat, Matrix.of_apply]`. Rewrite using `[he _ (by simp)]`. Both sides reduce to the same expression. Simplify using the standard rewrite rules.
-/
theorem leadT_der_cols (D : Derivation ℂ (Pol p q r s) (Pol p q r s)) (ρ : Fin m → Ix p q)
    (κ : Fin k → Ix r s) (t : ℕ)
    (h : ∀ j₀ : Fin k, j₀.val < t → (∀ i : Fin m, i.val < t → D (X (ρ i, κ j₀)) = 0) ∨
      ∃ j₁ : Fin k, j₁.val < t ∧ j₁ ≠ j₀ ∧ ∃ e : Pol p q r s,
        ∀ i : Fin m, i.val < t → D (X (ρ i, κ j₀)) = e * X (ρ i, κ j₁)) :
    D (leadT (varMat ρ κ) t) = 0 := by
  unfold leadT
  split_ifs with hh
  · apply deriv_det_eq_zero
    intro j
    rcases h (Fin.castLE hh.2 j) (by simp) with h0 | ⟨j₁, hj₁, hne, e, he⟩
    · left
      intro i
      simp only [Matrix.submatrix_apply, varMat, Matrix.of_apply]
      exact h0 _ (by simp)
    · right
      refine ⟨⟨j₁.val, hj₁⟩, ?_, e, ?_⟩
      · intro hc
        apply hne
        ext
        simp [← hc]
      · intro i
        simp only [Matrix.submatrix_apply, varMat, Matrix.of_apply]
        rw [he _ (by simp)]
        rfl
  · simp

/- English proof (translation)
Unfold `shapeProd`. Apply `deriv_prod_eq_zero` to reduce the goal to its premises. Introduce `t _`. Conclude with `deriv_pow_eq_zero _ _ _ (h _)`.
-/
theorem shapeProd_der (D : Derivation ℂ (Pol p q r s) (Pol p q r s))
    (M : Matrix (Fin m) (Fin k) (Pol p q r s)) (α : List ℕ) (h : ∀ t, D (leadT M t) = 0) :
    D (shapeProd M α) = 0 := by
  unfold shapeProd
  apply deriv_prod_eq_zero
  intro t _
  exact deriv_pow_eq_zero _ _ _ (h _)

/- English proof (translation)
Apply `leadT_der_rows` to reduce the goal to its premises. Introduce `i₀ hi₀`. Distinguish the cases in `hy : ρ i₀ = y`. Use `right`. Take `⟨i₁, hi₁, hx⟩` from `hcl i₀ hi₀ hy`.

Use `⟨i₁, hi₁, fun e => hxy (by rw [← hx, ← hy, e]), 1, fun j _ => ?_⟩` and prove the remaining obligations. Rewrite using `[leftRootDerivation_X]`. Simplify using `[hpos j, hy, hx]`. Use `left`. Introduce `j _`.

Rewrite using `[leftRootDerivation_X]`. Simplify using `[hpos j, hy]`.
-/
theorem leadingMinor_leftRootDerivation_pos (x y : Ix p q) (hxy : x ≠ y) (ρ : Fin m → Ix p q) (κ : Fin k → Ix r s)
    (t : ℕ) (hpos : ∀ j, linePos (x, κ j) = true)
    (hcl : ∀ i₀ : Fin m, i₀.val < t → ρ i₀ = y → ∃ i₁ : Fin m, i₁.val < t ∧ ρ i₁ = x) :
    der1 x y (leadT (varMat ρ κ) t) = 0 := by
  apply leadT_der_rows
  intro i₀ hi₀
  by_cases hy : ρ i₀ = y
  · right
    obtain ⟨i₁, hi₁, hx⟩ := hcl i₀ hi₀ hy
    refine ⟨i₁, hi₁, fun e => hxy (by rw [← hx, ← hy, e]), 1, fun j _ => ?_⟩
    rw [leftRootDerivation_X]
    simp [hpos j, hy, hx]
  · left
    intro j _
    rw [leftRootDerivation_X]
    simp [hpos j, hy]

/- English proof (translation)
Apply `leadT_der_rows` to reduce the goal to its premises. Introduce `i₀ hi₀`. Distinguish the cases in `hx : ρ i₀ = x`. Use `right`. Take `⟨i₁, hi₁, hy⟩` from `hcl i₀ hi₀ hx`.

Use `⟨i₁, hi₁, fun e => hxy (by rw [← hx, ← hy, e]), -1, fun j _ => ?_⟩` and prove the remaining obligations. Rewrite using `[leftRootDerivation_X]`. Simplify using `[hneg j, hy, hx]`. Use `left`. Introduce `j _`.

Rewrite using `[leftRootDerivation_X]`. Simplify using `[hneg j, hx]`.
-/
theorem leadingMinor_leftRootDerivation_neg (x y : Ix p q) (hxy : x ≠ y) (ρ : Fin m → Ix p q) (κ : Fin k → Ix r s)
    (t : ℕ) (hneg : ∀ j, linePos (x, κ j) = false)
    (hcl : ∀ i₀ : Fin m, i₀.val < t → ρ i₀ = x → ∃ i₁ : Fin m, i₁.val < t ∧ ρ i₁ = y) :
    der1 x y (leadT (varMat ρ κ) t) = 0 := by
  apply leadT_der_rows
  intro i₀ hi₀
  by_cases hx : ρ i₀ = x
  · right
    obtain ⟨i₁, hi₁, hy⟩ := hcl i₀ hi₀ hx
    refine ⟨i₁, hi₁, fun e => hxy (by rw [← hx, ← hy, e]), -1, fun j _ => ?_⟩
    rw [leftRootDerivation_X]
    simp [hneg j, hy, hx]
  · left
    intro j _
    rw [leftRootDerivation_X]
    simp [hneg j, hx]

/- English proof (translation)
Apply `leadT_der_cols` to reduce the goal to its premises. Introduce `j₀ hj₀`. Distinguish the cases in `hy : κ j₀ = y`. Use `right`. Take `⟨j₁, hj₁, hx⟩` from `hcl j₀ hj₀ hy`.

Use `⟨j₁, hj₁, fun e => hxy (by rw [← hx, ← hy, e]), 1, fun i _ => ?_⟩` and prove the remaining obligations. Rewrite using `[rightRootDerivation_X]`. Simplify using `[hpos i, hy, hx]`. Use `left`. Introduce `i _`.

Rewrite using `[rightRootDerivation_X]`. Simplify using `[hpos i, hy]`.
-/
theorem leadingMinor_rightRootDerivation_pos (x y : Ix r s) (hxy : x ≠ y) (ρ : Fin m → Ix p q) (κ : Fin k → Ix r s)
    (t : ℕ) (hpos : ∀ i, linePos (ρ i, x) = true)
    (hcl : ∀ j₀ : Fin k, j₀.val < t → κ j₀ = y → ∃ j₁ : Fin k, j₁.val < t ∧ κ j₁ = x) :
    der2 x y (leadT (varMat ρ κ) t) = 0 := by
  apply leadT_der_cols
  intro j₀ hj₀
  by_cases hy : κ j₀ = y
  · right
    obtain ⟨j₁, hj₁, hx⟩ := hcl j₀ hj₀ hy
    refine ⟨j₁, hj₁, fun e => hxy (by rw [← hx, ← hy, e]), 1, fun i _ => ?_⟩
    rw [rightRootDerivation_X]
    simp [hpos i, hy, hx]
  · left
    intro i _
    rw [rightRootDerivation_X]
    simp [hpos i, hy]

/- English proof (translation)
Apply `leadT_der_cols` to reduce the goal to its premises. Introduce `j₀ hj₀`. Distinguish the cases in `hx : κ j₀ = x`. Use `right`. Take `⟨j₁, hj₁, hy⟩` from `hcl j₀ hj₀ hx`.

Use `⟨j₁, hj₁, fun e => hxy (by rw [← hx, ← hy, e]), -1, fun i _ => ?_⟩` and prove the remaining obligations. Rewrite using `[rightRootDerivation_X]`. Simplify using `[hneg i, hy, hx]`. Use `left`. Introduce `i _`.

Rewrite using `[rightRootDerivation_X]`. Simplify using `[hneg i, hx]`.
-/
theorem leadingMinor_rightRootDerivation_neg (x y : Ix r s) (hxy : x ≠ y) (ρ : Fin m → Ix p q) (κ : Fin k → Ix r s)
    (t : ℕ) (hneg : ∀ i, linePos (ρ i, x) = false)
    (hcl : ∀ j₀ : Fin k, j₀.val < t → κ j₀ = x → ∃ j₁ : Fin k, j₁.val < t ∧ κ j₁ = y) :
    der2 x y (leadT (varMat ρ κ) t) = 0 := by
  apply leadT_der_cols
  intro j₀ hj₀
  by_cases hx : κ j₀ = x
  · right
    obtain ⟨j₁, hj₁, hy⟩ := hcl j₀ hj₀ hx
    refine ⟨j₁, hj₁, fun e => hxy (by rw [← hx, ← hy, e]), -1, fun i _ => ?_⟩
    rw [rightRootDerivation_X]
    simp [hneg i, hy, hx]
  · left
    intro i _
    rw [rightRootDerivation_X]
    simp [hneg i, hx]

end Kill

/- English proof (translation)
Rewrite using `[hwVec]`. Simplify using `only [Derivation.leibniz, shapeProd_der D _ _ h1, shapeProd_der D _ _ h2, shapeProd_der D _ _ h3, shapeProd_der D _ _ h4, smul_zero, add_zero]`.
-/
theorem hwVec_der (D : Derivation ℂ (Pol p q r s) (Pol p q r s)) (a b c d : List ℤ)
    (h1 : ∀ t, D (leadT (varMat (fun i : Fin p => (Sum.inl i : Ix p q))
      (fun k : Fin r => (Sum.inl k : Ix r s))) t) = 0)
    (h2 : ∀ t, D (leadT (varMat (fun i : Fin p => (Sum.inl (Fin.rev i) : Ix p q))
      (fun l : Fin s => (Sum.inr (Fin.rev l) : Ix r s))) t) = 0)
    (h3 : ∀ t, D (leadT (varMat (fun j : Fin q => (Sum.inr j : Ix p q))
      (fun l : Fin s => (Sum.inr l : Ix r s))) t) = 0)
    (h4 : ∀ t, D (leadT (varMat (fun j : Fin q => (Sum.inr (Fin.rev j) : Ix p q))
      (fun k : Fin r => (Sum.inl (Fin.rev k) : Ix r s))) t) = 0) :
    D (hwVec p q r s a b c d) = 0 := by
  rw [hwVec]
  simp only [Derivation.leibniz, shapeProd_der D _ _ h1, shapeProd_der D _ _ h2,
    shapeProd_der D _ _ h3, shapeProd_der D _ _ h4, smul_zero, add_zero]

/- English proof (translation)
Consider the cases of `x with`. Consider the case `inl i`. Consider the cases of `y with`. Consider the case `inr _ => exact hxy.elim`. Consider the case `inl i'`.

Establish `hii : i < i'` using `hxy`. Establish `hne : (Sum.inl i : Ix p q) ≠ Sum.inl i'` using `fun e => by simp at e; omega`. Apply `hwVec_der` to reduce the goal to its premises. Introduce `t`. Use `leadingMinor_leftRootDerivation_pos _ _ hne _ _ t (fun _ => rfl) ?_` and prove the remaining obligations.

Introduce `i₀ hi₀ e`. Simplify using `only [Sum.inl.injEq] at e`. Substitute `e` using the available equality. Conclude with `⟨i, by omega, rfl⟩`. Introduce `t`.

Use `leadingMinor_leftRootDerivation_neg _ _ hne _ _ t (fun _ => rfl) ?_` and prove the remaining obligations. Introduce `i₀ hi₀ e`. Simplify using `only [Sum.inl.injEq] at e`. Use `⟨Fin.rev i', ?_, by simp⟩` and prove the remaining obligations. Use `congrArg Fin.val e` as an intermediate fact.

Simplify using `only [Fin.val_rev] at this ⊢`. Use linear arithmetic over natural numbers and integers. Introduce `t`. Use `leadingMinor_leftRootDerivation_neg _ _ hne _ _ t (fun _ => rfl) ?_` and prove the remaining obligations. Introduce `i₀ _ e`.

Conclude with `absurd e (by simp)`. Introduce `t`. Use `leadingMinor_leftRootDerivation_pos _ _ hne _ _ t (fun _ => rfl) ?_` and prove the remaining obligations. Introduce `i₀ _ e`. Conclude with `absurd e (by simp)`.

Consider the case `inr j`. Consider the cases of `y with`. Consider the case `inl _ => exact hxy.elim`. Consider the case `inr j'`. Establish `hjj : j < j'` using `hxy`.

Establish `hne : (Sum.inr j : Ix p q) ≠ Sum.inr j'` using `fun e => by simp at e; omega`. Apply `hwVec_der` to reduce the goal to its premises. Introduce `t`. Use `leadingMinor_leftRootDerivation_neg _ _ hne _ _ t (fun _ => rfl) ?_` and prove the remaining obligations. Introduce `i₀ _ e`.

Conclude with `absurd e (by simp)`. Introduce `t`. Use `leadingMinor_leftRootDerivation_pos _ _ hne _ _ t (fun _ => rfl) ?_` and prove the remaining obligations. Introduce `i₀ _ e`. Conclude with `absurd e (by simp)`.

Introduce `t`. Use `leadingMinor_leftRootDerivation_pos _ _ hne _ _ t (fun _ => rfl) ?_` and prove the remaining obligations. Introduce `i₀ hi₀ e`. Simplify using `only [Sum.inr.injEq] at e`. Substitute `e` using the available equality.

Conclude with `⟨j, by omega, rfl⟩`. Introduce `t`. Use `leadingMinor_leftRootDerivation_neg _ _ hne _ _ t (fun _ => rfl) ?_` and prove the remaining obligations. Introduce `i₀ hi₀ e`. Simplify using `only [Sum.inr.injEq] at e`.

Use `⟨Fin.rev j', ?_, by simp⟩` and prove the remaining obligations. Use `congrArg Fin.val e` as an intermediate fact. Simplify using `only [Fin.val_rev] at this ⊢`. Use linear arithmetic over natural numbers and integers.
-/
theorem vecRaise1 (a b c d : List ℤ) (x y : Ix p q) (hxy : posC x y) :
    der1 (r := r) (s := s) x y (hwVec p q r s a b c d) = 0 := by
  cases x with
  | inl i =>
    cases y with
    | inr _ => exact hxy.elim
    | inl i' =>
      have hii : i < i' := hxy
      have hne : (Sum.inl i : Ix p q) ≠ Sum.inl i' := fun e => by simp at e; omega
      apply hwVec_der
      · intro t
        refine leadingMinor_leftRootDerivation_pos _ _ hne _ _ t (fun _ => rfl) ?_
        intro i₀ hi₀ e
        simp only [Sum.inl.injEq] at e
        subst e
        exact ⟨i, by omega, rfl⟩
      · intro t
        refine leadingMinor_leftRootDerivation_neg _ _ hne _ _ t (fun _ => rfl) ?_
        intro i₀ hi₀ e
        simp only [Sum.inl.injEq] at e
        refine ⟨Fin.rev i', ?_, by simp⟩
        have := congrArg Fin.val e
        simp only [Fin.val_rev] at this ⊢
        omega
      · intro t
        refine leadingMinor_leftRootDerivation_neg _ _ hne _ _ t (fun _ => rfl) ?_
        intro i₀ _ e
        exact absurd e (by simp)
      · intro t
        refine leadingMinor_leftRootDerivation_pos _ _ hne _ _ t (fun _ => rfl) ?_
        intro i₀ _ e
        exact absurd e (by simp)
  | inr j =>
    cases y with
    | inl _ => exact hxy.elim
    | inr j' =>
      have hjj : j < j' := hxy
      have hne : (Sum.inr j : Ix p q) ≠ Sum.inr j' := fun e => by simp at e; omega
      apply hwVec_der
      · intro t
        refine leadingMinor_leftRootDerivation_neg _ _ hne _ _ t (fun _ => rfl) ?_
        intro i₀ _ e
        exact absurd e (by simp)
      · intro t
        refine leadingMinor_leftRootDerivation_pos _ _ hne _ _ t (fun _ => rfl) ?_
        intro i₀ _ e
        exact absurd e (by simp)
      · intro t
        refine leadingMinor_leftRootDerivation_pos _ _ hne _ _ t (fun _ => rfl) ?_
        intro i₀ hi₀ e
        simp only [Sum.inr.injEq] at e
        subst e
        exact ⟨j, by omega, rfl⟩
      · intro t
        refine leadingMinor_leftRootDerivation_neg _ _ hne _ _ t (fun _ => rfl) ?_
        intro i₀ hi₀ e
        simp only [Sum.inr.injEq] at e
        refine ⟨Fin.rev j', ?_, by simp⟩
        have := congrArg Fin.val e
        simp only [Fin.val_rev] at this ⊢
        omega

/- English proof (translation)
Consider the cases of `x with`. Consider the case `inl k`. Consider the cases of `y with`. Consider the case `inr _ => exact hxy.elim`. Consider the case `inl k'`.

Establish `hkk : k < k'` using `hxy`. Establish `hne : (Sum.inl k : Ix r s) ≠ Sum.inl k'` using `fun e => by simp at e; omega`. Apply `hwVec_der` to reduce the goal to its premises. Introduce `t`. Use `leadingMinor_rightRootDerivation_pos _ _ hne _ _ t (fun _ => rfl) ?_` and prove the remaining obligations.

Introduce `j₀ hj₀ e`. Simplify using `only [Sum.inl.injEq] at e`. Substitute `e` using the available equality. Conclude with `⟨k, by omega, rfl⟩`. Introduce `t`.

Use `leadingMinor_rightRootDerivation_pos _ _ hne _ _ t (fun _ => rfl) ?_` and prove the remaining obligations. Introduce `j₀ _ e`. Conclude with `absurd e (by simp)`. Introduce `t`. Use `leadingMinor_rightRootDerivation_neg _ _ hne _ _ t (fun _ => rfl) ?_` and prove the remaining obligations.

Introduce `j₀ _ e`. Conclude with `absurd e (by simp)`. Introduce `t`. Use `leadingMinor_rightRootDerivation_neg _ _ hne _ _ t (fun _ => rfl) ?_` and prove the remaining obligations. Introduce `j₀ hj₀ e`.

Simplify using `only [Sum.inl.injEq] at e`. Use `⟨Fin.rev k', ?_, by simp⟩` and prove the remaining obligations. Use `congrArg Fin.val e` as an intermediate fact. Simplify using `only [Fin.val_rev] at this ⊢`. Use linear arithmetic over natural numbers and integers.

Consider the case `inr l`. Consider the cases of `y with`. Consider the case `inl _ => exact hxy.elim`. Consider the case `inr l'`. Establish `hll : l < l'` using `hxy`.

Establish `hne : (Sum.inr l : Ix r s) ≠ Sum.inr l'` using `fun e => by simp at e; omega`. Apply `hwVec_der` to reduce the goal to its premises. Introduce `t`. Use `leadingMinor_rightRootDerivation_neg _ _ hne _ _ t (fun _ => rfl) ?_` and prove the remaining obligations. Introduce `j₀ _ e`.

Conclude with `absurd e (by simp)`. Introduce `t`. Use `leadingMinor_rightRootDerivation_neg _ _ hne _ _ t (fun _ => rfl) ?_` and prove the remaining obligations. Introduce `j₀ hj₀ e`. Simplify using `only [Sum.inr.injEq] at e`.

Use `⟨Fin.rev l', ?_, by simp⟩` and prove the remaining obligations. Use `congrArg Fin.val e` as an intermediate fact. Simplify using `only [Fin.val_rev] at this ⊢`. Use linear arithmetic over natural numbers and integers. Introduce `t`.

Use `leadingMinor_rightRootDerivation_pos _ _ hne _ _ t (fun _ => rfl) ?_` and prove the remaining obligations. Introduce `j₀ hj₀ e`. Simplify using `only [Sum.inr.injEq] at e`. Substitute `e` using the available equality. Conclude with `⟨l, by omega, rfl⟩`.

Introduce `t`. Use `leadingMinor_rightRootDerivation_pos _ _ hne _ _ t (fun _ => rfl) ?_` and prove the remaining obligations. Introduce `j₀ _ e`. Conclude with `absurd e (by simp)`.
-/
theorem vecRaise2 (a b c d : List ℤ) (x y : Ix r s) (hxy : posC x y) :
    der2 (p := p) (q := q) x y (hwVec p q r s a b c d) = 0 := by
  cases x with
  | inl k =>
    cases y with
    | inr _ => exact hxy.elim
    | inl k' =>
      have hkk : k < k' := hxy
      have hne : (Sum.inl k : Ix r s) ≠ Sum.inl k' := fun e => by simp at e; omega
      apply hwVec_der
      · intro t
        refine leadingMinor_rightRootDerivation_pos _ _ hne _ _ t (fun _ => rfl) ?_
        intro j₀ hj₀ e
        simp only [Sum.inl.injEq] at e
        subst e
        exact ⟨k, by omega, rfl⟩
      · intro t
        refine leadingMinor_rightRootDerivation_pos _ _ hne _ _ t (fun _ => rfl) ?_
        intro j₀ _ e
        exact absurd e (by simp)
      · intro t
        refine leadingMinor_rightRootDerivation_neg _ _ hne _ _ t (fun _ => rfl) ?_
        intro j₀ _ e
        exact absurd e (by simp)
      · intro t
        refine leadingMinor_rightRootDerivation_neg _ _ hne _ _ t (fun _ => rfl) ?_
        intro j₀ hj₀ e
        simp only [Sum.inl.injEq] at e
        refine ⟨Fin.rev k', ?_, by simp⟩
        have := congrArg Fin.val e
        simp only [Fin.val_rev] at this ⊢
        omega
  | inr l =>
    cases y with
    | inl _ => exact hxy.elim
    | inr l' =>
      have hll : l < l' := hxy
      have hne : (Sum.inr l : Ix r s) ≠ Sum.inr l' := fun e => by simp at e; omega
      apply hwVec_der
      · intro t
        refine leadingMinor_rightRootDerivation_neg _ _ hne _ _ t (fun _ => rfl) ?_
        intro j₀ _ e
        exact absurd e (by simp)
      · intro t
        refine leadingMinor_rightRootDerivation_neg _ _ hne _ _ t (fun _ => rfl) ?_
        intro j₀ hj₀ e
        simp only [Sum.inr.injEq] at e
        refine ⟨Fin.rev l', ?_, by simp⟩
        have := congrArg Fin.val e
        simp only [Fin.val_rev] at this ⊢
        omega
      · intro t
        refine leadingMinor_rightRootDerivation_pos _ _ hne _ _ t (fun _ => rfl) ?_
        intro j₀ hj₀ e
        simp only [Sum.inr.injEq] at e
        subst e
        exact ⟨l, by omega, rfl⟩
      · intro t
        refine leadingMinor_rightRootDerivation_pos _ _ hne _ _ t (fun _ => rfl) ?_
        intro j₀ _ e
        exact absurd e (by simp)

end PI.FJMX
