import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicHomogeneousOfKType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinFirst
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.BasicNotions.TH GlobalTheory.FockAlg MvPolynomial

noncomputable section

namespace GlobalTheory.RealLift.SteepHarm

/- English proof (translation)
Use `set M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ) := (rename x : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial σ ℂ).toRingHom.mapMatrix (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ) with hM`. Establish `hdet : M.det ≠ 0`. Rewrite using `[hM, ← RingHom.map_det]`. Introduce `h0`. Apply `Matrix.det_mvPolynomialX_ne_zero (Fin n) ℂ` to reduce the goal to its premises.

Apply `rename_injective x hx` to reduce the goal to its premises. Simplify using `using h0`. Establish `hv : Matrix.vecMul (fun i => pderiv (y i) f) M = 0`. Use function extensionality and compare the values at `k`. Rewrite using `[Pi.zero_apply, ← hK k]`.

Simplify using `[Matrix.vecMul, dotProduct, hM, Matrix.mvPolynomialX, mul_comm]`. Establish `h0` using `Matrix.eq_zero_of_vecMul_eq_zero hdet hv`. Rewrite using `[← hE]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[show pderiv (y i) f = 0 from congrFun h0 i, mul_zero]`.
-/
theorem eq_zero_of_euler_of_raise {σ : Type} [DecidableEq σ] (n : ℕ) (x : Fin n × Fin n → σ) (y : Fin n → σ) (hx : Function.Injective x)
    (f : MvPolynomial σ ℂ) (hE : ∑ i, X (y i) * pderiv (y i) f = f)
    (hK : ∀ k : Fin n, ∑ i, X (x (i, k)) * pderiv (y i) f = 0) : f = 0 := by
  set M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ) :=
    (rename x : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial σ ℂ).toRingHom.mapMatrix
      (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ) with hM
  have hdet : M.det ≠ 0 := by
    rw [hM, ← RingHom.map_det]
    intro h0
    apply Matrix.det_mvPolynomialX_ne_zero (Fin n) ℂ
    apply rename_injective x hx
    simpa using h0
  have hv : Matrix.vecMul (fun i => pderiv (y i) f) M = 0 := by
    funext k
    rw [Pi.zero_apply, ← hK k]
    simp [Matrix.vecMul, dotProduct, hM, Matrix.mvPolynomialX, mul_comm]
  have h0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hv
  rw [← hE]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [show pderiv (y i) f = 0 from congrFun h0 i, mul_zero]

/- English proof (translation)
Rewrite using `[fockAct2_Eab, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `only [omE, Prod.mk.injEq, true_and]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem fockAct2_Eab_apply {P Q R S : ℕ} (c d : Ix R S) (g : Pol P Q R S) :
    fockAct2 P Q R S (Eab c d) g = ∑ a : Ix P Q, (raiB (a, c) (lowB (a, d) g) +
      if c = d then (1 / 2 : ℂ) • g else 0) := by
  rw [fockAct2_Eab, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [omE, Prod.mk.injEq, true_and]
  split_ifs <;> simp

/- English proof (translation)
Establish `hPR : P ≤ R` using `hi.trans (Nat.le_of_lt i.2)`. Take `⟨hne, hmem⟩` from `hf`. Rewrite `hmem` using `[GlobalTheory.FockAlg.MinFirst.mem_hwSub]`. Take `⟨hwt, hpos⟩` from `hmem`. Apply `hne` to reduce the goal to its premises.

Use `eq_zero_of_euler_of_raise P (fun p => ((.inl p.1, .inl (Fin.castLE hPR p.2)) : Ix P Q × Ix R S)) (fun i' => (.inl i', .inl i)) ?_ f ?_ ?_` and prove the remaining obligations. Introduce `p p' h`. Simplify using `only [Prod.mk.injEq, Sum.inl.injEq] at h`. Conclude with `Prod.ext h.1 (Fin.castLE_injective hPR h.2)`. Establish `h1` using `hwt (.inl i)`.

Rewrite `h1` using `[fockAct2_Eab_apply, Fintype.sum_sum_type]`. Simplify using `only [raiB, lowB, linePos, if_true, if_false, Bool.false_eq_true] at h1`. Establish `e1 : ∀ x : Fin Q, pderiv ((.inr x, .inl i) : Ix P Q × Ix R S) (X (.inr x, .inl i) * f) = f`. Introduce `x`. Rewrite using `[Derivation.leibniz, pderiv_X_self, hw, smul_zero, zero_add, smul_eq_mul, mul_one]`.

Simplify using `only [LinearMap.mulLeft_apply, LinearMap.neg_apply, Derivation.coeFn_coe, e1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, hμ, cPair] at h1`. Move the coercions through the operations in `at h1`. Take the linear combination `(norm := module) h1`. Introduce `k`. Establish `h1` using `hpos (.inl (Fin.castLE hPR k)) (.inl i) (by show Fin.castLE hPR k < i`.

Rewrite using `[Fin.lt_iff_val_lt_val]`. Simplify using the standard rewrite rules. Use the proof step `omega)`. Rewrite `h1` using `[fockAct2_Eab_apply, Fintype.sum_sum_type]`. Simplify using `only [raiB, lowB, linePos, if_true, if_false, Bool.false_eq_true] at h1`.

Establish `hne' : (Sum.inl (Fin.castLE hPR k) : Ix R S) ≠ Sum.inl i`. Introduce `h`. Simplify using `only [Sum.inl.injEq, Fin.ext_iff, Fin.coe_castLE] at h`. Use linear arithmetic over natural numbers and integers. Establish `e1 : ∀ x : Fin Q, pderiv ((.inr x, .inl (Fin.castLE hPR k)) : Ix P Q × Ix R S) (X (.inr x, .inl i) * f) = 0`.

Introduce `x`. Rewrite using `[Derivation.leibniz, pderiv_X_of_ne (by simp [hne'.symm]), hw, smul_zero, smul_zero, add_zero]`. Simplify using `only [LinearMap.mulLeft_apply, LinearMap.neg_apply, Derivation.coeFn_coe, e1, hne', if_false, add_zero, neg_zero, Finset.sum_const_zero] at h1`. Conclude with `h1`.
-/
theorem not_hw_of_wFree (P Q R S : ℕ) (μ : Ix R S → ℚ) (i : Fin R) (f : Pol P Q R S) (hi : P ≤ (i : ℕ))
    (hμ : μ (.inl i) = cPair P Q + 1)
    (hw : ∀ (j' : Fin Q) (k : Fin R), pderiv ((.inr j', .inl k) : Ix P Q × Ix R S) f = 0)
    (hf : IsHW (fockAct2 P Q R S) μ f) : False := by
  have hPR : P ≤ R := hi.trans (Nat.le_of_lt i.2)
  obtain ⟨hne, hmem⟩ := hf
  rw [GlobalTheory.FockAlg.MinFirst.mem_hwSub] at hmem
  obtain ⟨hwt, hpos⟩ := hmem
  apply hne
  refine eq_zero_of_euler_of_raise P (fun p => ((.inl p.1, .inl (Fin.castLE hPR p.2)) : Ix P Q × Ix R S)) (fun i' => (.inl i', .inl i)) ?_ f ?_ ?_
  · intro p p' h
    simp only [Prod.mk.injEq, Sum.inl.injEq] at h
    exact Prod.ext h.1 (Fin.castLE_injective hPR h.2)
  · have h1 := hwt (.inl i)
    rw [fockAct2_Eab_apply, Fintype.sum_sum_type] at h1
    simp only [raiB, lowB, linePos, if_true, if_false, Bool.false_eq_true] at h1
    have e1 : ∀ x : Fin Q, pderiv ((.inr x, .inl i) : Ix P Q × Ix R S) (X (.inr x, .inl i) * f) = f := by
      intro x; rw [Derivation.leibniz, pderiv_X_self, hw, smul_zero, zero_add, smul_eq_mul, mul_one]
    simp only [LinearMap.mulLeft_apply, LinearMap.neg_apply, Derivation.coeFn_coe, e1, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, hμ, cPair] at h1
    push_cast at h1
    linear_combination (norm := module) h1
  · intro k
    have h1 := hpos (.inl (Fin.castLE hPR k)) (.inl i) (by
      show Fin.castLE hPR k < i
      rw [Fin.lt_iff_val_lt_val]; simp; omega)
    rw [fockAct2_Eab_apply, Fintype.sum_sum_type] at h1
    simp only [raiB, lowB, linePos, if_true, if_false, Bool.false_eq_true] at h1
    have hne' : (Sum.inl (Fin.castLE hPR k) : Ix R S) ≠ Sum.inl i := by
      intro h; simp only [Sum.inl.injEq, Fin.ext_iff, Fin.coe_castLE] at h; omega
    have e1 : ∀ x : Fin Q, pderiv ((.inr x, .inl (Fin.castLE hPR k)) : Ix P Q × Ix R S) (X (.inr x, .inl i) * f) = 0 := by
      intro x
      rw [Derivation.leibniz, pderiv_X_of_ne (by simp [hne'.symm]), hw, smul_zero, smul_zero, add_zero]
    simp only [LinearMap.mulLeft_apply, LinearMap.neg_apply, Derivation.coeFn_coe, e1, hne', if_false, add_zero,
      neg_zero, Finset.sum_const_zero] at h1
    exact h1

/- English proof (translation)
Establish `hQS : Q ≤ S` using `hj.trans (Nat.le_of_lt j.2)`. Take `⟨hne, hmem⟩` from `hf`. Rewrite `hmem` using `[GlobalTheory.FockAlg.MinFirst.mem_hwSub]`. Take `⟨hwt, hpos⟩` from `hmem`. Apply `hne` to reduce the goal to its premises.

Use `eq_zero_of_euler_of_raise Q (fun p => ((.inr p.1, .inr (Fin.castLE hQS p.2)) : Ix P Q × Ix R S)) (fun j' => (.inr j', .inr j)) ?_ f ?_ ?_` and prove the remaining obligations. Introduce `p p' h`. Simplify using `only [Prod.mk.injEq, Sum.inr.injEq] at h`. Conclude with `Prod.ext h.1 (Fin.castLE_injective hQS h.2)`. Establish `h1` using `hwt (.inr j)`.

Rewrite `h1` using `[fockAct2_Eab_apply, Fintype.sum_sum_type]`. Simplify using `only [raiB, lowB, linePos, if_true, if_false, Bool.false_eq_true] at h1`. Establish `e1 : ∀ x : Fin P, pderiv ((.inl x, .inr j) : Ix P Q × Ix R S) (X (.inl x, .inr j) * f) = f`. Introduce `x`. Rewrite using `[Derivation.leibniz, pderiv_X_self, hu, smul_zero, zero_add, smul_eq_mul, mul_one]`.

Simplify using `only [LinearMap.mulLeft_apply, LinearMap.neg_apply, Derivation.coeFn_coe, e1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, hμ, cPair] at h1`. Move the coercions through the operations in `at h1`. Take the linear combination `(norm := module) h1`. Introduce `k`. Establish `h1` using `hpos (.inr (Fin.castLE hQS k)) (.inr j) (by show Fin.castLE hQS k < j`.

Rewrite using `[Fin.lt_iff_val_lt_val]`. Simplify using the standard rewrite rules. Use the proof step `omega)`. Rewrite `h1` using `[fockAct2_Eab_apply, Fintype.sum_sum_type]`. Simplify using `only [raiB, lowB, linePos, if_true, if_false, Bool.false_eq_true] at h1`.

Establish `hne' : (Sum.inr (Fin.castLE hQS k) : Ix R S) ≠ Sum.inr j`. Introduce `h`. Simplify using `only [Sum.inr.injEq, Fin.ext_iff, Fin.coe_castLE] at h`. Use linear arithmetic over natural numbers and integers. Establish `e1 : ∀ x : Fin P, pderiv ((.inl x, .inr (Fin.castLE hQS k)) : Ix P Q × Ix R S) (X (.inl x, .inr j) * f) = 0`.

Introduce `x`. Rewrite using `[Derivation.leibniz, pderiv_X_of_ne (by simp [hne'.symm]), hu, smul_zero, smul_zero, add_zero]`. Simplify using `only [LinearMap.mulLeft_apply, LinearMap.neg_apply, Derivation.coeFn_coe, e1, hne', if_false, add_zero, neg_zero, Finset.sum_const_zero, zero_add] at h1`. Conclude with `h1`.
-/
theorem not_hw_of_uFree (P Q R S : ℕ) (μ : Ix R S → ℚ) (j : Fin S) (f : Pol P Q R S) (hj : Q ≤ (j : ℕ))
    (hμ : μ (.inr j) = 1 - cPair P Q)
    (hu : ∀ (i' : Fin P) (l : Fin S), pderiv ((.inl i', .inr l) : Ix P Q × Ix R S) f = 0)
    (hf : IsHW (fockAct2 P Q R S) μ f) : False := by
  have hQS : Q ≤ S := hj.trans (Nat.le_of_lt j.2)
  obtain ⟨hne, hmem⟩ := hf
  rw [GlobalTheory.FockAlg.MinFirst.mem_hwSub] at hmem
  obtain ⟨hwt, hpos⟩ := hmem
  apply hne
  refine eq_zero_of_euler_of_raise Q (fun p => ((.inr p.1, .inr (Fin.castLE hQS p.2)) : Ix P Q × Ix R S)) (fun j' => (.inr j', .inr j)) ?_ f ?_ ?_
  · intro p p' h
    simp only [Prod.mk.injEq, Sum.inr.injEq] at h
    exact Prod.ext h.1 (Fin.castLE_injective hQS h.2)
  · have h1 := hwt (.inr j)
    rw [fockAct2_Eab_apply, Fintype.sum_sum_type] at h1
    simp only [raiB, lowB, linePos, if_true, if_false, Bool.false_eq_true] at h1
    have e1 : ∀ x : Fin P, pderiv ((.inl x, .inr j) : Ix P Q × Ix R S) (X (.inl x, .inr j) * f) = f := by
      intro x; rw [Derivation.leibniz, pderiv_X_self, hu, smul_zero, zero_add, smul_eq_mul, mul_one]
    simp only [LinearMap.mulLeft_apply, LinearMap.neg_apply, Derivation.coeFn_coe, e1, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, hμ, cPair] at h1
    push_cast at h1
    linear_combination (norm := module) h1
  · intro k
    have h1 := hpos (.inr (Fin.castLE hQS k)) (.inr j) (by
      show Fin.castLE hQS k < j
      rw [Fin.lt_iff_val_lt_val]; simp; omega)
    rw [fockAct2_Eab_apply, Fintype.sum_sum_type] at h1
    simp only [raiB, lowB, linePos, if_true, if_false, Bool.false_eq_true] at h1
    have hne' : (Sum.inr (Fin.castLE hQS k) : Ix R S) ≠ Sum.inr j := by
      intro h; simp only [Sum.inr.injEq, Fin.ext_iff, Fin.coe_castLE] at h; omega
    have e1 : ∀ x : Fin P, pderiv ((.inl x, .inr (Fin.castLE hQS k)) : Ix P Q × Ix R S) (X (.inl x, .inr j) * f) = 0 := by
      intro x
      rw [Derivation.leibniz, pderiv_X_of_ne (by simp [hne'.symm]), hu, smul_zero, smul_zero, add_zero]
    simp only [LinearMap.mulLeft_apply, LinearMap.neg_apply, Derivation.coeFn_coe, e1, hne', if_false, add_zero,
      neg_zero, Finset.sum_const_zero, zero_add] at h1
    exact h1

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on' with`. Consider the case `monomial β c`. Establish `: monomial β c = c • (monomial β (1 : ℂ))` using `by rw [smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[this, map_smul, hL, coeff_smul, coeff_smul, coeff_smul, coeff_monomial]`. Distinguish the cases in `h : β = α`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Simplify using `[h]`. Consider the case `add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]`.
-/
theorem coeff_diag {σ : Type} (L : Module.End ℂ (MvPolynomial σ ℂ)) (g : (σ →₀ ℕ) → ℂ)
    (hL : ∀ α, L (monomial α 1) = g α • monomial α 1) (f : MvPolynomial σ ℂ) (α : σ →₀ ℕ) :
    coeff α (L f) = g α * coeff α f := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial β c =>
    have : monomial β c = c • (monomial β (1 : ℂ)) := by rw [smul_monomial, smul_eq_mul, mul_one]
    rw [this, map_smul, hL, coeff_smul, coeff_smul, coeff_smul, coeff_monomial]
    by_cases h : β = α
    · subst h; simp; ring
    · simp [h]
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]

/- English proof (translation)
Establish `h` using `coeff_diag L g hL f α`. Rewrite `h` using `[hf, coeff_smul, smul_eq_mul]`. Conclude with `(mul_right_cancel₀ hα h).symm`.
-/
theorem coeff_eig {σ : Type} (L : Module.End ℂ (MvPolynomial σ ℂ)) (g : (σ →₀ ℕ) → ℂ)
    (hL : ∀ α, L (monomial α 1) = g α • monomial α 1) (f : MvPolynomial σ ℂ) (c : ℂ) (hf : L f = c • f)
    (α : σ →₀ ℕ) (hα : coeff α f ≠ 0) : g α = c := by
  have h := coeff_diag L g hL f α
  rw [hf, coeff_smul, smul_eq_mul] at h
  exact (mul_right_cancel₀ hα h).symm

/- English proof (translation)
Simplify using `[Eab, Matrix.trace_single_eq_same]`.
-/
theorem trace_Eab_self {p q : ℕ} (a : Ix p q) : (Eab a a).trace = 1 := by
  simp [Eab, Matrix.trace_single_eq_same]

/- English proof (translation)
Take `⟨_, hK, hne, hmem⟩` from `hf`. Rewrite `hmem` using `[GlobalTheory.FockAlg.MinFirst.mem_hwSub]`. Establish `e1 : ∀ a : Ix P Q, (∑ c, lineSign a c * (((α (a, c) : ℕ) : ℂ) + 1 / 2)) = (x : ℂ)`. Introduce `a`. Establish `h` using `hK (Eab a a) (GlobalTheory.FockAlg.MinFirst.isKC_diag a)`.

Rewrite `h` using `[trace_Eab_self, mul_one]`. Conclude with `coeff_eig _ _ (fun β => cartan1 a β) f _ h α hα`. Establish `e2 : ∀ c : Ix R S, (∑ a, lineSign a c * (((α (a, c) : ℕ) : ℂ) + 1 / 2)) = (μ c : ℂ)`. Introduce `c`. Establish `h` using `hmem.1 c`.

Rewrite `h` using `[sub_eq_zero]`. Conclude with `coeff_eig _ _ (fun β => cartan2 c β) f _ h α hα`. Use `⟨fun i' => ?_, fun j' => ?_, fun k => ?_, fun l => ?_⟩` and prove the remaining obligations. Establish `h` using `e1 (.inl i')`. Simplify using `only [Fintype.sum_sum_type, lineSign, one_mul, neg_one_mul, Finset.sum_neg_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h`.

Establish `h' : ((∑ k : Fin R, (α (.inl i', .inl k) : ℚ) - ∑ l : Fin S, (α (.inl i', .inr l) : ℚ) + R / 2 - S / 2 : ℚ) : ℂ) = (x : ℂ)` using `by push_cast; rw [← h]; ring`. Establish `h''` using `Rat.cast_injective h'`. Simplify using `only [cPair]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h` using `e1 (.inr j')`.

Simplify using `only [Fintype.sum_sum_type, lineSign, one_mul, neg_one_mul, Finset.sum_neg_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h`. Establish `h' : ((∑ l : Fin S, (α (.inr j', .inr l) : ℚ) - ∑ k : Fin R, (α (.inr j', .inl k) : ℚ) - R / 2 + S / 2 : ℚ) : ℂ) = (x : ℂ)` using `by push_cast; rw [← h]; ring`. Establish `h''` using `Rat.cast_injective h'`. Simplify using `only [cPair]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h` using `e2 (.inl k)`. Simplify using `only [Fintype.sum_sum_type, lineSign, one_mul, neg_one_mul, Finset.sum_neg_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h`. Establish `h' : ((∑ i' : Fin P, (α (.inl i', .inl k) : ℚ) - ∑ j' : Fin Q, (α (.inr j', .inl k) : ℚ) + P / 2 - Q / 2 : ℚ) : ℂ) = (μ (.inl k) : ℂ)` using `by push_cast; rw [← h]; ring`. Establish `h''` using `Rat.cast_injective h'`. Simplify using `only [cPair]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h` using `e2 (.inr l)`. Simplify using `only [Fintype.sum_sum_type, lineSign, one_mul, neg_one_mul, Finset.sum_neg_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h`. Establish `h' : ((∑ j' : Fin Q, (α (.inr j', .inr l) : ℚ) - ∑ i' : Fin P, (α (.inl i', .inr l) : ℚ) - P / 2 + Q / 2 : ℚ) : ℂ) = (μ (.inr l) : ℂ)` using `by push_cast; rw [← h]; ring`. Establish `h''` using `Rat.cast_injective h'`.

Simplify using `only [cPair]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem monomial_facts (P Q R S : ℕ) (x : ℚ) (μ : Ix R S → ℚ) (f : Pol P Q R S)
    (hf : GlobalTheory.RealLift.IsHarmVec x μ f) (α : (Ix P Q × Ix R S) →₀ ℕ) (hα : coeff α f ≠ 0) :
    (∀ i' : Fin P, ∑ k : Fin R, (α (.inl i', .inl k) : ℚ) - ∑ l : Fin S, (α (.inl i', .inr l) : ℚ) = x - cPair R S) ∧
    (∀ j' : Fin Q, ∑ l : Fin S, (α (.inr j', .inr l) : ℚ) - ∑ k : Fin R, (α (.inr j', .inl k) : ℚ) = x + cPair R S) ∧
    (∀ k : Fin R, ∑ i' : Fin P, (α (.inl i', .inl k) : ℚ) - ∑ j' : Fin Q, (α (.inr j', .inl k) : ℚ) = μ (.inl k) - cPair P Q) ∧
    (∀ l : Fin S, ∑ j' : Fin Q, (α (.inr j', .inr l) : ℚ) - ∑ i' : Fin P, (α (.inl i', .inr l) : ℚ) = μ (.inr l) + cPair P Q) := by
  obtain ⟨_, hK, hne, hmem⟩ := hf
  rw [GlobalTheory.FockAlg.MinFirst.mem_hwSub] at hmem
  have e1 : ∀ a : Ix P Q, (∑ c, lineSign a c * (((α (a, c) : ℕ) : ℂ) + 1 / 2)) = (x : ℂ) := by
    intro a
    have h := hK (Eab a a) (GlobalTheory.FockAlg.MinFirst.isKC_diag a)
    rw [trace_Eab_self, mul_one] at h
    exact coeff_eig _ _ (fun β => cartan1 a β) f _ h α hα
  have e2 : ∀ c : Ix R S, (∑ a, lineSign a c * (((α (a, c) : ℕ) : ℂ) + 1 / 2)) = (μ c : ℂ) := by
    intro c
    have h := hmem.1 c
    rw [sub_eq_zero] at h
    exact coeff_eig _ _ (fun β => cartan2 c β) f _ h α hα
  refine ⟨fun i' => ?_, fun j' => ?_, fun k => ?_, fun l => ?_⟩
  · have h := e1 (.inl i')
    simp only [Fintype.sum_sum_type, lineSign, one_mul, neg_one_mul, Finset.sum_neg_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    have h' : ((∑ k : Fin R, (α (.inl i', .inl k) : ℚ) - ∑ l : Fin S, (α (.inl i', .inr l) : ℚ) + R / 2 - S / 2 : ℚ) : ℂ) = (x : ℂ) := by
      push_cast; rw [← h]; ring
    have h'' := Rat.cast_injective h'
    simp only [cPair]; linarith
  · have h := e1 (.inr j')
    simp only [Fintype.sum_sum_type, lineSign, one_mul, neg_one_mul, Finset.sum_neg_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    have h' : ((∑ l : Fin S, (α (.inr j', .inr l) : ℚ) - ∑ k : Fin R, (α (.inr j', .inl k) : ℚ) - R / 2 + S / 2 : ℚ) : ℂ) = (x : ℂ) := by
      push_cast; rw [← h]; ring
    have h'' := Rat.cast_injective h'
    simp only [cPair]; linarith
  · have h := e2 (.inl k)
    simp only [Fintype.sum_sum_type, lineSign, one_mul, neg_one_mul, Finset.sum_neg_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    have h' : ((∑ i' : Fin P, (α (.inl i', .inl k) : ℚ) - ∑ j' : Fin Q, (α (.inr j', .inl k) : ℚ) + P / 2 - Q / 2 : ℚ) : ℂ) = (μ (.inl k) : ℂ) := by
      push_cast; rw [← h]; ring
    have h'' := Rat.cast_injective h'
    simp only [cPair]; linarith
  · have h := e2 (.inr l)
    simp only [Fintype.sum_sum_type, lineSign, one_mul, neg_one_mul, Finset.sum_neg_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    have h' : ((∑ j' : Fin Q, (α (.inr j', .inr l) : ℚ) - ∑ i' : Fin P, (α (.inl i', .inr l) : ℚ) - P / 2 + Q / 2 : ℚ) : ℂ) = (μ (.inr l) : ℂ) := by
      push_cast; rw [← h]; ring
    have h'' := Rat.cast_injective h'
    simp only [cPair]; linarith

/- English proof (translation)
Rewrite using `[Fin.sum_univ_eq_sum_range (fun k => if k < P then a else b) R]`. Take `⟨t, rfl⟩` from `Nat.exists_eq_add_of_le hPR`. Rewrite using `[Finset.sum_range_add]`. Simplify using `[Finset.sum_ite_of_true, Finset.sum_range]`.
-/
theorem sum_fin_ite_lt (P R : ℕ) (hPR : P ≤ R) (a b : ℚ) :
    ∑ k : Fin R, (if (k : ℕ) < P then a else b) = P * a + ((R - P : ℕ) : ℚ) * b := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if k < P then a else b) R]
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hPR
  rw [Finset.sum_range_add]
  simp [Finset.sum_ite_of_true, Finset.sum_range]

/- English proof (translation)
Take `⟨hh, _, hne, hmem⟩` from `hf`. Take `⟨W, fW, hP, sW⟩` from `((GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 f).1`. Establish `hOT` using `((GlobalTheory.BlockReps.finite_module_structure R S _ (fockAct2 P Q R S) GlobalTheory.FockAlg.MinFirst.kLie2 W fW sW fun v _ => GlobalTheory.FockAlg.MinFirst.wts2 v).2.2.2 μ f hP ⟨hne, hmem⟩).2.1`. Take `⟨d, hd, hhom⟩` from `(harmonic_homog_of_type P Q R S).2 μ f hne hOT hh`. Rewrite `hhom` using `[mem_homogeneousSubmodule]`.

Establish `h` using `hhom hα`. Rewrite using `[← hd, ← h]`. Simplify using `[Finsupp.weight_apply, Finsupp.sum_fintype]`.
-/
theorem monomial_cols (P Q R S : ℕ) (x : ℚ) (μ : Ix R S → ℚ) (f : Pol P Q R S)
    (hf : GlobalTheory.RealLift.IsHarmVec x μ f) (α : (Ix P Q × Ix R S) →₀ ℕ) (hα : coeff α f ≠ 0) :
    ∑ y, (α y : ℚ) = degW (cPair P Q) μ := by
  obtain ⟨hh, _, hne, hmem⟩ := hf
  obtain ⟨W, fW, hP, sW⟩ := ((GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 f).1
  have hOT := ((GlobalTheory.BlockReps.finite_module_structure R S _ (fockAct2 P Q R S) GlobalTheory.FockAlg.MinFirst.kLie2 W fW sW
    fun v _ => GlobalTheory.FockAlg.MinFirst.wts2 v).2.2.2 μ f hP ⟨hne, hmem⟩).2.1
  obtain ⟨d, hd, hhom⟩ := (harmonic_homog_of_type P Q R S).2 μ f hne hOT hh
  rw [mem_homogeneousSubmodule] at hhom
  have h := hhom hα
  rw [← hd, ← h]
  simp [Finsupp.weight_apply, Finsupp.sum_fintype]

/- English proof (translation)
Take `⟨_, _, _, _, ⟨n, hn⟩, ⟨m, hm⟩, hκ⟩` from `hN`. Establish `hmn : (n : ℤ) + 1 ≤ m`. Establish `: ((R + S : ℕ) : ℤ) = n + n` using `by exact_mod_cast hn`. Use linear arithmetic over natural numbers and integers. Establish `hmn' : (n : ℚ) + 1 ≤ m` using `by exact_mod_cast hmn`.

Establish `hκq : (κ : ℚ) = m + m` using `by exact_mod_cast hm`. Establish `hnq : (R : ℚ) + S = n + n` using `by exact_mod_cast hn`. Establish `hR : (0 : ℚ) ≤ R` using `Nat.cast_nonneg _`. Establish `hS : (0 : ℚ) ≤ S` using `Nat.cast_nonneg _`. Simplify using `only [cPair]`.

Apply the tactic sequence `constructor <;> linarith`.
-/
theorem alpha_beta_ge_one (P Q P' Q' R S : ℕ) (κ : ℤ) (hN : GlobalTheory.RealLift.Num P Q P' Q' R S κ) :
    1 ≤ (κ : ℚ) / 2 - cPair R S ∧ 1 ≤ (κ : ℚ) / 2 + cPair R S := by
  obtain ⟨_, _, _, _, ⟨n, hn⟩, ⟨m, hm⟩, hκ⟩ := hN
  have hmn : (n : ℤ) + 1 ≤ m := by
    have : ((R + S : ℕ) : ℤ) = n + n := by exact_mod_cast hn
    omega
  have hmn' : (n : ℚ) + 1 ≤ m := by exact_mod_cast hmn
  have hκq : (κ : ℚ) = m + m := by exact_mod_cast hm
  have hnq : (R : ℚ) + S = n + n := by exact_mod_cast hn
  have hR : (0 : ℚ) ≤ R := Nat.cast_nonneg _
  have hS : (0 : ℚ) ≤ S := Nat.cast_nonneg _
  simp only [cPair]
  constructor <;> linarith

/- English proof (translation)
Take `⟨_, _, F3, F4⟩` from `monomial_facts P Q R S x μ f hf α hα`. Establish `F5` using `monomial_cols P Q R S x μ f hf α hα`. Set `A : Ix R S → ℚ` to `fun c => match c with`. Consider the case `.inl k => ∑ i' : Fin P, (α (.inl i', .inl k) : ℚ)`. Consider the case `.inr l => ∑ j' : Fin Q, (α (.inr j', .inr l) : ℚ)`.

Set `B : Ix R S → ℚ` to `fun c => match c with`. Consider the case `.inl k => ∑ j' : Fin Q, (α (.inr j', .inl k) : ℚ)`. Consider the case `.inr l => ∑ i' : Fin P, (α (.inl i', .inr l) : ℚ)`. Establish `hA : ∀ c, 0 ≤ A c`. Apply the tactic sequence `rintro (k | l) <;> exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _`.

Establish `hB : ∀ c, 0 ≤ B c`. Apply the tactic sequence `rintro (k | l) <;> exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _`. Establish `hν : ∀ c, A c - B c = shiftNu (cPair P Q) μ c`. Introduce and unpack `(k | l)`. Conclude with `F3 k`.

Conclude with `F4 l`. Establish `hsum : ∑ c, (A c + B c) = ∑ c, |A c - B c|`. Simplify using `only [hν]`. Rewrite using `[show ∑ c, |shiftNu (cPair P Q) μ c| = degW (cPair P Q) μ from rfl, ← F5]`. Rewrite using `[Fintype.sum_prod_type_right, Fintype.sum_sum_type, Fintype.sum_sum_type]`.

Simplify using `only [A, B, Fintype.sum_sum_type, Finset.sum_add_distrib]`. Expand and normalize the polynomial expressions, which then agree. Establish `hle : ∀ c ∈ Finset.univ, |A c - B c| ≤ A c + B c` using `fun c _ => abs_le.2 ⟨by linarith [hA c, hB c], by linarith [hA c, hB c]⟩`. Establish `hpure` using `(Finset.sum_eq_sum_iff_of_le hle).1 hsum.symm`. Establish `hB0 : ∀ c, 0 ≤ A c - B c → B c = 0`.

Introduce `c hc`. Use `hpure c (Finset.mem_univ _)` as an intermediate fact. Rewrite `this` using `[abs_of_nonneg hc]`. Combine the linear relations using `[hB c]`. Prove the components needed by the constructor for the conclusion.

Introduce `k hk j'`. Establish `h0 : B (.inl k) = 0` using `hB0 (.inl k) (by have := hν (.inl k); simp only [shiftNu] at this; linarith)`. Use `(Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.cast_nonneg _)).1 h0 j' (Finset.mem_univ _)` as an intermediate fact. Conclude with `this` after adjusting the coercions. Introduce `l hl i'`.

Establish `h0 : B (.inr l) = 0` using `hB0 (.inr l) (by have := hν (.inr l); simp only [shiftNu] at this; linarith)`. Use `(Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.cast_nonneg _)).1 h0 i' (Finset.mem_univ _)` as an intermediate fact. Conclude with `this` after adjusting the coercions.
-/
theorem col_pure (P Q R S : ℕ) (x : ℚ) (μ : Ix R S → ℚ) (f : Pol P Q R S)
    (hf : GlobalTheory.RealLift.IsHarmVec x μ f) (α : (Ix P Q × Ix R S) →₀ ℕ) (hα : coeff α f ≠ 0) :
    (∀ k : Fin R, 0 ≤ μ (.inl k) - cPair P Q → ∀ j' : Fin Q, α (.inr j', .inl k) = 0) ∧
    (∀ l : Fin S, 0 ≤ μ (.inr l) + cPair P Q → ∀ i' : Fin P, α (.inl i', .inr l) = 0) := by
  obtain ⟨_, _, F3, F4⟩ := monomial_facts P Q R S x μ f hf α hα
  have F5 := monomial_cols P Q R S x μ f hf α hα
  let A : Ix R S → ℚ := fun c => match c with
    | .inl k => ∑ i' : Fin P, (α (.inl i', .inl k) : ℚ)
    | .inr l => ∑ j' : Fin Q, (α (.inr j', .inr l) : ℚ)
  let B : Ix R S → ℚ := fun c => match c with
    | .inl k => ∑ j' : Fin Q, (α (.inr j', .inl k) : ℚ)
    | .inr l => ∑ i' : Fin P, (α (.inl i', .inr l) : ℚ)
  have hA : ∀ c, 0 ≤ A c := by
    rintro (k | l) <;> exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hB : ∀ c, 0 ≤ B c := by
    rintro (k | l) <;> exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hν : ∀ c, A c - B c = shiftNu (cPair P Q) μ c := by
    rintro (k | l)
    · exact F3 k
    · exact F4 l
  have hsum : ∑ c, (A c + B c) = ∑ c, |A c - B c| := by
    simp only [hν]
    rw [show ∑ c, |shiftNu (cPair P Q) μ c| = degW (cPair P Q) μ from rfl, ← F5]
    rw [Fintype.sum_prod_type_right, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [A, B, Fintype.sum_sum_type, Finset.sum_add_distrib]
    ring
  have hle : ∀ c ∈ Finset.univ, |A c - B c| ≤ A c + B c := fun c _ =>
    abs_le.2 ⟨by linarith [hA c, hB c], by linarith [hA c, hB c]⟩
  have hpure := (Finset.sum_eq_sum_iff_of_le hle).1 hsum.symm
  have hB0 : ∀ c, 0 ≤ A c - B c → B c = 0 := by
    intro c hc
    have := hpure c (Finset.mem_univ _)
    rw [abs_of_nonneg hc] at this
    linarith [hB c]
  constructor
  · intro k hk j'
    have h0 : B (.inl k) = 0 := hB0 (.inl k) (by have := hν (.inl k); simp only [shiftNu] at this; linarith)
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.cast_nonneg _)).1 h0 j' (Finset.mem_univ _)
    exact_mod_cast this
  · intro l hl i'
    have h0 : B (.inr l) = 0 := hB0 (.inr l) (by have := hν (.inr l); simp only [shiftNu] at this; linarith)
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.cast_nonneg _)).1 h0 i' (Finset.mem_univ _)
    exact_mod_cast this

/- English proof (translation)
Apply `pderiv_eq_zero_of_notMem_vars` to reduce the goal to its premises. Introduce `hv`. Rewrite `hv` using `[mem_vars]`. Take `⟨α, hα, hαv⟩` from `hv`. Conclude with `(Finsupp.mem_support_iff.1 hαv) (h α (mem_support_iff.1 hα))`.
-/
theorem pderiv_eq_zero_of_coeff {σ : Type} [DecidableEq σ] (f : MvPolynomial σ ℂ) (v : σ)
    (h : ∀ α, coeff α f ≠ 0 → α v = 0) : pderiv v f = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro hv
  rw [mem_vars] at hv
  obtain ⟨α, hα, hαv⟩ := hv
  exact (Finsupp.mem_support_iff.1 hαv) (h α (mem_support_iff.1 hα))

/- English proof (translation)
Introduce `P Q P' Q' R S κ hN i j f hf`. Take `⟨hα1, hβ1⟩` from `alpha_beta_ge_one P Q P' Q' R S κ hN`. Establish `hPR : P ≤ R` using `by rw [hN.1]; omega`. Use `set μ := GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) (.inl i) (.inr j) with hμ`. Establish `hμl : ∀ k : Fin R, μ (.inl k) - cPair P Q = (if (k : ℕ) < P then (κ : ℚ) / 2 - cPair R S else 0) + (if k = i then 1 else 0)`.

Introduce `k`. Simplify using `only [hμ, GlobalTheory.RealLift.addRoot, GlobalTheory.RealLift.lam, Sum.inl.injEq, reduceCtorEq, if_false, sub_zero]`. Apply the tactic sequence `split_ifs <;> ring`. Establish `hμr : ∀ l : Fin S, μ (.inr l) + cPair P Q = (if (l : ℕ) < Q then (κ : ℚ) / 2 + cPair R S else 0) - (if l = j then 1 else 0)`. Introduce `l`.

Simplify using `only [hμ, GlobalTheory.RealLift.addRoot, GlobalTheory.RealLift.lam, Sum.inr.injEq, reduceCtorEq, if_false, add_zero]`. Apply the tactic sequence `split_ifs <;> ring`. Establish `key : ∀ α, coeff α f ≠ 0 → (∀ (j' : Fin Q) (k : Fin R), α (.inr j', .inl k) = 0) ∧ Q ≤ (j : ℕ)`. Introduce `α hα0`. Take `⟨cw, cu⟩` from `col_pure P Q R S _ μ f hf α hα0`.

Apply the tactic sequence `have hw : ∀ (k : Fin R) (j' : Fin Q), α (.inr j', .inl k) = 0 := fun k => cw k (by rw [hμl]; split_ifs <;> linarith)`. Use `⟨fun j' k => hw k j', ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hj`. Use `push_neg at hj`. Apply the tactic sequence `have hu : ∀ (l : Fin S) (i' : Fin P), α (.inl i', .inr l) = 0 := fun l => cu l (by rw [hμr]; split_ifs <;> first | linarith | (subst_vars; omega))`.

Take `⟨F1, _, F3, _⟩` from `monomial_facts P Q R S _ μ f hf α hα0`. Establish `s1 : ∑ i' : Fin P, (∑ k : Fin R, (α (.inl i', .inl k) : ℚ) - ∑ l : Fin S, (α (.inl i', .inr l) : ℚ)) = P * ((κ : ℚ) / 2 - cPair R S)`. Rewrite using `[Finset.sum_congr rfl (fun i' _ => F1 i')]`. Simplify using `[mul_sub]`. Establish `s3 : ∑ k : Fin R, (∑ i' : Fin P, (α (.inl i', .inl k) : ℚ) - ∑ j' : Fin Q, (α (.inr j', .inl k) : ℚ)) = ∑ k : Fin R, (μ (.inl k) - cPair P Q)` using `Finset.sum_congr rfl fun k _ => F3 k`.

Simplify using `only [hu, hw, Nat.cast_zero, Finset.sum_const_zero, sub_zero] at s1 s3`. Rewrite `s3` using `[Finset.sum_congr rfl (fun k _ => hμl k), Finset.sum_add_distrib, sum_fin_ite_lt P R hPR]`. Simplify using `only [Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_zero, add_zero] at s3`. Rewrite `s3` using `[Finset.sum_comm]`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨α, hα0⟩` from `ne_zero_iff.1 hf.2.2.1`. Conclude with `⟨(key α hα0).2, fun j' k => pderiv_eq_zero_of_coeff f _ fun β hβ => (key β hβ).1 j' k⟩`.
-/
theorem harm_shape_inl_inr : ∀ (P Q P' Q' R S : ℕ) (κ : ℤ), GlobalTheory.RealLift.Num P Q P' Q' R S κ → ∀ (i : Fin R) (j : Fin S)
    (f : Pol P Q R S), GlobalTheory.RealLift.IsHarmVec ((κ : ℚ) / 2) (GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) (.inl i) (.inr j)) f →
    Q ≤ (j : ℕ) ∧ ∀ (j' : Fin Q) (k : Fin R), pderiv ((.inr j', .inl k) : Ix P Q × Ix R S) f = 0 := by
  intro P Q P' Q' R S κ hN i j f hf
  obtain ⟨hα1, hβ1⟩ := alpha_beta_ge_one P Q P' Q' R S κ hN
  have hPR : P ≤ R := by rw [hN.1]; omega
  set μ := GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) (.inl i) (.inr j) with hμ
  have hμl : ∀ k : Fin R, μ (.inl k) - cPair P Q =
      (if (k : ℕ) < P then (κ : ℚ) / 2 - cPair R S else 0) + (if k = i then 1 else 0) := by
    intro k
    simp only [hμ, GlobalTheory.RealLift.addRoot, GlobalTheory.RealLift.lam, Sum.inl.injEq, reduceCtorEq, if_false, sub_zero]
    split_ifs <;> ring
  have hμr : ∀ l : Fin S, μ (.inr l) + cPair P Q =
      (if (l : ℕ) < Q then (κ : ℚ) / 2 + cPair R S else 0) - (if l = j then 1 else 0) := by
    intro l
    simp only [hμ, GlobalTheory.RealLift.addRoot, GlobalTheory.RealLift.lam, Sum.inr.injEq, reduceCtorEq, if_false, add_zero]
    split_ifs <;> ring
  have key : ∀ α, coeff α f ≠ 0 → (∀ (j' : Fin Q) (k : Fin R), α (.inr j', .inl k) = 0) ∧ Q ≤ (j : ℕ) := by
    intro α hα0
    obtain ⟨cw, cu⟩ := col_pure P Q R S _ μ f hf α hα0
    have hw : ∀ (k : Fin R) (j' : Fin Q), α (.inr j', .inl k) = 0 := fun k =>
      cw k (by rw [hμl]; split_ifs <;> linarith)
    refine ⟨fun j' k => hw k j', ?_⟩
    by_contra hj
    push_neg at hj
    have hu : ∀ (l : Fin S) (i' : Fin P), α (.inl i', .inr l) = 0 := fun l =>
      cu l (by rw [hμr]; split_ifs <;> first | linarith | (subst_vars; omega))
    obtain ⟨F1, _, F3, _⟩ := monomial_facts P Q R S _ μ f hf α hα0
    have s1 : ∑ i' : Fin P, (∑ k : Fin R, (α (.inl i', .inl k) : ℚ) - ∑ l : Fin S, (α (.inl i', .inr l) : ℚ)) =
        P * ((κ : ℚ) / 2 - cPair R S) := by
      rw [Finset.sum_congr rfl (fun i' _ => F1 i')]; simp [mul_sub]
    have s3 : ∑ k : Fin R, (∑ i' : Fin P, (α (.inl i', .inl k) : ℚ) - ∑ j' : Fin Q, (α (.inr j', .inl k) : ℚ)) =
        ∑ k : Fin R, (μ (.inl k) - cPair P Q) := Finset.sum_congr rfl fun k _ => F3 k
    simp only [hu, hw, Nat.cast_zero, Finset.sum_const_zero, sub_zero] at s1 s3
    rw [Finset.sum_congr rfl (fun k _ => hμl k), Finset.sum_add_distrib, sum_fin_ite_lt P R hPR] at s3
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_zero, add_zero] at s3
    rw [Finset.sum_comm] at s3
    linarith
  obtain ⟨α, hα0⟩ := ne_zero_iff.1 hf.2.2.1
  exact ⟨(key α hα0).2, fun j' k => pderiv_eq_zero_of_coeff f _ fun β hβ => (key β hβ).1 j' k⟩

/- English proof (translation)
Introduce `P Q P' Q' R S κ hN i j f hf`. Take `⟨hα1, hβ1⟩` from `alpha_beta_ge_one P Q P' Q' R S κ hN`. Establish `hPR : P ≤ R` using `by rw [hN.1]; omega`. Use `set μ := GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) (.inr j) (.inl i) with hμ`. Establish `hμl : ∀ k : Fin R, μ (.inl k) - cPair P Q = (if (k : ℕ) < P then (κ : ℚ) / 2 - cPair R S else 0) - (if k = i then 1 else 0)`.

Introduce `k`. Simplify using `only [hμ, GlobalTheory.RealLift.addRoot, GlobalTheory.RealLift.lam, Sum.inl.injEq, reduceCtorEq, if_false, add_zero]`. Apply the tactic sequence `split_ifs <;> ring`. Establish `hμr : ∀ l : Fin S, μ (.inr l) + cPair P Q = (if (l : ℕ) < Q then (κ : ℚ) / 2 + cPair R S else 0) + (if l = j then 1 else 0)`. Introduce `l`.

Simplify using `only [hμ, GlobalTheory.RealLift.addRoot, GlobalTheory.RealLift.lam, Sum.inr.injEq, reduceCtorEq, if_false, sub_zero]`. Apply the tactic sequence `split_ifs <;> ring`. Establish `key : ∀ α, coeff α f ≠ 0 → (∀ (i' : Fin P) (l : Fin S), α (.inl i', .inr l) = 0) ∧ P ≤ (i : ℕ)`. Introduce `α hα0`. Take `⟨cw, cu⟩` from `col_pure P Q R S _ μ f hf α hα0`.

Apply the tactic sequence `have hu : ∀ (l : Fin S) (i' : Fin P), α (.inl i', .inr l) = 0 := fun l => cu l (by rw [hμr]; split_ifs <;> linarith)`. Use `⟨fun i' l => hu l i', ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hi`. Use `push_neg at hi`. Apply the tactic sequence `have hw : ∀ (k : Fin R) (j' : Fin Q), α (.inr j', .inl k) = 0 := fun k => cw k (by rw [hμl]; split_ifs <;> first | linarith | (subst_vars; omega))`.

Take `⟨F1, _, F3, _⟩` from `monomial_facts P Q R S _ μ f hf α hα0`. Establish `s1 : ∑ i' : Fin P, (∑ k : Fin R, (α (.inl i', .inl k) : ℚ) - ∑ l : Fin S, (α (.inl i', .inr l) : ℚ)) = P * ((κ : ℚ) / 2 - cPair R S)`. Rewrite using `[Finset.sum_congr rfl (fun i' _ => F1 i')]`. Simplify using `[mul_sub]`. Establish `s3 : ∑ k : Fin R, (∑ i' : Fin P, (α (.inl i', .inl k) : ℚ) - ∑ j' : Fin Q, (α (.inr j', .inl k) : ℚ)) = ∑ k : Fin R, (μ (.inl k) - cPair P Q)` using `Finset.sum_congr rfl fun k _ => F3 k`.

Simplify using `only [hu, hw, Nat.cast_zero, Finset.sum_const_zero, sub_zero] at s1 s3`. Rewrite `s3` using `[Finset.sum_congr rfl (fun k _ => hμl k), Finset.sum_sub_distrib, sum_fin_ite_lt P R hPR]`. Simplify using `only [Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_zero, add_zero] at s3`. Rewrite `s3` using `[Finset.sum_comm]`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨α, hα0⟩` from `ne_zero_iff.1 hf.2.2.1`. Conclude with `⟨(key α hα0).2, fun i' l => pderiv_eq_zero_of_coeff f _ fun β hβ => (key β hβ).1 i' l⟩`.
-/
theorem harm_shape_inr_inl : ∀ (P Q P' Q' R S : ℕ) (κ : ℤ), GlobalTheory.RealLift.Num P Q P' Q' R S κ → ∀ (i : Fin R) (j : Fin S)
    (f : Pol P Q R S), GlobalTheory.RealLift.IsHarmVec ((κ : ℚ) / 2) (GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) (.inr j) (.inl i)) f →
    P ≤ (i : ℕ) ∧ ∀ (i' : Fin P) (l : Fin S), pderiv ((.inl i', .inr l) : Ix P Q × Ix R S) f = 0 := by
  intro P Q P' Q' R S κ hN i j f hf
  obtain ⟨hα1, hβ1⟩ := alpha_beta_ge_one P Q P' Q' R S κ hN
  have hPR : P ≤ R := by rw [hN.1]; omega
  set μ := GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) (.inr j) (.inl i) with hμ
  have hμl : ∀ k : Fin R, μ (.inl k) - cPair P Q =
      (if (k : ℕ) < P then (κ : ℚ) / 2 - cPair R S else 0) - (if k = i then 1 else 0) := by
    intro k
    simp only [hμ, GlobalTheory.RealLift.addRoot, GlobalTheory.RealLift.lam, Sum.inl.injEq, reduceCtorEq, if_false, add_zero]
    split_ifs <;> ring
  have hμr : ∀ l : Fin S, μ (.inr l) + cPair P Q =
      (if (l : ℕ) < Q then (κ : ℚ) / 2 + cPair R S else 0) + (if l = j then 1 else 0) := by
    intro l
    simp only [hμ, GlobalTheory.RealLift.addRoot, GlobalTheory.RealLift.lam, Sum.inr.injEq, reduceCtorEq, if_false, sub_zero]
    split_ifs <;> ring
  have key : ∀ α, coeff α f ≠ 0 → (∀ (i' : Fin P) (l : Fin S), α (.inl i', .inr l) = 0) ∧ P ≤ (i : ℕ) := by
    intro α hα0
    obtain ⟨cw, cu⟩ := col_pure P Q R S _ μ f hf α hα0
    have hu : ∀ (l : Fin S) (i' : Fin P), α (.inl i', .inr l) = 0 := fun l =>
      cu l (by rw [hμr]; split_ifs <;> linarith)
    refine ⟨fun i' l => hu l i', ?_⟩
    by_contra hi
    push_neg at hi
    have hw : ∀ (k : Fin R) (j' : Fin Q), α (.inr j', .inl k) = 0 := fun k =>
      cw k (by rw [hμl]; split_ifs <;> first | linarith | (subst_vars; omega))
    obtain ⟨F1, _, F3, _⟩ := monomial_facts P Q R S _ μ f hf α hα0
    have s1 : ∑ i' : Fin P, (∑ k : Fin R, (α (.inl i', .inl k) : ℚ) - ∑ l : Fin S, (α (.inl i', .inr l) : ℚ)) =
        P * ((κ : ℚ) / 2 - cPair R S) := by
      rw [Finset.sum_congr rfl (fun i' _ => F1 i')]; simp [mul_sub]
    have s3 : ∑ k : Fin R, (∑ i' : Fin P, (α (.inl i', .inl k) : ℚ) - ∑ j' : Fin Q, (α (.inr j', .inl k) : ℚ)) =
        ∑ k : Fin R, (μ (.inl k) - cPair P Q) := Finset.sum_congr rfl fun k _ => F3 k
    simp only [hu, hw, Nat.cast_zero, Finset.sum_const_zero, sub_zero] at s1 s3
    rw [Finset.sum_congr rfl (fun k _ => hμl k), Finset.sum_sub_distrib, sum_fin_ite_lt P R hPR] at s3
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_zero, add_zero] at s3
    rw [Finset.sum_comm] at s3
    linarith
  obtain ⟨α, hα0⟩ := ne_zero_iff.1 hf.2.2.1
  exact ⟨(key α hα0).2, fun i' l => pderiv_eq_zero_of_coeff f _ fun β hβ => (key β hβ).1 i' l⟩

open GlobalTheory.RealLift in

/- English proof (translation)
Simplify using `only [casK, addRoot, Fintype.sum_sum_type]`. Simplify using `only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false, sub_zero, add_zero, zero_sub]`. Establish `h1 : ∀ k : Fin R, (μ (.inl k) + if k = i then 1 else 0) ^ 2 = μ (.inl k) ^ 2 + (if k = i then 2 * μ (.inl i) + 1 else 0)`. Apply the tactic sequence `intro k; split_ifs with h <;> [subst h; skip] <;> ring`. Establish `h2 : ∀ k : Fin S, (μ (.inr k) - if k = j then 1 else 0) ^ 2 = μ (.inr k) ^ 2 + (if k = j then -2 * μ (.inr j) + 1 else 0)`.

Apply the tactic sequence `intro k; split_ifs with h <;> [subst h; skip] <;> ring`. Simplify using `only [h1, h2, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem casK_addRoot_lr {R S : ℕ} (μ : Ix R S → ℚ) (i : Fin R) (j : Fin S) :
    casK (addRoot μ (.inl i) (.inr j)) = casK μ + 2 * (μ (.inl i) - μ (.inr j)) + 2 +
      ((R : ℚ) - 1 - 2 * (i : ℕ)) - ((S : ℚ) - 1 - 2 * (j : ℕ)) := by
  simp only [casK, addRoot, Fintype.sum_sum_type]
  simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false, sub_zero, add_zero, zero_sub]
  have h1 : ∀ k : Fin R, (μ (.inl k) + if k = i then 1 else 0) ^ 2 = μ (.inl k) ^ 2 + (if k = i then 2 * μ (.inl i) + 1 else 0) := by
    intro k; split_ifs with h <;> [subst h; skip] <;> ring
  have h2 : ∀ k : Fin S, (μ (.inr k) - if k = j then 1 else 0) ^ 2 = μ (.inr k) ^ 2 + (if k = j then -2 * μ (.inr j) + 1 else 0) := by
    intro k; split_ifs with h <;> [subst h; skip] <;> ring
  simp only [h1, h2, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

open GlobalTheory.RealLift in

/- English proof (translation)
Simplify using `only [casK, addRoot, Fintype.sum_sum_type]`. Simplify using `only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false, sub_zero, add_zero, zero_sub, zero_add]`. Establish `h1 : ∀ k : Fin R, (μ (.inl k) - if k = i then 1 else 0) ^ 2 = μ (.inl k) ^ 2 + (if k = i then -2 * μ (.inl i) + 1 else 0)`. Apply the tactic sequence `intro k; split_ifs with h <;> [subst h; skip] <;> ring`. Establish `h2 : ∀ k : Fin S, (μ (.inr k) + if k = j then 1 else 0) ^ 2 = μ (.inr k) ^ 2 + (if k = j then 2 * μ (.inr j) + 1 else 0)`.

Apply the tactic sequence `intro k; split_ifs with h <;> [subst h; skip] <;> ring`. Simplify using `only [h1, h2, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem casK_addRoot_rl {R S : ℕ} (μ : Ix R S → ℚ) (i : Fin R) (j : Fin S) :
    casK (addRoot μ (.inr j) (.inl i)) = casK μ + 2 * (μ (.inr j) - μ (.inl i)) + 2 +
      ((S : ℚ) - 1 - 2 * (j : ℕ)) - ((R : ℚ) - 1 - 2 * (i : ℕ)) := by
  simp only [casK, addRoot, Fintype.sum_sum_type]
  simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false, sub_zero, add_zero, zero_sub, zero_add]
  have h1 : ∀ k : Fin R, (μ (.inl k) - if k = i then 1 else 0) ^ 2 = μ (.inl k) ^ 2 + (if k = i then -2 * μ (.inl i) + 1 else 0) := by
    intro k; split_ifs with h <;> [subst h; skip] <;> ring
  have h2 : ∀ k : Fin S, (μ (.inr k) + if k = j then 1 else 0) ^ 2 = μ (.inr k) ^ 2 + (if k = j then 2 * μ (.inr j) + 1 else 0) := by
    intro k; split_ifs with h <;> [subst h; skip] <;> ring
  simp only [h1, h2, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/- English proof (translation)
Introduce `P Q P' Q' R S κ hN i j hi hj`. Rewrite using `[casK_addRoot_lr]`. Establish `hj' : ¬ (j : ℕ) < Q` using `not_lt.2 hj`. Simplify using `only [GlobalTheory.RealLift.lam, hi, hj', if_true, if_false, cPair]`. Establish `hk : ((R + S : ℕ) : ℤ) < κ` using `hN.2.2.2.2.2.2`.

Establish `hk' : ((R : ℚ) + S) < (κ : ℚ)` using `by exact_mod_cast hk`. Establish `hi' : ((i : ℕ) : ℚ) + 1 ≤ P` using `by exact_mod_cast hi`. Establish `hj'' : (Q : ℚ) ≤ ((j : ℕ) : ℚ)` using `by exact_mod_cast hj`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem casK_lt_inl_inr : ∀ (P Q P' Q' R S : ℕ) (κ : ℤ), GlobalTheory.RealLift.Num P Q P' Q' R S κ → ∀ (i : Fin R) (j : Fin S),
    (i : ℕ) < P → Q ≤ (j : ℕ) → GlobalTheory.RealLift.casK (GlobalTheory.RealLift.lam P Q R S κ) + ((R + S : ℕ) : ℚ) <
      GlobalTheory.RealLift.casK (GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) (.inl i) (.inr j)) := by
  intro P Q P' Q' R S κ hN i j hi hj
  rw [casK_addRoot_lr]
  have hj' : ¬ (j : ℕ) < Q := not_lt.2 hj
  simp only [GlobalTheory.RealLift.lam, hi, hj', if_true, if_false, cPair]
  have hk : ((R + S : ℕ) : ℤ) < κ := hN.2.2.2.2.2.2
  have hk' : ((R : ℚ) + S) < (κ : ℚ) := by exact_mod_cast hk
  have hi' : ((i : ℕ) : ℚ) + 1 ≤ P := by exact_mod_cast hi
  have hj'' : (Q : ℚ) ≤ ((j : ℕ) : ℚ) := by exact_mod_cast hj
  push_cast
  linarith

/- English proof (translation)
Introduce `P Q P' Q' R S κ hN i j hj hi`. Rewrite using `[casK_addRoot_rl]`. Establish `hi' : ¬ (i : ℕ) < P` using `not_lt.2 hi`. Simplify using `only [GlobalTheory.RealLift.lam, hj, hi', if_true, if_false, cPair]`. Establish `hk : ((R + S : ℕ) : ℤ) < κ` using `hN.2.2.2.2.2.2`.

Establish `hk' : ((R : ℚ) + S) < (κ : ℚ)` using `by exact_mod_cast hk`. Establish `hj'' : ((j : ℕ) : ℚ) + 1 ≤ Q` using `by exact_mod_cast hj`. Establish `hi'' : (P : ℚ) ≤ ((i : ℕ) : ℚ)` using `by exact_mod_cast hi`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem casK_lt_inr_inl : ∀ (P Q P' Q' R S : ℕ) (κ : ℤ), GlobalTheory.RealLift.Num P Q P' Q' R S κ → ∀ (i : Fin R) (j : Fin S),
    (j : ℕ) < Q → P ≤ (i : ℕ) → GlobalTheory.RealLift.casK (GlobalTheory.RealLift.lam P Q R S κ) + ((R + S : ℕ) : ℚ) <
      GlobalTheory.RealLift.casK (GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) (.inr j) (.inl i)) := by
  intro P Q P' Q' R S κ hN i j hj hi
  rw [casK_addRoot_rl]
  have hi' : ¬ (i : ℕ) < P := not_lt.2 hi
  simp only [GlobalTheory.RealLift.lam, hj, hi', if_true, if_false, cPair]
  have hk : ((R + S : ℕ) : ℤ) < κ := hN.2.2.2.2.2.2
  have hk' : ((R : ℚ) + S) < (κ : ℚ) := by exact_mod_cast hk
  have hj'' : ((j : ℕ) : ℚ) + 1 ≤ Q := by exact_mod_cast hj
  have hi'' : (P : ℚ) ≤ ((i : ℕ) : ℚ) := by exact_mod_cast hi
  push_cast
  linarith

/- English proof (translation)
Introduce `P Q P' Q' R S κ hN a b hab f hf`. Apply the tactic sequence `rcases a with i | j <;> rcases b with i' | j'`. Conclude with `absurd trivial hab`. Take `⟨hj, hw⟩` from `harm_shape_inl_inr P Q P' Q' R S κ hN i j' f hf`. Establish `hi : (i : ℕ) < P`.

Assume the negation of the conclusion as `h`. Conclude with `not_hw_of_wFree P Q R S _ i f (not_lt.1 h) (by simp [GlobalTheory.RealLift.addRoot, GlobalTheory.RealLift.lam, h]) hw hf.2.2`. Conclude with `casK_lt_inl_inr P Q P' Q' R S κ hN i j' hi hj`. Take `⟨hi, hu⟩` from `harm_shape_inr_inl P Q P' Q' R S κ hN i' j f hf`. Establish `hj : (j : ℕ) < Q`.

Assume the negation of the conclusion as `h`. Conclude with `not_hw_of_uFree P Q R S _ j f (not_lt.1 h) (by simp [GlobalTheory.RealLift.addRoot, GlobalTheory.RealLift.lam, h]; ring) hu hf.2.2`. Conclude with `casK_lt_inr_inl P Q P' Q' R S κ hN i' j hj hi`. Conclude with `absurd trivial hab`.
-/
theorem _root_.GlobalTheory.RealLift.casK_lt_of_isHarmVec_addRoot : ∀ (P Q P' Q' R S : ℕ) (κ : ℤ), GlobalTheory.RealLift.Num P Q P' Q' R S κ → ∀ a b : Formalism.BasicNotions.TH.Ix R S, ¬ Formalism.BasicNotions.TH.sameBlock a b → ∀ f : Formalism.BasicNotions.TH.Pol P Q R S, GlobalTheory.RealLift.IsHarmVec ((κ : ℚ) / 2) (GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) a b) f → GlobalTheory.RealLift.casK (GlobalTheory.RealLift.lam P Q R S κ) + ((R + S : ℕ) : ℚ) < GlobalTheory.RealLift.casK (GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) a b) := by
  intro P Q P' Q' R S κ hN a b hab f hf
  rcases a with i | j <;> rcases b with i' | j'
  · exact absurd trivial hab
  · obtain ⟨hj, hw⟩ := harm_shape_inl_inr P Q P' Q' R S κ hN i j' f hf
    have hi : (i : ℕ) < P := by
      by_contra h
      exact not_hw_of_wFree P Q R S _ i f (not_lt.1 h) (by simp [GlobalTheory.RealLift.addRoot, GlobalTheory.RealLift.lam, h]) hw hf.2.2
    exact casK_lt_inl_inr P Q P' Q' R S κ hN i j' hi hj
  · obtain ⟨hi, hu⟩ := harm_shape_inr_inl P Q P' Q' R S κ hN i' j f hf
    have hj : (j : ℕ) < Q := by
      by_contra h
      exact not_hw_of_uFree P Q R S _ j f (not_lt.1 h) (by simp [GlobalTheory.RealLift.addRoot, GlobalTheory.RealLift.lam, h]; ring) hu hf.2.2
    exact casK_lt_inr_inl P Q P' Q' R S κ hN i' j hj hi
  · exact absurd trivial hab

end GlobalTheory.RealLift.SteepHarm

end
