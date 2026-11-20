import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.LossBoundNonneg

open Matrix
open scoped ComplexConjugate ContDiff

noncomputable section

namespace CCRuleCW

open Formalism.FourierDecayAlt

section sup

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

/- English proof (translation)
Establish `: Q₁ = Q₂` using `funext h`. Conclude with `this ▸ h₁`.
-/
theorem good_congr {D : ℕ} {Q₁ Q₂ : B.Mat k r → ℂ} (h : ∀ g, Q₁ g = Q₂ g) (h₁ : Good D Q₁) : Good D Q₂ := by
  have : Q₁ = Q₂ := funext h
  exact this ▸ h₁

/- English proof (translation)
Use `⟨h.1, fun ops hl => ?_⟩` and prove the remaining obligations. Take `⟨C, hC⟩` from `h.2 ops hl`. Use `⟨max C 0, fun g hg => (hC g hg).trans ?_⟩` and prove the remaining obligations. Establish `h1` using `one_le_gN g hg`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem good_mono {a b : ℕ} (hab : a ≤ b) (Q : B.Mat k r → ℂ) (h : Good a Q) : Good b Q := by
  refine ⟨h.1, fun ops hl => ?_⟩
  obtain ⟨C, hC⟩ := h.2 ops hl
  refine ⟨max C 0, fun g hg => (hC g hg).trans ?_⟩
  have h1 := one_le_gN g hg
  calc C * B.gN g ^ a ≤ max C 0 * B.gN g ^ a :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (by linarith) _)
    _ ≤ max C 0 * B.gN g ^ b := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 hab) (le_max_right _ _)

/- English proof (translation)
Use `⟨h₁.1.add h₂.1, fun ops hl => ?_⟩` and prove the remaining obligations. Take `⟨C₁, hC₁⟩` from `h₁.2 ops hl`. Take `⟨C₂, hC₂⟩` from `h₂.2 ops hl`. Use `⟨C₁ + C₂, fun g hg => ?_⟩` and prove the remaining obligations. Rewrite using `[apO_add ops hl Q₁ Q₂ (smooth_ck Q₁ h₁.1) (smooth_ck Q₂ h₂.1) g hg]`.

Establish `e1` using `hC₁ g hg`. Establish `e2` using `hC₂ g hg`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem good_add {D : ℕ} (Q₁ Q₂ : B.Mat k r → ℂ) (h₁ : Good D Q₁) (h₂ : Good D Q₂) :
    Good D (fun g => Q₁ g + Q₂ g) := by
  refine ⟨h₁.1.add h₂.1, fun ops hl => ?_⟩
  obtain ⟨C₁, hC₁⟩ := h₁.2 ops hl
  obtain ⟨C₂, hC₂⟩ := h₂.2 ops hl
  refine ⟨C₁ + C₂, fun g hg => ?_⟩
  rw [apO_add ops hl Q₁ Q₂ (smooth_ck Q₁ h₁.1) (smooth_ck Q₂ h₂.1) g hg]
  have e1 := hC₁ g hg
  have e2 := hC₂ g hg
  calc _ ≤ ‖apO ops Q₁ g‖ + ‖apO ops Q₂ g‖ := norm_add_le _ _
    _ ≤ C₁ * B.gN g ^ D + C₂ * B.gN g ^ D := add_le_add e1 e2
    _ = (C₁ + C₂) * B.gN g ^ D := by ring

/- English proof (translation)
Use `⟨h₁.1.mul h₂.1, fun ops hl => ?_⟩` and prove the remaining obligations. Establish `hterm : ∀ p ∈ splits ops, ∃ C, ∀ g ∈ B.GV k r, ‖apO p.1 Q₁ g • apO p.2 Q₂ g‖ ≤ C * B.gN g ^ (a + b)`. Introduce `p hp`. Take `⟨s1, s2⟩` from `mem_splits _ p hp`. Take `⟨C₁, hC₁⟩` from `h₁.2 p.1 (fun o ho => hl o (s1.subset ho))`.

Take `⟨C₂, hC₂⟩` from `h₂.2 p.2 (fun o ho => hl o (s2.subset ho))`. Use `⟨max C₁ 0 * max C₂ 0, fun g hg => ?_⟩` and prove the remaining obligations. Rewrite using `[norm_smul, pow_add]`. Establish `hN : 0 ≤ B.gN g` using `(gN_pos g hg).le`. Establish `e1 : ‖apO p.1 Q₁ g‖ ≤ max C₁ 0 * B.gN g ^ a` using `(hC₁ g hg).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hN _))`.

Establish `e2 : ‖apO p.2 Q₂ g‖ ≤ max C₂ 0 * B.gN g ^ b` using `(hC₂ g hg).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hN _))`. Combine the equalities or inequalities in the displayed calculation. Take `⟨C, hC⟩` from `sum_bound _ (B.GV k r) (fun g => B.gN g ^ (a + b)) (fun (p : List (Bool × B.Mat k r) × List (Bool × B.Mat k r)) (g : B.Mat k r) => ‖apO p.1 Q₁ g • apO p.2 Q₂ g‖) hterm`. Use `⟨C, fun g hg => ?_⟩` and prove the remaining obligations. Establish `e : (fun g => Q₁ g * Q₂ g) = (fun g => Q₁ g • Q₂ g)` using `rfl`.

Rewrite using `[e, leib ops hl Q₁ h₁.1 Q₂ (smooth_ck Q₂ h₂.1) g hg]`. Conclude with `(norm_sum_map_le _ _).trans (hC g hg)`.
-/
theorem good_mul {a b : ℕ} (Q₁ Q₂ : B.Mat k r → ℂ) (h₁ : Good a Q₁) (h₂ : Good b Q₂) :
    Good (a + b) (fun g => Q₁ g * Q₂ g) := by
  refine ⟨h₁.1.mul h₂.1, fun ops hl => ?_⟩
  have hterm : ∀ p ∈ splits ops, ∃ C, ∀ g ∈ B.GV k r,
      ‖apO p.1 Q₁ g • apO p.2 Q₂ g‖ ≤ C * B.gN g ^ (a + b) := by
    intro p hp
    obtain ⟨s1, s2⟩ := mem_splits _ p hp
    obtain ⟨C₁, hC₁⟩ := h₁.2 p.1 (fun o ho => hl o (s1.subset ho))
    obtain ⟨C₂, hC₂⟩ := h₂.2 p.2 (fun o ho => hl o (s2.subset ho))
    refine ⟨max C₁ 0 * max C₂ 0, fun g hg => ?_⟩
    rw [norm_smul, pow_add]
    have hN : 0 ≤ B.gN g := (gN_pos g hg).le
    have e1 : ‖apO p.1 Q₁ g‖ ≤ max C₁ 0 * B.gN g ^ a :=
      (hC₁ g hg).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hN _))
    have e2 : ‖apO p.2 Q₂ g‖ ≤ max C₂ 0 * B.gN g ^ b :=
      (hC₂ g hg).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hN _))
    calc _ ≤ (max C₁ 0 * B.gN g ^ a) * (max C₂ 0 * B.gN g ^ b) :=
          mul_le_mul e1 e2 (norm_nonneg _) (mul_nonneg (le_max_right _ _) (pow_nonneg hN _))
      _ = _ := by ring
  obtain ⟨C, hC⟩ := sum_bound _ (B.GV k r) (fun g => B.gN g ^ (a + b))
    (fun (p : List (Bool × B.Mat k r) × List (Bool × B.Mat k r)) (g : B.Mat k r) =>
      ‖apO p.1 Q₁ g • apO p.2 Q₂ g‖) hterm
  refine ⟨C, fun g hg => ?_⟩
  have e : (fun g => Q₁ g * Q₂ g) = (fun g => Q₁ g • Q₂ g) := rfl
  rw [e, leib ops hl Q₁ h₁.1 Q₂ (smooth_ck Q₂ h₂.1) g hg]
  exact (norm_sum_map_le _ _).trans (hC g hg)

/- English proof (translation)
The claim follows from `| [], c => ⟨c, le_rfl, rfl⟩ | o :: os, c => by have h0 : act o (fun _ : B.Mat k r => c) = fun _ => (0 : ℂ) := by funext g rw [act_eq] simp obtain ⟨c', h1, h2⟩ := apO_const os 0 refine ⟨c', h1.trans (by simp), ?_⟩ simp only [apO_cons, h0, h2]`.
-/
theorem apO_const : ∀ (ops : List (Bool × B.Mat k r)) (c : ℂ),
    ∃ c' : ℂ, ‖c'‖ ≤ ‖c‖ ∧ apO ops (fun _ : B.Mat k r => c) = fun _ => c'
  | [], c => ⟨c, le_rfl, rfl⟩
  | o :: os, c => by
    have h0 : act o (fun _ : B.Mat k r => c) = fun _ => (0 : ℂ) := by
      funext g
      rw [act_eq]
      simp
    obtain ⟨c', h1, h2⟩ := apO_const os 0
    refine ⟨c', h1.trans (by simp), ?_⟩
    simp only [apO_cons, h0, h2]

/- English proof (translation)
Use `⟨contDiff_const, fun ops _ => ?_⟩` and prove the remaining obligations. Take `⟨c', h1, h2⟩` from `apO_const ops c`. Conclude with `⟨‖c‖, fun g _ => by rw [h2, pow_zero, mul_one]; exact h1⟩`.
-/
theorem good_const (c : ℂ) : Good 0 (fun _ : B.Mat k r => c) := by
  refine ⟨contDiff_const, fun ops _ => ?_⟩
  obtain ⟨c', h1, h2⟩ := apO_const ops c
  exact ⟨‖c‖, fun g _ => by rw [h2, pow_zero, mul_one]; exact h1⟩

def dirL (o : Bool × B.Mat k r) : B.Mat k r →L[ℝ] B.Mat k r :=
  LinearMap.toContinuousLinearMap
    { toFun := dir o
      map_add' := fun a b => by
        rcases o with ⟨_ | _, X⟩
        · exact Matrix.add_mul a b X
        · show -(X * (a + b)) = -(X * a) + -(X * b)
          rw [Matrix.mul_add, neg_add]
      map_smul' := fun c a => by
        rcases o with ⟨_ | _, X⟩
        · exact Matrix.smul_mul c a X
        · show -(X * (c • a)) = c • -(X * a)
          rw [Matrix.mul_smul, smul_neg] }

/- English proof (translation)
The claim follows from `| [], ℓ => ⟨ℓ, rfl⟩ | o :: os, ℓ => by have h : act o ⇑ℓ = ⇑(ℓ.comp (dirL o)) := by funext g rw [act_eq] exact (ℓ.hasFDerivAt.comp_hasDerivAt_of_eq 0 (curve_hasDerivAt o g) (curve_zero o g).symm).deriv obtain ⟨ℓ', h'⟩ := apO_clm os (ℓ.comp (dirL o)) exact ⟨ℓ', by simp only [apO_c …`.
-/
theorem apO_clm : ∀ (ops : List (Bool × B.Mat k r)) (ℓ : B.Mat k r →L[ℝ] ℂ),
    ∃ ℓ' : B.Mat k r →L[ℝ] ℂ, apO ops ⇑ℓ = ⇑ℓ'
  | [], ℓ => ⟨ℓ, rfl⟩
  | o :: os, ℓ => by
    have h : act o ⇑ℓ = ⇑(ℓ.comp (dirL o)) := by
      funext g
      rw [act_eq]
      exact (ℓ.hasFDerivAt.comp_hasDerivAt_of_eq 0 (curve_hasDerivAt o g) (curve_zero o g).symm).deriv
    obtain ⟨ℓ', h'⟩ := apO_clm os (ℓ.comp (dirL o))
    exact ⟨ℓ', by simp only [apO_cons, h, h']⟩

/- English proof (translation)
The claim follows from `(Matrix.norm_le_iff (Real.sqrt_nonneg _)).2 fun i j => entry_le_gN g i j`.
-/
theorem sup_le_gN (g : B.Mat k r) : ‖g‖ ≤ B.gN g :=
  (Matrix.norm_le_iff (Real.sqrt_nonneg _)).2 fun i j => entry_le_gN g i j

/- English proof (translation)
Use `⟨ℓ.contDiff, fun ops _ => ?_⟩` and prove the remaining obligations. Take `⟨ℓ', h⟩` from `apO_clm ops ℓ`. Choose the witnesses or unpack the hypotheses as in `⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 < M ∧ ∀ x : B.Mat k r, ‖ℓ' x‖ ≤ M * ‖x‖ := by`. Conclude with `ℓ'.bound`. Use `⟨M, fun g _ => ?_⟩` and prove the remaining obligations.

Rewrite using `[h, pow_one]`. Conclude with `(hM g).trans (mul_le_mul_of_nonneg_left (sup_le_gN g) hM0.le)`.
-/
theorem good_clm (ℓ : B.Mat k r →L[ℝ] ℂ) : Good 1 ⇑ℓ := by
  refine ⟨ℓ.contDiff, fun ops _ => ?_⟩
  obtain ⟨ℓ', h⟩ := apO_clm ops ℓ
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 < M ∧ ∀ x : B.Mat k r, ‖ℓ' x‖ ≤ M * ‖x‖ := by
    exact ℓ'.bound
  refine ⟨M, fun g _ => ?_⟩
  rw [h, pow_one]
  exact (hM g).trans (mul_le_mul_of_nonneg_left (sup_le_gN g) hM0.le)

def coordL (p : Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) : B.Mat k r →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => g p.1 p.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

def ccoordL (p : Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) : B.Mat k r →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => conj (g p.1 p.2)
      map_add' := fun a b => by simp
      map_smul' := fun c a => by simp [Matrix.smul_apply, Complex.real_smul] }

def xv (g : B.Mat k r) : (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) → ℂ :=
  Sum.elim (fun p => g p.1 p.2) (fun p => conj (g p.1 p.2))

/- English proof (translation)
Break down `i with p | p` into its components or cases. Conclude with `good_congr (fun g => rfl) (good_clm (coordL p))`. Conclude with `good_congr (fun g => rfl) (good_clm (ccoordL p))`.
-/
theorem good_var (i : (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) :
    Good 1 (fun g : B.Mat k r => xv g i) := by
  rcases i with p | p
  · exact good_congr (fun g => rfl) (good_clm (coordL p))
  · exact good_congr (fun g => rfl) (good_clm (ccoordL p))

/- English proof (translation)
The claim follows from `| 0 => good_congr (fun g => (pow_zero (Q g)).symm) (good_const 1) | m + 1 => good_congr (fun g => (pow_succ (Q g) m).symm) (good_mul _ _ (good_pow Q h m) h)`.
-/
theorem good_pow (Q : B.Mat k r → ℂ) (h : Good 1 Q) : ∀ m : ℕ, Good m (fun g => Q g ^ m)
  | 0 => good_congr (fun g => (pow_zero (Q g)).symm) (good_const 1)
  | m + 1 => good_congr (fun g => (pow_succ (Q g) m).symm) (good_mul _ _ (good_pow Q h m) h)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using good_const (k := k) (r := r) 1`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `good_congr (fun g => by rw [Finset.prod_insert ha]) (good_mul _ _ (good_pow _ (good_var a) (d a)) ih)`.
-/
theorem good_mono_prod (d : (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) → ℕ)
    (s : Finset ((Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)))) :
    Good (∑ i ∈ s, d i) (fun g : B.Mat k r => ∏ i ∈ s, xv g i ^ d i) := by
  induction s using Finset.induction_on with
  | empty => simpa using good_const (k := k) (r := r) 1
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact good_congr (fun g => by rw [Finset.prod_insert ha])
      (good_mul _ _ (good_pow _ (good_var a) (d a)) ih)

/- English proof (translation)
Establish `e : (fun g : B.Mat k r => MvPolynomial.eval (xv g) q) = ∑ d ∈ q.support, fun g : B.Mat k r => q.coeff d * ∏ i ∈ d.support, xv g i ^ d i`. Use function extensionality and compare the values at `g`. Rewrite using `[MvPolynomial.eval_eq, Finset.sum_apply]`. Rewrite using `[e]`. Use `Finset.sum_induction _ (Good D) (fun a b ha hb => good_add a b ha hb) (good_mono (Nat.zero_le D) _ (good_const 0)) ?_` and prove the remaining obligations.

Introduce `d hd`. Establish `hdeg : (∑ i ∈ d.support, d i) ≤ D` using `(MvPolynomial.le_totalDegree hd).trans hq`. Conclude with `good_mono (by simpa using hdeg) _ (good_mul _ _ (good_const (q.coeff d)) (good_mono_prod d d.support))`.
-/
theorem good_poly (q : MvPolynomial ((Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) ℂ)
    (D : ℕ) (hq : q.totalDegree ≤ D) :
    Good D (fun g : B.Mat k r => MvPolynomial.eval (xv g) q) := by
  have e : (fun g : B.Mat k r => MvPolynomial.eval (xv g) q) =
      ∑ d ∈ q.support, fun g : B.Mat k r => q.coeff d * ∏ i ∈ d.support, xv g i ^ d i := by
    funext g
    rw [MvPolynomial.eval_eq, Finset.sum_apply]
  rw [e]
  refine Finset.sum_induction _ (Good D) (fun a b ha hb => good_add a b ha hb)
    (good_mono (Nat.zero_le D) _ (good_const 0)) ?_
  intro d hd
  have hdeg : (∑ i ∈ d.support, d i) ≤ D := (MvPolynomial.le_totalDegree hd).trans hq
  exact good_mono (by simpa using hdeg) _ (good_mul _ _ (good_const (q.coeff d)) (good_mono_prod d d.support))

/- English proof (translation)
Introduce `k r E _ _ A F D P hF hP`. Take `⟨q, hq, hPq⟩` from `hP`. Conclude with `main A D P (good_congr (fun g => (hPq g).symm) (good_poly q D hq)) F hF`.
-/
theorem ruleC : C2.RuleC := by
  intro k r E _ _ A F D P hF hP
  obtain ⟨q, hq, hPq⟩ := hP
  exact main A D P (good_congr (fun g => (hPq g).symm) (good_poly q D hq)) F hF

end sup

end CCRuleCW
