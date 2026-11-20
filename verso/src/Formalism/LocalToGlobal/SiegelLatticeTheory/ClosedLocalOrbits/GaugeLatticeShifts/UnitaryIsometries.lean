import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries

open Formalism.L2.SG.HidaSetting

section Form

variable {n : ℕ} (ε : Fin n → Bool)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem hJ_add_right (x y y' : Fin n → ℂ) : hJ ε x (y + y') = hJ ε x y + hJ ε x y' := by
  unfold hJ
  rw [Matrix.mulVec_add, dotProduct_add]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem hJ_smul_right (a : ℂ) (x y : Fin n → ℂ) : hJ ε x (a • y) = a * hJ ε x y := by
  unfold hJ
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem hJ_sub_right (x y y' : Fin n → ℂ) : hJ ε x (y - y') = hJ ε x y - hJ ε x y' := by
  unfold hJ
  rw [Matrix.mulVec_sub, dotProduct_sub]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem hJ_neg_right (x y : Fin n → ℂ) : hJ ε x (-y) = -hJ ε x y := by
  unfold hJ
  rw [Matrix.mulVec_neg, dotProduct_neg]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.
-/
theorem hJ_sum_right {ι : Type*} (s : Finset ι) (x : Fin n → ℂ) (c : ι → ℂ) (y : ι → Fin n → ℂ) :
    hJ ε x (∑ i ∈ s, c i • y i) = ∑ i ∈ s, c i * hJ ε x (y i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [hJ]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hJ_add_right, hJ_smul_right, ih]

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem hJ_conj (x y : Fin n → ℂ) : hJ ε x y = conj (hJ ε y x) := by
  unfold hJ Formalism.REAL.Jm
  simp only [Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, map_sum, map_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs <;> simp <;> ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem hJ_add_left (x x' y : Fin n → ℂ) : hJ ε (x + x') y = hJ ε x y + hJ ε x' y := by
  rw [hJ_conj, hJ_add_right, map_add, ← hJ_conj, ← hJ_conj]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem hJ_smul_left (a : ℂ) (x y : Fin n → ℂ) : hJ ε (a • x) y = conj a * hJ ε x y := by
  rw [hJ_conj, hJ_smul_right, map_mul, ← hJ_conj]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem hJ_sub_left (x x' y : Fin n → ℂ) : hJ ε (x - x') y = hJ ε x y - hJ ε x' y := by
  rw [hJ_conj, hJ_sub_right, map_sub, ← hJ_conj, ← hJ_conj]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem hJ_neg_left (x y : Fin n → ℂ) : hJ ε (-x) y = -hJ ε x y := by
  rw [hJ_conj, hJ_neg_right, map_neg, ← hJ_conj]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem hJ_sum_left {ι : Type*} (s : Finset ι) (c : ι → ℂ) (x : ι → Fin n → ℂ) (y : Fin n → ℂ) :
    hJ ε (∑ i ∈ s, c i • x i) y = ∑ i ∈ s, conj (c i) * hJ ε (x i) y := by
  rw [hJ_conj, hJ_sum_right, map_sum]
  simp only [map_mul, ← hJ_conj]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hJ_self_conj (x : Fin n → ℂ) : conj (hJ ε x x) = hJ ε x x := (hJ_conj ε x x).symm

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem hJ_mulVec (g : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    hJ ε (g *ᵥ x) (g *ᵥ y) = star x ⬝ᵥ ((gᴴ * Formalism.REAL.Jm ε * g) *ᵥ y) := by
  unfold hJ
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

end Form

section Isom

variable {n : ℕ} (ε : Fin n → Bool)

def IsIsom (g : Matrix (Fin n) (Fin n) ℂ) : Prop := ∀ x y, hJ ε (g *ᵥ x) (g *ᵥ y) = hJ ε x y

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem isIsom_one : IsIsom ε 1 := fun x y => by rw [Matrix.one_mulVec, Matrix.one_mulVec]

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem isIsom_mul {A B : Matrix (Fin n) (Fin n) ℂ} (hA : IsIsom ε A) (hB : IsIsom ε B) : IsIsom ε (A * B) := fun x y => by rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA, hB]

/- English proof (translation)
By extensionality, compare the relevant components. Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
theorem matrix_eq_of_form {A B : Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ x y : Fin n → ℂ, star x ⬝ᵥ (A *ᵥ y) = star x ⬝ᵥ (B *ᵥ y)) : A = B := by
  ext i j
  have h1 := h (Pi.single i 1) (Pi.single j 1)
  have hs : star (Pi.single i (1 : ℂ) : Fin n → ℂ) = Pi.single i 1 := by
    funext k
    by_cases hk : k = i
    · subst hk
      simp
    · simp [hk]
  rw [hs] at h1
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h1

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem inUJ_of_isIsom {g : Matrix (Fin n) (Fin n) ℂ} (hg : IsIsom ε g) : Formalism.REAL.inUJ ε g := by
  unfold Formalism.REAL.inUJ
  apply matrix_eq_of_form
  intro x y
  rw [← hJ_mulVec, hg x y]
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
theorem det_ne_zero_of_inUJ {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) : g.det ≠ 0 := by
  intro h0
  have h1 := congrArg Matrix.det hg
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at h1
  have h2 : (Formalism.REAL.Jm ε).det ≠ 0 := by
    unfold Formalism.REAL.Jm
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 (fun a _ => by split_ifs <;> norm_num)
  exact h2 h1.symm

def toUJ {g : Matrix (Fin n) (Fin n) ℂ} (hg : IsIsom ε g) : Formalism.REAL.UJ ε :=
  ⟨Matrix.nonsingInvUnit g (isUnit_iff_ne_zero.mpr (det_ne_zero_of_inUJ ε (inUJ_of_isIsom ε hg))),
    inUJ_of_isIsom ε hg⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem uMat_toUJ {g : Matrix (Fin n) (Fin n) ℂ} (hg : IsIsom ε g) : Formalism.MainNotions.S.uMat (toUJ ε hg) = g := rfl

end Isom

section Transv

variable {n : ℕ} (ε : Fin n → Bool)

def tvL (u : Fin n → ℂ) (ξ : ℂ) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun v := v - (ξ * hJ ε u v) • u
  map_add' v w := by
    simp only [hJ_add_right, mul_add, add_smul]
    abel
  map_smul' a v := by
    simp only [hJ_smul_right, RingHom.id_apply, smul_sub, smul_smul]
    congr 2
    ring

def tv (u : Fin n → ℂ) (ξ : ℂ) : Matrix (Fin n) (Fin n) ℂ := LinearMap.toMatrix' (tvL ε u ξ)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem tv_apply (u : Fin n → ℂ) (ξ : ℂ) (v : Fin n → ℂ) : tv ε u ξ *ᵥ v = v - (ξ * hJ ε u v) • u := by
  unfold tv
  rw [LinearMap.toMatrix'_mulVec]
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem tv_fix (u : Fin n → ℂ) (ξ : ℂ) {p : Fin n → ℂ} (hp : hJ ε u p = 0) : tv ε u ξ *ᵥ p = p := by
  rw [tv_apply, hp, mul_zero, zero_smul, sub_zero]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem tv_isIsom (u : Fin n → ℂ) {ξ : ℂ} (hξ : ξ + conj ξ = ξ * conj ξ * hJ ε u u) : IsIsom ε (tv ε u ξ) := by
  intro x y
  rw [tv_apply, tv_apply, hJ_sub_left, hJ_sub_right, hJ_sub_right, hJ_smul_left, hJ_smul_left,
    hJ_smul_right, hJ_smul_right, hJ_conj ε x u, map_mul]
  linear_combination (-(conj (hJ ε u x)) * hJ ε u y) * hξ

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem step_exists (x y : Fin n → ℂ) (hxy : hJ ε x x = hJ ε y y) (hx : hJ ε x x ≠ 0) :
    ∃ g, IsIsom ε g ∧ g *ᵥ x = y ∧ ∀ p, hJ ε x p = 0 → hJ ε y p = 0 → g *ᵥ p = p := by
  have hcr : conj (hJ ε x x) = hJ ε x x := hJ_self_conj ε x
  have hxy' : hJ ε x y = conj (hJ ε y x) := hJ_conj ε x y
  have gen : ∀ u : Fin n → ℂ, hJ ε u x ≠ 0 → hJ ε u u = hJ ε u x + conj (hJ ε u x) →
      IsIsom ε (tv ε u (hJ ε u x)⁻¹) ∧ tv ε u (hJ ε u x)⁻¹ *ᵥ x = x - u := by
    intro u hu hH
    refine ⟨tv_isIsom ε u ?_, ?_⟩
    · have hb : conj (hJ ε u x) ≠ 0 := by rwa [map_ne_zero]
      rw [map_inv₀]
      linear_combination (-((hJ ε u x)⁻¹ * (conj (hJ ε u x))⁻¹)) * hH +
        (-(conj (hJ ε u x))⁻¹) * (mul_inv_cancel₀ hu) + (-(hJ ε u x)⁻¹) * (mul_inv_cancel₀ hb)
    · rw [tv_apply, inv_mul_cancel₀ hu, one_smul]
  by_cases hA : hJ ε (x - y) x = 0
  · have hyx : hJ ε y x = hJ ε x x := by
      rw [hJ_sub_left] at hA
      exact (sub_eq_zero.1 hA).symm
    have hu1 : hJ ε (x + y) x ≠ 0 := by
      rw [hJ_add_left, hyx]
      intro h2
      apply hx
      linear_combination h2 / 2
    have hH1 : hJ ε (x + y) (x + y) = hJ ε (x + y) x + conj (hJ ε (x + y) x) := by
      simp only [hJ_add_left, hJ_add_right, map_add]
      linear_combination hxy' - hxy - hcr
    obtain ⟨hI1, hm1⟩ := gen (x + y) hu1 hH1
    have hc0 : hJ ε y y ≠ 0 := by rw [← hxy]; exact hx
    have hcy : conj (hJ ε y y) = hJ ε y y := hJ_self_conj ε y
    have hξ2 : 2 / hJ ε y y + conj (2 / hJ ε y y) = 2 / hJ ε y y * conj (2 / hJ ε y y) * hJ ε y y := by
      rw [map_div₀, map_ofNat, hcy]
      field_simp
      ring
    refine ⟨tv ε y (2 / hJ ε y y) * tv ε (x + y) (hJ ε (x + y) x)⁻¹, isIsom_mul ε (tv_isIsom ε y hξ2) hI1, ?_, ?_⟩
    · rw [← Matrix.mulVec_mulVec, hm1]
      have e1 : x - (x + y) = -y := by abel
      rw [e1, tv_apply, hJ_neg_right]
      have e2 : 2 / hJ ε y y * -hJ ε y y = -2 := by field_simp
      rw [e2, neg_smul, sub_neg_eq_add, two_smul]
      abel
    · intro p hp1 hp2
      rw [← Matrix.mulVec_mulVec, tv_fix ε (x + y) _ (by rw [hJ_add_left, hp1, hp2, add_zero]), tv_fix ε y _ hp2]
  · have hH : hJ ε (x - y) (x - y) = hJ ε (x - y) x + conj (hJ ε (x - y) x) := by
      simp only [hJ_sub_left, hJ_sub_right, map_sub]
      linear_combination -hxy' - hxy - hcr
    obtain ⟨hI, hm⟩ := gen (x - y) hA hH
    refine ⟨tv ε (x - y) (hJ ε (x - y) x)⁻¹, hI, ?_, ?_⟩
    · rw [hm, sub_sub_cancel]
    · intro p hp1 hp2
      apply tv_fix
      rw [hJ_sub_left, hp1, hp2, sub_zero]

end Transv

section Orth

variable {n : ℕ} (ε : Fin n → Bool)

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem witt_orth {m : ℕ} (d d' : Fin m → Fin n → ℂ) (hG : ∀ i j, hJ ε (d i) (d j) = hJ ε (d' i) (d' j))
    (horth : ∀ i j, i ≠ j → hJ ε (d i) (d j) = 0) (hnz : ∀ i, hJ ε (d i) (d i) ≠ 0) :
    ∃ g, IsIsom ε g ∧ ∀ i, g *ᵥ d i = d' i := by
  induction m with
  | zero => exact ⟨1, isIsom_one ε, fun i => Fin.elim0 i⟩
  | succ m ih =>
    obtain ⟨g0, hg0, hg0d⟩ := ih (fun i => d (Fin.castSucc i)) (fun i => d' (Fin.castSucc i))
      (fun i j => hG _ _) (fun i j hij => horth _ _ (fun h => hij (Fin.castSucc_injective _ h))) (fun i => hnz _)
    have hxx : hJ ε (g0 *ᵥ d (Fin.last m)) (g0 *ᵥ d (Fin.last m)) =
        hJ ε (d' (Fin.last m)) (d' (Fin.last m)) := by
      rw [hg0 (d (Fin.last m)) (d (Fin.last m)), hG]
    have hx0 : hJ ε (g0 *ᵥ d (Fin.last m)) (g0 *ᵥ d (Fin.last m)) ≠ 0 := by
      rw [hg0 (d (Fin.last m)) (d (Fin.last m))]
      exact hnz _
    obtain ⟨g1, hg1, hg1x, hg1p⟩ := step_exists ε _ _ hxx hx0
    refine ⟨g1 * g0, isIsom_mul ε hg1 hg0, fun i => ?_⟩
    rw [← Matrix.mulVec_mulVec]
    induction i using Fin.lastCases with
    | last => exact hg1x
    | cast i =>
      rw [hg0d i]
      apply hg1p
      · rw [← hg0d i, hg0 (d (Fin.last m)) (d (Fin.castSucc i))]
        exact horth _ _ (Fin.castSucc_lt_last i).ne'
      · rw [← hG (Fin.last m) (Fin.castSucc i)]
        exact horth _ _ (Fin.castSucc_lt_last i).ne'

end Orth

section Gen

variable {n : ℕ} (ε : Fin n → Bool)

def gram {m : ℕ} (x : Fin m → Fin n → ℂ) : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun i j => hJ ε (x i) (x j)

/- English proof (translation)
Replace the relevant objects with their definitions. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem gram_isHermitian {m : ℕ} (x : Fin m → Fin n → ℂ) : (gram ε x).IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  simp only [Matrix.conjTranspose_apply, gram, Matrix.of_apply]
  rw [hJ_conj ε (x i) (x j)]
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem gram_comb {m : ℕ} (x : Fin m → Fin n → ℂ) (A : Matrix (Fin m) (Fin m) ℂ) (k l : Fin m) :
    hJ ε (∑ i, A i k • x i) (∑ j, A j l • x j) = (star A * gram ε x * A) k l := by
  rw [hJ_sum_left]
  simp only [hJ_sum_right, Matrix.mul_apply, Matrix.star_apply, gram, Matrix.of_apply, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [starRingEnd_apply]
  ring

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
theorem recon {m : ℕ} (x : Fin m → Fin n → ℂ) (A : Matrix (Fin m) (Fin m) ℂ) (hA : A * star A = 1) (i : Fin m) :
    ∑ k, star (A i k) • ∑ j, A j k • x j = x i := by
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have h2 : ∀ j, ∑ k, star (A i k) * A j k = if j = i then 1 else 0 := by
    intro j
    have h3 := congrFun (congrFun hA j) i
    rw [Matrix.mul_apply, Matrix.one_apply] at h3
    rw [← h3]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Matrix.star_apply, mul_comm]
  simp only [← Finset.sum_smul, h2]
  simp

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Treat this case separately. Treat this case separately. Establish an intermediate fact.

Treat this case separately. Treat this case separately. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem witt_of_gram {m : ℕ} (x y : Fin m → Fin n → ℂ) (hG : ∀ i j, hJ ε (x i) (x j) = hJ ε (y i) (y j))
    (hnd : (Matrix.of fun i j => hJ ε (x i) (x j)).det ≠ 0) :
    ∃ g : Formalism.REAL.UJ ε, ∀ i, Formalism.MainNotions.S.uMat g *ᵥ x i = y i := by
  have hH : (gram ε x).IsHermitian := gram_isHermitian ε x
  have hU1 : (hH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) * star (hH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) = 1 :=
    by
      first
        | exact Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
        | exact Matrix.mem_unitaryGroup_iff.1 hH.eigenvectorUnitary.2
  have hU2 : star (hH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) * (hH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) = 1 :=
    by
      first
        | exact Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
        | exact Matrix.mem_unitaryGroup_iff'.1 hH.eigenvectorUnitary.2
  have hs := hH.spectral_theorem
  have hΛ : star (hH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) * gram ε x * (hH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) =
      Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) := by
    have e1 := congrArg (fun M => star (hH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) * M *
      (hH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)) hs
    simp only [Unitary.conjStarAlgAut_apply] at e1
    rw [e1]
    simp only [← Matrix.mul_assoc]
    rw [hU2, Matrix.one_mul, Matrix.mul_assoc, hU2, Matrix.mul_one]
  have hdet : (star (hH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) * gram ε x *
      (hH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_mul, mul_comm (star (hH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)).det,
      mul_assoc, ← Matrix.det_mul, hU2, Matrix.det_one, mul_one]
    exact hnd
  rw [hΛ, Matrix.det_diagonal] at hdet
  have hgy : gram ε y = gram ε x := Matrix.ext fun i j => (hG i j).symm
  obtain ⟨g, hg, hgd⟩ := witt_orth ε
    (fun k => ∑ i, (hH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) i k • x i)
    (fun k => ∑ i, (hH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) i k • y i)
    (fun k l => by rw [gram_comb, gram_comb, hgy])
    (fun k l hkl => by rw [gram_comb, hΛ, Matrix.diagonal_apply_ne _ hkl])
    (fun k => by
      rw [gram_comb, hΛ, Matrix.diagonal_apply_eq]
      exact Finset.prod_ne_zero_iff.1 hdet k (Finset.mem_univ k))
  refine ⟨toUJ ε hg, fun i => ?_⟩
  rw [uMat_toUJ, ← recon x _ hU1 i, ← recon y _ hU1 i, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Matrix.mulVec_smul, hgd k]

end Gen

end Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries
