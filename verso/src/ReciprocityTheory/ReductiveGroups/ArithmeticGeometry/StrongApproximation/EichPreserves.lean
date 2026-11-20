import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.StrongApproximation.SAOpenStatement

namespace ReciprocityTheory.ChartRestriction.G.SA

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R] (σ : R →+* R)
  (J : Matrix ι ι R)

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hf_eq (x y : ι → R) : hf σ J x y = (J *ᵥ (σ ∘ y)) ⬝ᵥ x := by
  simp only [hf, dotProduct, mulVec, Function.comp_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hf_add_left (x x' y : ι → R) : hf σ J (x + x') y = hf σ J x y + hf σ J x' y := by
  simp only [hf, Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hf_smul_left (a : R) (x y : ι → R) : hf σ J (a • x) y = a * hf σ J x y := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hf_neg_left (x y : ι → R) : hf σ J (-x) y = - hf σ J x y := by
  simp only [hf, Pi.neg_apply, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hf_sub_left (x x' y : ι → R) : hf σ J (x - x') y = hf σ J x y - hf σ J x' y := by
  simp only [hf, Pi.sub_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hf_zero_left (y : ι → R) : hf σ J 0 y = 0 := by
  simp [hf]

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hf_add_right (x y y' : ι → R) : hf σ J x (y + y') = hf σ J x y + hf σ J x y' := by
  simp only [hf, Pi.add_apply, map_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hf_smul_right (a : R) (x y : ι → R) : hf σ J x (a • y) = σ a * hf σ J x y := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hf_neg_right (x y : ι → R) : hf σ J x (-y) = - hf σ J x y := by
  simp only [hf, Pi.neg_apply, map_neg, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

variable {σ J}

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem hf_symm (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) (x y : ι → R) :
    σ (hf σ J x y) = hf σ J y x := by
  have hJ' : ∀ i j, σ (J i j) = J j i := by
    intro i j
    have := congrFun (congrFun hJ i) j
    simp only [transpose_apply, map_apply] at this
    exact this.symm
  simp only [hf, map_sum, map_mul, hσ, hJ']
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

variable (σ J) in
/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem hf_mulVec (g : Matrix ι ι R) (x y : ι → R) :
    hf σ J (g *ᵥ x) (g *ᵥ y) = hf σ (gᵀ * J * g.map σ) x y := by
  have key : ∀ (M : Matrix ι ι R) (x y : ι → R), hf σ M x y = x ⬝ᵥ (M *ᵥ (σ ∘ y)) := by
    intro M x y
    rw [hf_eq, dotProduct_comm]
  have hs : σ ∘ (g *ᵥ y) = g.map σ *ᵥ (σ ∘ y) := by
    funext i
    simp [mulVec, dotProduct, map_sum]
  rw [key, key, hs, ← mulVec_mulVec, ← mulVec_mulVec]
  conv_rhs => rw [dotProduct_mulVec, vecMul_transpose]

variable (σ) in
/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem hf_single (M : Matrix ι ι R) (i j : ι) :
    hf σ M (Pi.single i 1) (Pi.single j 1) = M i j := by
  have hs : ∀ k, σ ((Pi.single j (1 : R) : ι → R) k) = (Pi.single j (1 : R) : ι → R) k := by
    intro k
    by_cases h : k = j
    · subst h; simp
    · simp [Pi.single_apply, h]
  simp [hf, hs, Pi.single_apply]

/- English proof (translation)
By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem eq_of_hf (M M' : Matrix ι ι R) (h : ∀ x y, hf σ M x y = hf σ M' x y) : M = M' := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  rwa [hf_single, hf_single] at this

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
theorem mem_SU_iff (g : Matrix ι ι R) :
    g ∈ SU σ J ↔ g.det = 1 ∧ ∀ x y, hf σ J (g *ᵥ x) (g *ᵥ y) = hf σ J x y := by
  constructor
  · rintro ⟨hd, hg⟩
    exact ⟨hd, fun x y => by rw [hf_mulVec, hg]⟩
  · rintro ⟨hd, h⟩
    exact ⟨hd, eq_of_hf (σ := σ) _ _ fun x y => by rw [← hf_mulVec]; exact h x y⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SU_preserves {g : Matrix ι ι R} (hg : g ∈ SU σ J) (x y : ι → R) :
    hf σ J (g *ᵥ x) (g *ᵥ y) = hf σ J x y :=
  ((mem_SU_iff g).1 hg).2 x y

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem one_mem_SU : (1 : Matrix ι ι R) ∈ SU σ J := by
  exact ⟨det_one, by simp⟩

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the hypotheses and the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem mul_mem_SU {g h : Matrix ι ι R} (hg : g ∈ SU σ J) (hh : h ∈ SU σ J) : g * h ∈ SU σ J := by
  refine ⟨by rw [det_mul, hg.1, hh.1, one_mul], ?_⟩
  rw [transpose_mul, Matrix.map_mul,
    show hᵀ * gᵀ * J * (g.map σ * h.map σ) = hᵀ * (gᵀ * J * g.map σ) * h.map σ by
      simp only [Matrix.mul_assoc],
    hg.2, hh.2]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vmv_mulVec (u v w : ι → R) : vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  funext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro j _
  ring

variable (σ J) in

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem eich_mulVec (e u : ι → R) (c : R) (x : ι → R) :
    eich σ J e u c *ᵥ x = x + hf σ J x e • u - hf σ J x u • e + (c * hf σ J x e) • e := by
  simp only [eich, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    vmv_mulVec, ← hf_eq, smul_smul]

section Eich

variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ)
include hσ hJ

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hf_expand (x y u e : ι → R) (a b a' b' : R) :
    hf σ J (x + a • u + b • e) (y + a' • u + b' • e) =
      hf σ J x y + σ a' * hf σ J x u + σ b' * hf σ J x e
      + a * (σ (hf σ J y u) + σ a' * hf σ J u u + σ b' * hf σ J u e)
      + b * (σ (hf σ J y e) + σ a' * hf σ J e u + σ b' * hf σ J e e) := by
  simp only [hf_add_left, hf_add_right, hf_smul_left, hf_smul_right]
  rw [← hf_symm hσ hJ y u, ← hf_symm hσ hJ y e]
  ring

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem eich_preserves {e u : ι → R} {c : R} (he : hf σ J e e = 0) (hue : hf σ J u e = 0)
    (hc : c + σ c + hf σ J u u = 0) (x y : ι → R) :
    hf σ J (eich σ J e u c *ᵥ x) (eich σ J e u c *ᵥ y) = hf σ J x y := by
  have heu : hf σ J e u = 0 := by rw [← hf_symm hσ hJ u e, hue, map_zero]
  have hv : ∀ z, eich σ J e u c *ᵥ z
      = z + hf σ J z e • u + (c * hf σ J z e - hf σ J z u) • e := by
    intro z
    rw [eich_mulVec, sub_smul]
    abel
  rw [hv, hv, hf_expand hσ hJ]
  simp only [he, hue, heu, mul_zero, add_zero, map_sub, map_mul]
  linear_combination (hf σ J x e * σ (hf σ J y e)) * hc

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem eich_det {e u : ι → R} {c : R} (he : hf σ J e e = 0) (hue : hf σ J u e = 0) :
    (eich σ J e u c).det = 1 := by
  have heu : hf σ J e u = 0 := by rw [← hf_symm hσ hJ u e, hue, map_zero]
  set α := J *ᵥ (σ ∘ e)
  set β := J *ᵥ (σ ∘ u)
  have hαe : α ⬝ᵥ e = 0 := by rw [← hf_eq]; exact he
  have hβe : β ⬝ᵥ e = 0 := by rw [← hf_eq]; exact heu
  have hαu : α ⬝ᵥ u = 0 := by rw [← hf_eq]; exact hue

  have hAB : vecMulVec u α * vecMulVec e β = 0 := by
    rw [vecMulVec_mul_vecMulVec, hαe, zero_smul]; ext i j; simp [vecMulVec_apply]
  have hAC : vecMulVec u α * (c • vecMulVec e α) = 0 := by
    rw [Matrix.mul_smul, vecMulVec_mul_vecMulVec, hαe, zero_smul]; ext i j; simp [vecMulVec_apply]
  have hBC : vecMulVec e β * (c • vecMulVec e α) = 0 := by
    rw [Matrix.mul_smul, vecMulVec_mul_vecMulVec, hβe, zero_smul]; ext i j; simp [vecMulVec_apply]
  have hfac : eich σ J e u c
      = (1 + vecMulVec u α) * (1 - vecMulVec e β) * (1 + c • vecMulVec e α) := by
    have h3 : ∀ A B C : Matrix ι ι R, (1 + A) * (1 - B) * (1 + C)
        = 1 + A - B + C - A * B + A * C - B * C - A * B * C := by
      intro A B C; noncomm_ring
    rw [h3, hAB, hAC, hBC]
    simp [eich, α, β]
  have hB : (1 : Matrix ι ι R) - vecMulVec e β = 1 + vecMulVec (-e) β := by
    ext i j; simp [vecMulVec_apply, sub_eq_add_neg]
  have hC : c • vecMulVec e α = vecMulVec (c • e) α := by
    ext i j; simp [vecMulVec_apply, mul_assoc]
  rw [hfac, det_mul, det_mul, hB, hC, vecMulVec_eq Unit, vecMulVec_eq Unit, vecMulVec_eq Unit,
    det_one_add_replicateCol_mul_replicateRow, det_one_add_replicateCol_mul_replicateRow,
    det_one_add_replicateCol_mul_replicateRow, hαu, dotProduct_neg, hβe, dotProduct_smul, hαe]
  simp

end Eich

end ReciprocityTheory.ChartRestriction.G.SA
