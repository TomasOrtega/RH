import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorMaximalCompactBasisSubstitut

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockSubBoth

open GlobalTheory.FockSubst GlobalTheory.FockCompare GlobalTheory.OrientedHeis Complex

/- English proof (translation)
Unfold `unitMap`. Rewrite using `[Matrix.mul_inv_rev]`. Establish `key : k' * single a c (1 : ℂ) * k⁻¹ = ∑ b : Fin m × Fin n, (k' b.1 a * k⁻¹ c b.2) • single b.1 b.2 (1 : ℂ)`. Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, Fintype.sum_prod_type, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', ite_mul, zero_mul]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by`. Rewrite using `[key, Matrix.mul_sum, Matrix.sum_mul]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.mul_smul, Matrix.smul_mul]`.
-/
theorem unitMap_mul_both {m n : ℕ} (B k : Matrix (Fin n) (Fin n) ℂ) (B' k' : Matrix (Fin m) (Fin m) ℂ) (a : Fin m)
    (c : Fin n) : unitMap (B * k) (B' * k') a c =
      ∑ b : Fin m × Fin n, (k' b.1 a * k⁻¹ c b.2) • unitMap B B' b.1 b.2 := by
  unfold unitMap
  rw [Matrix.mul_inv_rev]
  have key : k' * single a c (1 : ℂ) * k⁻¹ = ∑ b : Fin m × Fin n, (k' b.1 a * k⁻¹ c b.2) • single b.1 b.2 (1 : ℂ) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, Fintype.sum_prod_type, ite_and, Finset.sum_ite_eq,
      Finset.sum_ite_eq', ite_mul, zero_mul]
  calc B' * k' * single a c (1 : ℂ) * (k⁻¹ * B⁻¹) = B' * (k' * single a c (1 : ℂ) * k⁻¹) * B⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [key, Matrix.mul_sum, Matrix.sum_mul]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Take `⟨ε, hε, hG, hs⟩` from `h`. Establish `hdiag : (diagonal fun a => ((ε a : _) : ℂ)) = diagonal fun a : Fin k => if a.val < p then (1 : ℂ) else -1`. Use `congr 1`. Use function extensionality and compare the values at `a`. Break down `hε a with ⟨h1, h2⟩ | ⟨h1, h2⟩` into its components or cases.

Simplify using `[h1, h2]`. Simplify using `[h1, not_lt.mpr h2]`. Use `⟨?_, hs.trans (by rw [hdiag])⟩` and prove the remaining obligations. Rewrite using `[isUnit_iff_ne_zero]`. Introduce `h0`.

Establish `hd` using `congrArg Matrix.det hG`. Rewrite `hd` using `[Matrix.det_mul, h0, mul_zero, hdiag, Matrix.det_diagonal]`. Establish `: ∀ a ∈ (Finset.univ : Finset (Fin k)), (if a.val < p then (1 : ℂ) else -1) ≠ 0`. Introduce `a _`. Apply the tactic sequence `split_ifs <;> norm_num`.

Conclude with `(Finset.prod_ne_zero_iff.mpr this) hd.symm`.
-/
theorem onb_sign {k : ℕ} {G s B : Matrix (Fin k) (Fin k) ℂ} {p : ℕ} (h : IsONBasis G s B p) :
    IsUnit B.det ∧ s * B = B * Matrix.diagonal (fun a : Fin k => if a.val < p then (1 : ℂ) else -1) := by
  obtain ⟨ε, hε, hG, hs⟩ := h
  have hdiag : (diagonal fun a => ((ε a : _) : ℂ)) = diagonal fun a : Fin k => if a.val < p then (1 : ℂ) else -1 := by
    congr 1
    funext a
    rcases hε a with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp [h1, h2]
    · simp [h1, not_lt.mpr h2]
  refine ⟨?_, hs.trans (by rw [hdiag])⟩
  rw [isUnit_iff_ne_zero]
  intro h0
  have hd := congrArg Matrix.det hG
  rw [Matrix.det_mul, h0, mul_zero, hdiag, Matrix.det_diagonal] at hd
  have : ∀ a ∈ (Finset.univ : Finset (Fin k)), (if a.val < p then (1 : ℂ) else -1) ≠ 0 := by
    intro a _
    split_ifs <;> norm_num
  exact (Finset.prod_ne_zero_iff.mpr this) hd.symm

/- English proof (translation)
Take `⟨hB, hs⟩` from `onb_sign h`. Take `⟨-, hs'⟩` from `onb_sign h'`. Establish `hinv : B⁻¹ * B = 1` using `Matrix.nonsing_inv_mul B hB`. Establish `hBB : B * B⁻¹ = 1` using `Matrix.mul_nonsing_inv B hB`. Establish `hBi : B⁻¹ * s = diagonal (fun a : Fin n => if a.val < p then (1 : ℂ) else -1) * B⁻¹`.

Combine the equalities or inequalities in the displayed calculation. Establish `e1 : s' * (B' * single i j (1 : ℂ) * B⁻¹) * s = B' * (diagonal (fun a : Fin m => if a.val < p' then (1 : ℂ) else -1) * single i j (1 : ℂ) * diagonal (fun a : Fin n => if a.val < p then (1 : ℂ) else -1)) * B⁻¹`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [hs', hBi]; simp only [Matrix.mul_assoc]`.

Establish `e2 : diagonal (fun a : Fin m => if a.val < p' then (1 : ℂ) else -1) * single i j (1 : ℂ) * diagonal (fun a : Fin n => if a.val < p then (1 : ℂ) else -1) = ((if i.val < p' then (1 : ℂ) else -1) * (if j.val < p then (1 : ℂ) else -1)) • single i j (1 : ℂ)`. Use extensionality with `x y`. Simplify using `only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]`. Distinguish the cases in `hxy : i = x ∧ j = y`. Rewrite using `[if_pos hxy]`.

Take `⟨rfl, rfl⟩` from `hxy`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hxy]`. Expand and normalize the polynomial expressions, which then agree. Unfold `cplxO unitMap`.

Rewrite using `[e1, e2, Matrix.mul_smul, Matrix.smul_mul, smul_smul]`. Use `congr 1`. Apply the tactic sequence `by_cases hi : i.val < p' <;> by_cases hj : j.val < p <;> simp [hi, hj]`.
-/
theorem cplxO_unitMap_both {m n : ℕ} {G s B : Matrix (Fin n) (Fin n) ℂ} {p : ℕ} (h : IsONBasis G s B p)
    {G' s' B' : Matrix (Fin m) (Fin m) ℂ} {p' : ℕ} (h' : IsONBasis G' s' B' p') (i : Fin m) (j : Fin n) :
    cplxO s s' (unitMap B B' i j) =
      ((if decide (i.val < p' ↔ j.val < p) then 1 else -1 : ℂ) * I) • unitMap B B' i j := by
  obtain ⟨hB, hs⟩ := onb_sign h
  obtain ⟨-, hs'⟩ := onb_sign h'
  have hinv : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hB
  have hBB : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hB
  have hBi : B⁻¹ * s = diagonal (fun a : Fin n => if a.val < p then (1 : ℂ) else -1) * B⁻¹ := by
    calc B⁻¹ * s = B⁻¹ * s * (B * B⁻¹) := by rw [hBB, Matrix.mul_one]
      _ = B⁻¹ * (s * B) * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = B⁻¹ * (B * diagonal (fun a : Fin n => if a.val < p then (1 : ℂ) else -1)) * B⁻¹ := by rw [hs]
      _ = _ := by rw [← Matrix.mul_assoc B⁻¹, hinv, Matrix.one_mul]
  have e1 : s' * (B' * single i j (1 : ℂ) * B⁻¹) * s =
      B' * (diagonal (fun a : Fin m => if a.val < p' then (1 : ℂ) else -1) * single i j (1 : ℂ) *
        diagonal (fun a : Fin n => if a.val < p then (1 : ℂ) else -1)) * B⁻¹ := by
    calc s' * (B' * single i j (1 : ℂ) * B⁻¹) * s = (s' * B') * single i j (1 : ℂ) * (B⁻¹ * s) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hs', hBi]; simp only [Matrix.mul_assoc]
  have e2 : diagonal (fun a : Fin m => if a.val < p' then (1 : ℂ) else -1) * single i j (1 : ℂ) *
      diagonal (fun a : Fin n => if a.val < p then (1 : ℂ) else -1) =
      ((if i.val < p' then (1 : ℂ) else -1) * (if j.val < p then (1 : ℂ) else -1)) • single i j (1 : ℂ) := by
    ext x y
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    by_cases hxy : i = x ∧ j = y
    · rw [if_pos hxy]
      obtain ⟨rfl, rfl⟩ := hxy
      ring
    · rw [if_neg hxy]
      ring
  unfold cplxO unitMap
  rw [e1, e2, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  congr 1
  by_cases hi : i.val < p' <;> by_cases hj : j.val < p <;> simp [hi, hj]

/- English proof (translation)
Take `⟨hu, hz⟩` from `h`. Establish `hinv : κ⁻¹ = star κ` using `Matrix.inv_eq_right_inv (Matrix.mem_unitaryGroup_iff.mp hu)`. Rewrite using `[hinv, Matrix.star_apply, hz j i (fun h' => hij h'.symm), star_zero]`.
-/
theorem isKMat_inv_zero {k p : ℕ} {κ : Matrix (Fin k) (Fin k) ℂ} (h : IsKMat p κ) {i j : Fin k}
    (hij : ¬ (i.val < p ↔ j.val < p)) : κ⁻¹ i j = 0 := by
  obtain ⟨hu, hz⟩ := h
  have hinv : κ⁻¹ = star κ := Matrix.inv_eq_right_inv (Matrix.mem_unitaryGroup_iff.mp hu)
  rw [hinv, Matrix.star_apply, hz j i (fun h' => hij h'.symm), star_zero]

/- English proof (translation)
Introduce `D ψ θ S T hψ hθ sS BS sT BT pS pT hpS hpT hcS hcT hoS hoT f hf τ κS κT hkS hkT BS' BT' hS hT hne P`. Take `⟨-, hkTz⟩` from `hkT`. Establish `hτ : ∀ (i : Fin T.rank) (j : Fin S.rank) (g : WO S T → ℂ), IsThetaFunO ψ S T g → aPlus (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) (unitMap (BS' τ) (BT' τ) i j) g = ∑ b : Fin T.rank × Fin S.rank, (if (i.val < pT τ ↔ j.val < pS τ) then κT b.1 i * κS⁻¹ j b.2 else starRingEnd ℂ (κT b.1 …`. Introduce `i j g hg`. Rewrite using `[hS, hT, unitMap_mul_both, GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ τ (sS τ) (sT τ) hg]`.

Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.FockSubst.aPlus_dir_smul hψ hθ τ (sS τ) (sT τ) hg (decide (b.1.val < pT τ ↔ b.2.val < pS τ)) _ (cplxO_unitMap_both (hoS τ) (hoT τ) b.1 b.2)]`. Use `congr 1`. Distinguish the cases in `hw : κT b.1 i * κS⁻¹ j b.2 = 0`. Rewrite using `[hw]`.

Simplify using the standard rewrite rules. Establish `h1 : (b.1.val < pT τ ↔ i.val < pT τ)`. Assume the negation of the conclusion as `hc`. Conclude with `hw (by rw [hkTz b.1 i hc, zero_mul])`. Establish `h2 : (j.val < pS τ ↔ b.2.val < pS τ)`.

Assume the negation of the conclusion as `hc`. Conclude with `hw (by rw [isKMat_inv_zero hkS hc, mul_zero])`. Distinguish the cases in `hc : (i.val < pT τ ↔ j.val < pS τ)`. Establish `hd : decide (b.1.val < pT τ ↔ b.2.val < pS τ) = true`. Rewrite using `[decide_eq_true_iff, h1, ← h2]`.

Conclude with `hc`. Rewrite using `[if_pos hd, if_pos hc]`. Establish `hd : ¬ decide (b.1.val < pT τ ↔ b.2.val < pS τ) = true`. Rewrite using `[decide_eq_true_iff, h1, ← h2]`. Conclude with `hc`.

Rewrite using `[if_neg hd, if_neg hc]`. Establish `key` using `GlobalTheory.FockSubst.pure_subst (ι := FVar D T.rank S.rank) (X := WO S T) (κ := Fin T.rank × Fin S.rank) (A := fun k => aPlus (heisO ψ S T) θ k.1 (cplxO (sS k.1) (sT k.1)) (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2)) (A' := fun k => aPlus (heisO ψ S T) θ k.1 (cplxO (sS k.1) (sT k.1 …`. Introduce and unpack `⟨ρ, i, j⟩ g hg`. Simplify using `only`. Distinguish the cases in `hρ : ρ = τ`.

Substitute `hρ` using the available equality. Simplify using `only [if_true]`. Conclude with `hτ i j g hg`. Take `⟨h1, h2⟩` from `hne ρ hρ`. Simplify using `[hρ, h1, h2, ite_smul])`.

Use `hf P`. Establish `hsub : (MvPolynomial.aeval fun v : FVar D T.rank S.rank => ∑ b : Fin T.rank × Fin S.rank, (if v.1 = τ then (if (v.2.1.val < pT τ ↔ v.2.2.val < pS τ) then κT b.1 v.2.1 * κS⁻¹ v.2.2 b.2 else starRingEnd ℂ (κT b.1 v.2.1 * κS⁻¹ v.2.2 b.2)) else (if b = (v.2.1, v.2.2) then 1 else 0)) …`. Unfold `fockSub`. Use `congr 2`. Use function extensionality and compare the values at `y`.

Take `⟨ρ, i, j⟩` from `y`. Distinguish the cases in `hρ : ρ = τ`. Substitute `hρ` using the available equality. Simplify using `only [if_true, Fintype.sum_prod_type, MvPolynomial.smul_eq_C_mul]`. Simplify using `[hρ, ite_smul]`.

Unfold `pureTensorO aPlusAll`. Use `beta_reduce`. Rewrite using `[key, hsub]`.
-/
theorem pureTensorO_fockSub : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ ρ, pS ρ ≤ S.rank) → (∀ ρ, pT ρ ≤ T.rank) → (∀ ρ, IsCartanInv (gramAt D S ρ) (sS ρ)) → (∀ ρ, IsCartanInv (gramAt D T ρ) (sT ρ)) → (∀ ρ, IsONBasis (gramAt D S ρ) (sS ρ) (BS ρ) (pS ρ)) → (∀ ρ, IsONBasis (gramAt D T ρ) (sT ρ) (BT ρ) (pT ρ)) → ∀ f, IsThetaFunO ψ S T f → ∀ (τ : D.what₂.Tau) κS κT, IsKMat (pS τ) κS → IsKMat (pT τ) κT → ∀ (BS' : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), BS' τ = BS τ * κS → BT' τ = BT τ * κT → (∀ ρ, ρ ≠ τ → BS' ρ = BS ρ ∧ BT' ρ = BT ρ) → ∀ P, pureTensorO ψ θ S T sS sT BS' BT' f P = pureTensorO ψ θ S T sS sT BS BT f (fockSub τ (pS τ) (pT τ) κS κT P) := by
  intro D ψ θ S T hψ hθ sS BS sT BT pS pT hpS hpT hcS hcT hoS hoT f hf τ κS κT hkS hkT BS' BT' hS hT hne P
  classical
  obtain ⟨-, hkTz⟩ := hkT
  have hτ : ∀ (i : Fin T.rank) (j : Fin S.rank) (g : WO S T → ℂ), IsThetaFunO ψ S T g →
      aPlus (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) (unitMap (BS' τ) (BT' τ) i j) g =
      ∑ b : Fin T.rank × Fin S.rank, (if (i.val < pT τ ↔ j.val < pS τ) then κT b.1 i * κS⁻¹ j b.2
          else starRingEnd ℂ (κT b.1 i * κS⁻¹ j b.2)) •
        aPlus (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) (unitMap (BS τ) (BT τ) b.1 b.2) g := by
    intro i j g hg
    rw [hS, hT, unitMap_mul_both, GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ τ (sS τ) (sT τ) hg]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [GlobalTheory.FockSubst.aPlus_dir_smul hψ hθ τ (sS τ) (sT τ) hg (decide (b.1.val < pT τ ↔ b.2.val < pS τ)) _
      (cplxO_unitMap_both (hoS τ) (hoT τ) b.1 b.2)]
    congr 1
    by_cases hw : κT b.1 i * κS⁻¹ j b.2 = 0
    · rw [hw]
      simp
    · have h1 : (b.1.val < pT τ ↔ i.val < pT τ) := by
        by_contra hc
        exact hw (by rw [hkTz b.1 i hc, zero_mul])
      have h2 : (j.val < pS τ ↔ b.2.val < pS τ) := by
        by_contra hc
        exact hw (by rw [isKMat_inv_zero hkS hc, mul_zero])
      by_cases hc : (i.val < pT τ ↔ j.val < pS τ)
      · have hd : decide (b.1.val < pT τ ↔ b.2.val < pS τ) = true := by
          rw [decide_eq_true_iff, h1, ← h2]
          exact hc
        rw [if_pos hd, if_pos hc]
      · have hd : ¬ decide (b.1.val < pT τ ↔ b.2.val < pS τ) = true := by
          rw [decide_eq_true_iff, h1, ← h2]
          exact hc
        rw [if_neg hd, if_neg hc]
  have key := GlobalTheory.FockSubst.pure_subst (ι := FVar D T.rank S.rank) (X := WO S T) (κ := Fin T.rank × Fin S.rank)
    (A := fun k => aPlus (heisO ψ S T) θ k.1 (cplxO (sS k.1) (sT k.1)) (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2))
    (A' := fun k => aPlus (heisO ψ S T) θ k.1 (cplxO (sS k.1) (sT k.1)) (unitMap (BS' k.1) (BT' k.1) k.2.1 k.2.2))
    (P := IsThetaFunO ψ S T)
    (fun g g' hg hg' => GlobalTheory.OrientedHeis.theta_add hg hg')
    (fun a g hg => GlobalTheory.OrientedHeis.theta_smul a hg)
    (fun k g hg => GlobalTheory.FockSubst.aPlus_th hψ hθ _ _ _ hg)
    (fun k l g hg => GlobalTheory.FockSubst.aPlus_comm hψ hθ _ _ hcS hcT _ _ hg)
    (fun k g g' hg hg' => GlobalTheory.FockSubst.aPlus_add hψ hθ _ _ _ hg hg')
    (fun k a g hg => GlobalTheory.FockSubst.aPlus_smul hψ hθ _ _ _ a hg)
    (fun k g hg => GlobalTheory.FockSubst.aPlus_th hψ hθ _ _ _ hg)
    (fun k l g hg => GlobalTheory.FockSubst.aPlus_comm hψ hθ _ _ hcS hcT _ _ hg)
    (fun k g g' hg hg' => GlobalTheory.FockSubst.aPlus_add hψ hθ _ _ _ hg hg')
    (fun k a g hg => GlobalTheory.FockSubst.aPlus_smul hψ hθ _ _ _ a hg)
    (fun v b => if v.1 = τ then
        (if (v.2.1.val < pT τ ↔ v.2.2.val < pS τ) then κT b.1 v.2.1 * κS⁻¹ v.2.2 b.2
          else starRingEnd ℂ (κT b.1 v.2.1 * κS⁻¹ v.2.2 b.2))
        else (if b = (v.2.1, v.2.2) then 1 else 0))
    (fun v b => (v.1, b.1, b.2))
    (by
      rintro ⟨ρ, i, j⟩ g hg
      dsimp only
      by_cases hρ : ρ = τ
      · subst hρ
        simp only [if_true]
        exact hτ i j g hg
      · obtain ⟨h1, h2⟩ := hne ρ hρ
        simp [hρ, h1, h2, ite_smul])
    hf P
  have hsub : (MvPolynomial.aeval fun v : FVar D T.rank S.rank => ∑ b : Fin T.rank × Fin S.rank,
      (if v.1 = τ then
        (if (v.2.1.val < pT τ ↔ v.2.2.val < pS τ) then κT b.1 v.2.1 * κS⁻¹ v.2.2 b.2
          else starRingEnd ℂ (κT b.1 v.2.1 * κS⁻¹ v.2.2 b.2))
        else (if b = (v.2.1, v.2.2) then 1 else 0)) •
        (MvPolynomial.X (v.1, b.1, b.2) : MvPolynomial (FVar D T.rank S.rank) ℂ)) P =
      fockSub τ (pS τ) (pT τ) κS κT P := by
    unfold fockSub
    congr 2
    funext y
    obtain ⟨ρ, i, j⟩ := y
    by_cases hρ : ρ = τ
    · subst hρ
      simp only [if_true, Fintype.sum_prod_type, MvPolynomial.smul_eq_C_mul]
    · simp [hρ, ite_smul]
  unfold pureTensorO aPlusAll
  beta_reduce
  rw [key, hsub]

end GlobalTheory.FockSubBoth
