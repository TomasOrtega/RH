import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtMapComp
open Matrix MeasureTheory Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Gauge
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsionForm.FrameContr

open GlobalTheory.ExtFunctor

variable {m : ℕ}

def contrLin (k : Fin m) : Ext m →ₗ[ℂ] Ext m where
  toFun := contr k
  map_add' v w := by funext S; simp only [contr, Pi.add_apply]; split_ifs <;> ring
  map_smul' c w := by
    funext S; simp only [contr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem contrLin_apply (k : Fin m) (w : Ext m) : contrLin k w = contr k w := rfl

/- English proof (translation)
Establish an intermediate fact. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem sgn_insert_of_not_lt {k i : Fin m} {S : Finset (Fin m)} (h : ¬ k < i) :
    sgn i (insert k S) = sgn i S := by
  have := sgn_erase_of_not_lt (l := i) (S := insert k S) h
  by_cases hk : k ∈ S
  · rw [Finset.insert_eq_of_mem hk]
  · rw [Finset.erase_insert hk] at this; exact this.symm

/- English proof (translation)
Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Apply the first step, then apply the next step to every resulting obligation. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem contr_wedge (k i : Fin m) (w : Ext m) :
    contr k (wedge i w) = (if k = i then (1 : ℂ) else 0) • w - wedge i (contr k w) := by
  by_cases hki : k = i
  · subst hki
    rw [if_pos rfl, one_smul, eq_sub_iff_add_eq, add_comm]; exact wedge_contr_add k w
  rw [if_neg hki, zero_smul, zero_sub]
  funext S
  simp only [contr, wedge, Pi.neg_apply, Finset.mem_insert, Finset.mem_erase]
  by_cases hk : k ∈ S
  · by_cases hi : i ∈ S <;> simp [hk, hi, hki]
  by_cases hi : i ∈ S
  · simp only [hk, hi, if_false, if_true, or_true, and_true, Ne.symm hki, false_and, ne_eq, not_false_eq_true,
      and_false]
    rw [Finset.erase_insert_of_ne hki]
    rcases lt_or_gt_of_ne hki with h | h
    · rw [sgn_insert_of_lt hk h, sgn_erase_of_not_lt (not_lt.2 h.le)]; ring
    · rw [sgn_insert_of_not_lt (not_lt.2 h.le), sgn_erase_of_lt hi h]; ring
  · have hik : i ≠ k := Ne.symm hki
    simp [hk, hi, hki, hik]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem contr_wedgeVec (k : Fin m) (v : Fin m → ℂ) (w : Ext m) :
    contr k (wedgeVec v w) = v k • w - wedgeVec v (contr k w) := by
  rw [wedgeVec_apply, wedgeVec_apply, ← contrLin_apply, map_sum]
  simp_rw [map_smul, contrLin_apply, contr_wedge, smul_sub, Finset.sum_sub_distrib, smul_smul]
  congr 1
  rw [← Finset.sum_smul]
  simp [Finset.sum_ite_eq]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem contr_single_empty (k : Fin m) : contr k (Pi.single (∅ : Finset (Fin m)) (1 : ℂ)) = 0 := by
  funext S
  simp only [contr, Pi.zero_apply]
  split_ifs
  · rfl
  · rw [Pi.single_apply, if_neg (Finset.insert_ne_empty k S), mul_zero]

end GlobalTheory.TorsionForm.FrameContr

namespace GlobalTheory.TorsionForm.FrameContr

open GlobalTheory.ExtFunctor

variable {m : ℕ}

def defect {g : ℕ} (ψ : Matrix (Fin m) (Fin m) ℂ) (d : Fin m) (c : Fin g → ℂ) (x : Fin g → Fin m) :
    Ext m →ₗ[ℂ] Ext m :=
  (extMap ψ).toLinearMap ∘ₗ contrLin d - ∑ a, c a • (contrLin (x a) ∘ₗ (extMap ψ).toLinearMap)

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem defect_apply {g : ℕ} (ψ : Matrix (Fin m) (Fin m) ℂ) (d : Fin m) (c : Fin g → ℂ)
    (x : Fin g → Fin m) (w : Ext m) :
    defect ψ d c x w = extMap ψ (contr d w) - ∑ a, c a • contr (x a) (extMap ψ w) := by
  simp [defect, LinearMap.sum_apply, contrLin_apply]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Normalize the expressions using the abelian group laws.
-/
theorem defect_wedge {g : ℕ} (ψ : Matrix (Fin m) (Fin m) ℂ) (d : Fin m) (c : Fin g → ℂ)
    (x : Fin g → Fin m) (hs : ∀ i, ∑ a, c a * ψ i (x a) = if d = i then 1 else 0) (i : Fin m)
    (w : Ext m) : defect ψ d c x (wedge i w) = - wedgeVec (ψ i) (defect ψ d c x w) := by
  rw [defect_apply, defect_apply, contr_wedge, map_sub, map_smul, extMap_wedge, extMap_wedge]
  simp_rw [contr_wedgeVec, smul_sub, Finset.sum_sub_distrib, smul_smul]
  rw [← Finset.sum_smul, hs i, map_sub, map_sum]
  simp_rw [map_smul]
  abel

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem defect_single {g : ℕ} (ψ : Matrix (Fin m) (Fin m) ℂ) (d : Fin m) (c : Fin g → ℂ)
    (x : Fin g → Fin m) (hs : ∀ i, ∑ a, c a * ψ i (x a) = if d = i then 1 else 0)
    (S : Finset (Fin m)) : defect ψ d c x (Pi.single S 1) = 0 := by
  refine Finset.induction_on_min S ?_ ?_
  · rw [defect_apply, contr_single_empty, map_zero, extMap_single, genProd_empty]
    simp [contr_single_empty]
  · intro a T hmin ih
    have haT : a ∉ T := fun h => lt_irrefl a (hmin a h)
    have e : (Pi.single (insert a T) (1 : ℂ) : Ext m) = wedge a (Pi.single T 1) := by
      rw [wedge_single, if_neg haT, sgn_of_lt_all hmin, one_smul]
    rw [e, defect_wedge ψ d c x hs, ih, map_zero, neg_zero]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem defect_eq_zero {g : ℕ} (ψ : Matrix (Fin m) (Fin m) ℂ) (d : Fin m) (c : Fin g → ℂ)
    (x : Fin g → Fin m) (hs : ∀ i, ∑ a, c a * ψ i (x a) = if d = i then 1 else 0) :
    defect ψ d c x = 0 :=
  (Pi.basisFun ℂ (Finset (Fin m))).ext fun S => by
    rw [Pi.basisFun_apply, defect_single ψ d c x hs, LinearMap.zero_apply]

end GlobalTheory.TorsionForm.FrameContr

namespace GlobalTheory.TorsionForm.FrameContr

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem frame_scalar {g : ℕ} (n : ℕ) (D : Matrix (Fin g) (Fin g) ℂ) (hD : IsUnit D) (d : Fin g)
    (i : Fin (n + n + g)) :
    ∑ a, star (D d a) * fibMat n (D⁻¹)ᴴ i (dzb n a) = if dzb n d = i then 1 else 0 := by
  have hdet : IsUnit D.det := (Matrix.isUnit_iff_isUnit_det D).mp hD
  refine Fin.addCases (fun j => ?_) (fun c => ?_) i
  · have hne : dzb n d ≠ Fin.castAdd g j := by
      intro h; have := congrArg Fin.val h; simp [dzb] at this; omega
    rw [if_neg hne]
    refine Finset.sum_eq_zero fun a _ => ?_
    simp [fibMat, dzb, Matrix.reindex_apply, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd]
  · have hmul : (D * D⁻¹) d c = (1 : Matrix (Fin g) (Fin g) ℂ) d c := by rw [Matrix.mul_nonsing_inv D hdet]
    rw [Matrix.mul_apply] at hmul
    have e : ∑ a, star (D d a) * fibMat n (D⁻¹)ᴴ (Fin.natAdd (n + n) c) (dzb n a) =
        star (∑ a, D d a * D⁻¹ a c) := by
      rw [star_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp [fibMat, dzb, Matrix.reindex_apply, finSumFinEquiv_symm_apply_natAdd, mul_comm]
    rw [e, hmul]
    by_cases hdc : d = c
    · subst hdc; simp [dzb]
    · have : dzb n d ≠ Fin.natAdd (n + n) c := by
        intro h; apply hdc; have := congrArg Fin.val h; simp [dzb] at this; exact Fin.ext this
      simp [Matrix.one_apply_ne hdc, this]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem frameMap_contr_dzb : ∀ {g : ℕ} (n : ℕ) (D : Matrix (Fin g) (Fin g) ℂ), IsUnit D →
    ∀ (d : Fin g) (w : Ext (n + n + g)),
      frameMap n D (contr (dzb n d) w) = ∑ a, star (D d a) • contr (dzb n a) (frameMap n D w) := by
  intro g n D hD d w
  have h := LinearMap.congr_fun (defect_eq_zero (fibMat n (D⁻¹)ᴴ) (dzb n d) (fun a => star (D d a))
    (dzb n) (frame_scalar n D hD d)) w
  rw [defect_apply, LinearMap.zero_apply, sub_eq_zero] at h
  exact h

end GlobalTheory.TorsionForm.FrameContr
