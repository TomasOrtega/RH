import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Objects
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.FunFieldEquivMemChartRingIff
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

omit [DecidableEq ι] in

/- English proof (translation)
Split into cases according to the possible forms of the given data. Split into cases according to the possible forms of the given data. Split into cases according to the possible forms of the given data. Split into cases according to the possible forms of the given data. Both sides reduce to the same expression.
-/
theorem hermLine_eq_of {A B : HermLine n} (hdeg : A.deg = B.deg) (hmet : A.metric = B.metric) :
    A = B := by
  cases A
  cases B
  cases hdeg
  cases hmet
  rfl

omit [DecidableEq ι] in

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem powDivStd_eq (M : HermLine n) (k : ℕ) :
    powDivStd M k = (M.pow k).mul (HermLine.standard n).inv := by
  refine hermLine_eq_of ?_ ?_
  · funext b
    change (k : ℤ) * M.deg b - 1 = k • M.deg b + -1
    rw [nsmul_eq_mul, sub_eq_add_neg]
  · funext z
    change M.metric z ^ k / (HermLine.standard n).metric z =
      M.metric z ^ k * ((HermLine.standard n).metric z)⁻¹
    rw [div_eq_mul_inv]

omit [DecidableEq ι] in

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem twistPow_eq (M : HermLine n) (p a : ℕ) (C : ℝ) :
    twistPow M p a C =
      (((M.pow p).mul (HermLine.standard n)).pow a).scale (Real.exp (-(a * C))) (Real.exp_pos _) := by
  refine hermLine_eq_of ?_ ?_
  · funext b
    change (a : ℤ) * (p * M.deg b + 1) = a • (p • M.deg b + 1)
    simp only [nsmul_eq_mul]
  · rfl

omit [DecidableEq ι] in

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem twistPow_deg (M : HermLine n) (p a : ℕ) (C : ℝ) :
    (twistPow M p a C).deg = a • (p • M.deg + (HermLine.standard n).deg) := by
  rw [twistPow_eq]
  rfl

omit [DecidableEq ι] in

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem twistPow_metric (M : HermLine n) (p a : ℕ) (C : ℝ) (z : Cone n ℂ) :
    (twistPow M p a C).metric z =
      Real.exp (-(a * C)) * (((M.pow p).mul (HermLine.standard n)).pow a).metric z := by
  rw [twistPow_eq]
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem funFieldEquiv_toFun {P : ArithVariety n} {a : ι → ℤ} (e : IntegralSection P a) :
    funFieldEquiv P e.toFun = sectionVal e := by
  rw [IntegralSection.toFun, map_div₀, funFieldEquiv_mkF, funFieldEquiv_mkF]
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem toFun_eq_symm_sectionVal {P : ArithVariety n} {a : ι → ℤ} (e : IntegralSection P a) :
    e.toFun = (funFieldEquiv P).symm (sectionVal e) := by
  rw [← funFieldEquiv_toFun, RingEquiv.symm_apply_apply]

def blockCoordEquiv (k₀ : ι) : Fin (n k₀ + 1) ≃ Coord (fun _ : Unit ↦ n k₀) where
  toFun i := ⟨(), i⟩
  invFun v := v.2
  left_inv _ := rfl
  right_inv := fun ⟨(), _⟩ ↦ rfl

omit [Fintype ι] in

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem oneBlockIdeal_eq_comap_projIdeal (P : ArithVariety n) (k₀ : ι) :
    oneBlockIdeal P k₀ = (P.projIdeal k₀).comap (rename (blockCoordEquiv (n := n) k₀)) := by
  ext f
  rw [oneBlockIdeal, ArithVariety.projIdeal, Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap,
    rename_rename]
  rfl

omit [Fintype ι] in

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem mem_oneBlockPoints_iff (P : ArithVariety n) (k₀ : ι) (w : Fin (n k₀ + 1) → ℂ) :
    w ∈ oneBlockPoints P k₀ ↔
      (fun _ : Unit ↦ w) ∈ Heights.conePoints (P.projIdeal k₀) ℂ := by
  have heval : ∀ f : MvPolynomial (Coord (fun _ : Unit ↦ n k₀)) ℤ,
      evalCone (fun _ : Unit ↦ w) f =
        eval₂ (Int.castRingHom ℂ) w (rename (blockCoordEquiv (n := n) k₀).symm f) := by
    intro f
    rw [evalCone, eval₂_rename]
    rfl
  constructor
  · rintro ⟨hw, hf⟩
    refine ⟨fun _ ↦ hw, fun f hfI ↦ ?_⟩
    rw [heval]
    refine hf _ ?_
    rw [oneBlockIdeal_eq_comap_projIdeal, Ideal.mem_comap, rename_rename, Equiv.self_comp_symm,
      rename_id_apply]
    exact hfI
  · rintro ⟨hw, hf⟩
    refine ⟨hw (), fun f hfI ↦ ?_⟩
    rw [oneBlockIdeal_eq_comap_projIdeal, Ideal.mem_comap] at hfI
    have h := hf _ hfI
    rw [heval, rename_rename, Equiv.symm_comp_self, rename_id_apply] at h
    exact h

omit [DecidableEq ι] in

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pullFS_metric (k₀ : ι) (z : Cone n ℂ) :
    (pullFS n k₀).metric z =
      (HermLine.standard (fun _ : Unit ↦ n k₀)).metric (Heights.projBlock k₀ z) := rfl

omit [DecidableEq ι] in

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem pullFS_metric_eq_l2Norm (k₀ : ι) (z : Cone n ℂ) :
    (pullFS n k₀).metric z = l2Norm (z k₀) := by
  rw [pullFS_metric]
  change ∏ _u : Unit, l2Norm (z k₀) = _
  rw [Fintype.prod_unique]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
