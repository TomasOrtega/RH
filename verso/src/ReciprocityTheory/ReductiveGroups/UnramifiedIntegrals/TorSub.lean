import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorDefs

noncomputable section
open scoped Classical

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)

variable {C : Type} [Field C] (K : Subfield C) (W : WeierstrassCurve C)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem inSub_zero : InSub K (0 : W.toAffine.Point) := trivial

/- English proof (translation)
Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Treat this case separately. Treat this case separately. Treat this case separately.

Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately.

Treat this case separately. A detailed English derivation is pending.
-/
theorem negY_mem_sub (hW : CoeffSub K W) {x y : C} (hx : x ∈ K) (hy : y ∈ K) :
    W.toAffine.negY x y ∈ K := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  simp only [WeierstrassCurve.Affine.negY]
  repeat (first
    | assumption
    | exact K.zero_mem
    | exact K.one_mem
    | apply K.div_mem
    | apply K.sub_mem
    | apply K.add_mem
    | apply K.mul_mem
    | apply K.pow_mem
    | apply K.neg_mem)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Replace the relevant objects with their definitions.

Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately.

Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately.

Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately.

Treat this case separately. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem slope_mem_sub (hW : CoeffSub K W) {x₁ x₂ y₁ y₂ : C} (hx₁ : x₁ ∈ K) (hx₂ : x₂ ∈ K)
    (hy₁ : y₁ ∈ K) (hy₂ : y₂ ∈ K) : W.toAffine.slope x₁ x₂ y₁ y₂ ∈ K := by
  have n1 := negY_mem_sub K W hW hx₁ hy₁
  have n2 := negY_mem_sub K W hW hx₂ hy₂
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  have c2 : (2 : C) ∈ K := by
    have h0 := natCast_mem K 2
    simpa using h0
  have c3 : (3 : C) ∈ K := by
    have h0 := natCast_mem K 3
    simpa using h0
  unfold WeierstrassCurve.Affine.slope
  split_ifs
  · exact K.zero_mem
  · repeat (first
    | assumption
    | exact K.zero_mem
    | exact K.one_mem
    | apply K.div_mem
    | apply K.sub_mem
    | apply K.add_mem
    | apply K.mul_mem
    | apply K.pow_mem
    | apply K.neg_mem)
  · repeat (first
    | assumption
    | exact K.zero_mem
    | exact K.one_mem
    | apply K.div_mem
    | apply K.sub_mem
    | apply K.add_mem
    | apply K.mul_mem
    | apply K.pow_mem
    | apply K.neg_mem)

/- English proof (translation)
Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Treat this case separately. Treat this case separately. Treat this case separately.

Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately.

Treat this case separately. A detailed English derivation is pending.
-/
theorem addX_mem_sub (hW : CoeffSub K W) {x₁ x₂ s : C} (hx₁ : x₁ ∈ K) (hx₂ : x₂ ∈ K)
    (hs : s ∈ K) : W.toAffine.addX x₁ x₂ s ∈ K := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  simp only [WeierstrassCurve.Affine.addX]
  repeat (first
    | assumption
    | exact K.zero_mem
    | exact K.one_mem
    | apply K.div_mem
    | apply K.sub_mem
    | apply K.add_mem
    | apply K.mul_mem
    | apply K.pow_mem
    | apply K.neg_mem)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Treat this case separately. Treat this case separately.

Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately.

Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem addY_mem_sub (hW : CoeffSub K W) {x₁ x₂ y₁ s : C} (hx₁ : x₁ ∈ K) (hx₂ : x₂ ∈ K)
    (hy₁ : y₁ ∈ K) (hs : s ∈ K) : W.toAffine.addY x₁ x₂ y₁ s ∈ K := by
  have hX := addX_mem_sub K W hW hx₁ hx₂ hs
  have hN : W.toAffine.negAddY x₁ x₂ y₁ s ∈ K := by
    simp only [WeierstrassCurve.Affine.negAddY]
    repeat (first
    | assumption
    | exact K.zero_mem
    | exact K.one_mem
    | apply K.div_mem
    | apply K.sub_mem
    | apply K.add_mem
    | apply K.mul_mem
    | apply K.pow_mem
    | apply K.neg_mem)
  simp only [WeierstrassCurve.Affine.addY]
  exact negY_mem_sub K W hW hX hN

/- English proof (translation)
Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.
-/
theorem inSub_neg (hW : CoeffSub K W) (P : W.toAffine.Point) (hP : InSub K P) : InSub K (-P) := by
  cases P with
  | zero => trivial
  | some x y h =>
    rw [WeierstrassCurve.Affine.Point.neg_some]
    exact ⟨hP.1, negY_mem_sub K W hW hP.1 hP.2⟩

/- English proof (translation)
Split into cases according to the possible forms of the given data. Treat this case separately. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Use the resulting assumption. Treat this case separately.

Split into cases according to the possible forms of the given data. Treat this case separately. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Use the resulting assumption. Treat this case separately.

Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Check the elementary cases of the proposition. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Supply the required witnesses or components.
-/
theorem inSub_add (hW : CoeffSub K W) (P Q : W.toAffine.Point) (hP : InSub K P) (hQ : InSub K Q) :
    InSub K (P + Q) := by
  cases P with
  | zero =>
    change InSub K ((0 : W.toAffine.Point) + _)
    rwa [zero_add]
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      change InSub K (_ + (0 : W.toAffine.Point))
      rwa [add_zero]
    | some x₂ y₂ h₂ =>
      by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
      · rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hxy.1 hxy.2]
        trivial
      · rw [WeierstrassCurve.Affine.Point.add_some hxy]
        have hs := slope_mem_sub K W hW hP.1 hQ.1 hP.2 hQ.2
        exact ⟨addX_mem_sub K W hW hP.1 hQ.1 hs, addY_mem_sub K W hW hP.1 hQ.1 hP.2 hs⟩

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem inSub_nsmul (hW : CoeffSub K W) (n : ℕ) (P : W.toAffine.Point) (hP : InSub K P) :
    InSub K (n • P) := by
  induction n with
  | zero => rw [zero_smul]; exact inSub_zero K W
  | succ n ih => rw [succ_nsmul]; exact inSub_add K W hW _ _ ih hP

/- English proof (translation)
Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately.
-/
theorem inSub_px (P : W.toAffine.Point) (hP : InSub K P) : px W P ∈ K ∧ py W P ∈ K := by
  cases P with
  | zero => exact ⟨K.zero_mem, K.zero_mem⟩
  | some x y h => exact hP

end ReciprocityTheory.ChartRestriction.L1
