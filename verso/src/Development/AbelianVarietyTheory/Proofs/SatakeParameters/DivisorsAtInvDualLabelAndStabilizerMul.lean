import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DivDual

section Abstract

variable {R : Type} [CommRing R] {n : ℕ}

def Dv (Λ : (Fin n → R) → Prop) (O : R → Prop) (e : R) (u : Fin n → R) (A : Matrix (Fin n) (Fin n) R) : Prop :=
  ∃ B : Matrix (Fin n) (Fin n) R,
    (∀ z : Fin n → R, (∀ i, O (z i)) → Λ (e • B.mulVec z)) ∧
    (∀ y, Λ y → ∃ z : Fin n → R, (∀ i, O (z i)) ∧ e • y = e • B.mulVec z) ∧
    (∀ y, Λ y → ∃ z : Fin n → R, (∀ i, O (z i)) ∧ e • A.mulVec y = e • B.mulVec (fun i => u i * z i)) ∧
    (∀ z : Fin n → R, (∀ i, O (z i)) → ∃ y, Λ y ∧ e • A.mulVec y = e • B.mulVec (fun i => u i * z i))

/- English proof (translation)
Take `⟨B, h1, h2, h3, h4⟩` from `h`. Establish `hcancel : ∀ y, A'.mulVec (e • A.mulVec y) = e • y` using `fun y => by`. Rewrite using `[Matrix.mulVec_smul, Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]`. Set `B' : Matrix (Fin n) (Fin n) R` to `Matrix.of fun a j => (A' * B) a j.rev * u j.rev`. Establish `hB' : ∀ z, B'.mulVec z = A'.mulVec (B.mulVec fun i => u i * z i.rev)` using `fun z => by`.

Rewrite using `[Matrix.mulVec_mulVec]`. Use function extensionality and compare the values at `a`. Simplify using `only [B', Matrix.mulVec, dotProduct, Matrix.of_apply]`. Rewrite using `[← Equiv.sum_comp Fin.revPerm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using `only [Fin.revPerm_apply, Fin.rev_rev]`. Expand and normalize the polynomial expressions, which then agree. Establish `hB'' : ∀ z : Fin n → R, B'.mulVec (fun i => u' i * z i) = A'.mulVec (B.mulVec fun i => z i.rev)` using `fun z => by`. Rewrite using `[hB']`. Use `congr 2`.

Use function extensionality and compare the values at `i`. Rewrite using `[← mul_assoc, hu, one_mul]`. Use `⟨B', fun z hz => ?_, fun y hy => ?_, fun y hy => ?_, fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, hyz⟩` from `h4 (fun i => z i.rev) (fun i => hz _)`. Rewrite using `[hB', ← Matrix.mulVec_smul, ← hyz, hcancel]`.

Take `⟨w, hw, hyw⟩` from `h2 y hy`. Rewrite using `[hyw]`. Conclude with `h1 w hw`. Take `⟨z, hz, hyz⟩` from `h3 y hy`. Use `⟨fun i => z i.rev, fun i => hz _, ?_⟩` and prove the remaining obligations.

Rewrite using `[hB', ← Matrix.mulVec_smul]`. Simplify using `only [Fin.rev_rev]`. Rewrite using `[← hyz, hcancel]`. Take `⟨z, hz, hyz⟩` from `h2 y hy`. Use `⟨fun i => z i.rev, fun i => hz _, ?_⟩` and prove the remaining obligations.

Rewrite using `[hB'', ← Matrix.mulVec_smul, ← Matrix.mulVec_smul, hyz]`. Simplify using `only [Fin.rev_rev]`. Use `⟨e • B.mulVec (fun i => z i.rev), h1 _ (fun i => hz _), ?_⟩` and prove the remaining obligations. Rewrite using `[hB'', Matrix.mulVec_smul, smul_smul, he]`.
-/
theorem Dv.inv {Λ : (Fin n → R) → Prop} {O : R → Prop} {e : R} {u u' : Fin n → R}
    {A A' : Matrix (Fin n) (Fin n) R} (he : e * e = e) (hA : A' * A = 1)
    (hu : ∀ i, u i * u' i.rev = 1) (h : Dv Λ O e u A) : Dv Λ O e u' A' := by
  obtain ⟨B, h1, h2, h3, h4⟩ := h
  have hcancel : ∀ y, A'.mulVec (e • A.mulVec y) = e • y := fun y => by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]
  let B' : Matrix (Fin n) (Fin n) R := Matrix.of fun a j => (A' * B) a j.rev * u j.rev
  have hB' : ∀ z, B'.mulVec z = A'.mulVec (B.mulVec fun i => u i * z i.rev) := fun z => by
    rw [Matrix.mulVec_mulVec]
    funext a
    simp only [B', Matrix.mulVec, dotProduct, Matrix.of_apply]
    rw [← Equiv.sum_comp Fin.revPerm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Fin.revPerm_apply, Fin.rev_rev]
    ring
  have hB'' : ∀ z : Fin n → R, B'.mulVec (fun i => u' i * z i) = A'.mulVec (B.mulVec fun i => z i.rev) := fun z => by
    rw [hB']
    congr 2
    funext i
    rw [← mul_assoc, hu, one_mul]
  refine ⟨B', fun z hz => ?_, fun y hy => ?_, fun y hy => ?_, fun z hz => ?_⟩
  · obtain ⟨y, hy, hyz⟩ := h4 (fun i => z i.rev) (fun i => hz _)
    rw [hB', ← Matrix.mulVec_smul, ← hyz, hcancel]
    obtain ⟨w, hw, hyw⟩ := h2 y hy
    rw [hyw]
    exact h1 w hw
  · obtain ⟨z, hz, hyz⟩ := h3 y hy
    refine ⟨fun i => z i.rev, fun i => hz _, ?_⟩
    rw [hB', ← Matrix.mulVec_smul]
    simp only [Fin.rev_rev]
    rw [← hyz, hcancel]
  · obtain ⟨z, hz, hyz⟩ := h2 y hy
    refine ⟨fun i => z i.rev, fun i => hz _, ?_⟩
    rw [hB'', ← Matrix.mulVec_smul, ← Matrix.mulVec_smul, hyz]
    simp only [Fin.rev_rev]
  · refine ⟨e • B.mulVec (fun i => z i.rev), h1 _ (fun i => hz _), ?_⟩
    rw [hB'', Matrix.mulVec_smul, smul_smul, he]

/- English proof (translation)
Take `⟨B, h1, h2, h3, h4⟩` from `h`. Establish `ea : ∀ y, a.mulVec (a'.mulVec y) = y` using `fun y => by`. Rewrite using `[Matrix.mulVec_mulVec, haa, Matrix.one_mulVec]`. Establish `eb : ∀ y, b.mulVec (b'.mulVec y) = y` using `fun y => by`. Rewrite using `[Matrix.mulVec_mulVec, hbb, Matrix.one_mulVec]`.

Use `⟨a * B, fun z hz => ?_, fun y hy => ?_, fun y hy => ?_, fun z hz => ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul]`. Conclude with `(ha _).1 (h1 z hz)`. Take `⟨z, hz, hyz⟩` from `h2 (a'.mulVec y) ((ha _).2 (by rw [ea]; exact hy))`. Use `⟨z, hz, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul, ← hyz, Matrix.mulVec_smul, ea]`. Take `⟨z, hz, hyz⟩` from `h3 (b.mulVec y) ((hb _).1 hy)`. Use `⟨z, hz, ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul, hyz, Matrix.mulVec_smul]`. Take `⟨y, hy, hyz⟩` from `h4 z hz`.

Use `⟨b'.mulVec y, (hb _).2 (by rw [eb]; exact hy), ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, eb, ← Matrix.mulVec_smul, hyz, Matrix.mulVec_smul]`.
-/
theorem Dv.mul {Λ : (Fin n → R) → Prop} {O : R → Prop} {e : R} {u : Fin n → R}
    {A a a' b b' : Matrix (Fin n) (Fin n) R} (haa : a * a' = 1) (hbb : b * b' = 1)
    (ha : ∀ y, Λ y ↔ Λ (a.mulVec y)) (hb : ∀ y, Λ y ↔ Λ (b.mulVec y))
    (h : Dv Λ O e u A) : Dv Λ O e u (a * A * b) := by
  obtain ⟨B, h1, h2, h3, h4⟩ := h
  have ea : ∀ y, a.mulVec (a'.mulVec y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, haa, Matrix.one_mulVec]
  have eb : ∀ y, b.mulVec (b'.mulVec y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, hbb, Matrix.one_mulVec]
  refine ⟨a * B, fun z hz => ?_, fun y hy => ?_, fun y hy => ?_, fun z hz => ?_⟩
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul]
    exact (ha _).1 (h1 z hz)
  · obtain ⟨z, hz, hyz⟩ := h2 (a'.mulVec y) ((ha _).2 (by rw [ea]; exact hy))
    refine ⟨z, hz, ?_⟩
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul, ← hyz, Matrix.mulVec_smul, ea]
  · obtain ⟨z, hz, hyz⟩ := h3 (b.mulVec y) ((hb _).1 hy)
    refine ⟨z, hz, ?_⟩
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul, hyz,
      Matrix.mulVec_smul]
  · obtain ⟨y, hy, hyz⟩ := h4 z hz
    refine ⟨b'.mulVec y, (hb _).2 (by rw [eb]; exact hy), ?_⟩
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, eb, ← Matrix.mulVec_smul, hyz,
      Matrix.mulVec_smul]

end Abstract

/- English proof (translation)
Substitute `hd` using the available equality. Establish `h1 : i.rev.1 < (dualLab d).length` using `by simp only [dualLab, List.length_reverse, List.length_map]; exact i.rev.2`. Rewrite using `[List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ i.2]`. Simplify using `only [dualLab, List.getElem_reverse, List.getElem_map, List.length_map, Fin.val_rev]`. Use `i.2` as an intermediate fact.

Use `congr 2`. Use linear arithmetic over natural numbers and integers.
-/
theorem getD_dualLab (d : List ℤ) {n : ℕ} (hd : d.length = n) (i : Fin n) :
    (dualLab d).getD i.rev.1 0 = -(d.getD i.1 0) := by
  subst hd
  have h1 : i.rev.1 < (dualLab d).length := by simp only [dualLab, List.length_reverse, List.length_map]; exact i.rev.2
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ i.2]
  simp only [dualLab, List.getElem_reverse, List.getElem_map, List.length_map, Fin.val_rev]
  have := i.2
  congr 2
  omega

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem divAt_iff {D : D7} (V : HSp D) (e : Formalism.L2.Theta.AE D) (ϖ : D.host.E) (d : List ℤ) (α : GA D V) :
    DivAt V e ϖ d α ↔ d.length = V.rank ∧ Dv (fun y => y ∈ LamHat V) (fun x => x ∈ intAE D) (finPart D e)
      (fun i => finPart D (incA D (ϖ ^ (d.getD i.1 0)))) (finMat D.sp.cm.sig V.gram α) := Iff.rfl

/- English proof (translation)
Introduce `D V e ϖ d α he hϖ h`. Rewrite `h` using `[divAt_iff]`. Take `⟨hd, h⟩` from `h`. Establish `hm : ∀ g g' : GA D V, finMat D.sp.cm.sig V.gram (g * g') = finMat D.sp.cm.sig V.gram g * finMat D.sp.cm.sig V.gram g'` using `fun g g' => Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_mul _ _ g g'`. Establish `h1 : finMat D.sp.cm.sig V.gram (1 : GA D V) = 1` using `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_one _ _`.

Use `⟨?_, fun a ha b hb => ?_⟩` and prove the remaining obligations. Rewrite using `[divAt_iff]`. Use `⟨by simpa [dualLab] using hd, h.inv (by rw [← map_mul, he]) ?_ fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[← hm, inv_mul_cancel, h1]`. Rewrite using `[getD_dualLab d hd, ← map_mul, ← map_mul, zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ hϖ), map_one, map_one]`.

Rewrite using `[divAt_iff, hm, hm]`. Use `⟨hd, h.mul (a' := finMat D.sp.cm.sig V.gram a⁻¹) (b' := finMat D.sp.cm.sig V.gram b⁻¹) ?_ ?_ ha.2.1 hb.2.1⟩` and prove the remaining obligations. Rewrite using `[← hm, mul_inv_cancel, h1]`. Rewrite using `[← hm, mul_inv_cancel, h1]`.
-/
theorem divAt_inv_and_mul : ∀ {D : D7} (V : HSp D) (e : Formalism.L2.Theta.AE D) (ϖ : D.host.E) (d : List ℤ) (α : GA D V), e * e = e → ϖ ≠ 0 → DivAt V e ϖ d α → DivAt V e ϖ (dualLab d) α⁻¹ ∧ ∀ a ∈ KsphC V ∅, ∀ b ∈ KsphC V ∅, DivAt V e ϖ d (a * α * b) := by
  intro D V e ϖ d α he hϖ h
  rw [divAt_iff] at h
  obtain ⟨hd, h⟩ := h
  have hm : ∀ g g' : GA D V, finMat D.sp.cm.sig V.gram (g * g') =
      finMat D.sp.cm.sig V.gram g * finMat D.sp.cm.sig V.gram g' := fun g g' =>
    Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_mul _ _ g g'
  have h1 : finMat D.sp.cm.sig V.gram (1 : GA D V) = 1 := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_one _ _
  refine ⟨?_, fun a ha b hb => ?_⟩
  · rw [divAt_iff]
    refine ⟨by simpa [dualLab] using hd, h.inv (by rw [← map_mul, he]) ?_ fun i => ?_⟩
    · rw [← hm, inv_mul_cancel, h1]
    · rw [getD_dualLab d hd, ← map_mul, ← map_mul, zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ hϖ), map_one, map_one]
  · rw [divAt_iff, hm, hm]
    refine ⟨hd, h.mul (a' := finMat D.sp.cm.sig V.gram a⁻¹) (b' := finMat D.sp.cm.sig V.gram b⁻¹) ?_ ?_
      ha.2.1 hb.2.1⟩
    · rw [← hm, mul_inv_cancel, h1]
    · rw [← hm, mul_inv_cancel, h1]

end GlobalTheory.DivDual
