import Mathlib

open Module

namespace Bl.SecondBlockLemmaM

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add y z _ _ hy hz`. Take `⟨r, hr, hrs⟩` from `hy`.

Take `⟨s, hs, hss⟩` from `hz`. Use `⟨r * s, mul_ne_zero hr hs, ?_⟩` and prove the remaining obligations. Establish `h : (r * s) • (y + z) = s • (r • y) + r • (s • z)`. Rewrite using `[smul_add, smul_smul, smul_smul, mul_comm s r]`. Rewrite using `[h]`.

Conclude with `S.add_mem (S.smul_mem s hrs) (S.smul_mem r hss)`. Consider the case `smul c y _ hy`. Take `⟨r, hr, hrs⟩` from `hy`. Take `⟨⟨a, b⟩, hab⟩` from `IsLocalization.surj (nonZeroDivisors R) c`. Establish `hab' : c * algebraMap R C (b : R) = algebraMap R C a` using `hab`.

Use `⟨(b : R) * r, mul_ne_zero (nonZeroDivisors.ne_zero b.2) hr, ?_⟩` and prove the remaining obligations. Establish `h : ((b : R) * r) • (c • y) = a • (r • y)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h]`. Conclude with `S.smul_mem a hrs`.
-/
theorem goal1 [IsDomain R] [IsFractionRing R C]
    {V : Type} [AddCommGroup V] [Module C V] [Module R V] [IsScalarTower R C V]
    (S : Submodule R V) {x : V} (hx : x ∈ Submodule.span C (S : Set V)) :
    ∃ r : R, r ≠ 0 ∧ r • x ∈ S := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨r, hr, hrs⟩ := hy
    obtain ⟨s, hs, hss⟩ := hz
    refine ⟨r * s, mul_ne_zero hr hs, ?_⟩
    have h : (r * s) • (y + z) = s • (r • y) + r • (s • z) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm s r]
    rw [h]
    exact S.add_mem (S.smul_mem s hrs) (S.smul_mem r hss)
  | smul c y _ hy =>
    obtain ⟨r, hr, hrs⟩ := hy
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors R) c
    have hab' : c * algebraMap R C (b : R) = algebraMap R C a := hab
    refine ⟨(b : R) * r, mul_ne_zero (nonZeroDivisors.ne_zero b.2) hr, ?_⟩
    have h : ((b : R) * r) • (c • y) = a • (r • y) := by
      calc ((b : R) * r) • (c • y) = r • ((b : R) • (c • y)) := by rw [mul_comm, mul_smul]
        _ = r • (((b : R) • c) • y) := by rw [smul_assoc]
        _ = r • ((algebraMap R C a) • y) := by rw [Algebra.smul_def, mul_comm, hab']
        _ = r • (a • y) := by rw [algebraMap_smul]
        _ = a • (r • y) := smul_comm r a y
    rw [h]
    exact S.smul_mem a hrs

end Bl.SecondBlockLemmaM
