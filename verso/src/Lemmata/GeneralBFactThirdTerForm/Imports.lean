import Mathlib

namespace Bl.general_b_fact_third_ter_form

/- English proof (translation)
Establish `hv : v ∈ Submodule.span K (Λ : Set W)` using `by rw [hspan]; trivial`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Λ.zero_mem⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨s, hs, hsx⟩` from `hx`. Take `⟨t, ht, hty⟩` from `hy`. Use `⟨s * t, mul_ne_zero hs ht, ?_⟩` and prove the remaining obligations. Establish `e : (s * t) • (x + y) = t • (s • x) + s • (t • y)`. Rewrite using `[smul_add, smul_smul, smul_smul, mul_comm t s]`.

Rewrite using `[e]`. Conclude with `Λ.add_mem (Λ.smul_mem t hsx) (Λ.smul_mem s hty)`. Consider the case `smul a x _ hx`. Take `⟨s, hs, hsx⟩` from `hx`. Take `⟨⟨n, d⟩, hnd⟩` from `IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers K)) a`.

Simplify using `only at hnd`. Use `⟨(d : NumberField.RingOfIntegers K) * s, mul_ne_zero (nonZeroDivisors.ne_zero d.2) hs, ?_⟩` and prove the remaining obligations. Establish `e : ((d : NumberField.RingOfIntegers K) * s) • (a • x) = n • (s • x)`. Rewrite using `[← algebraMap_smul K ((d : NumberField.RingOfIntegers K) * s) (a • x), ← algebraMap_smul K s x, ← algebraMap_smul K n, smul_smul, smul_smul]`. Use `congr 1`.

Rewrite using `[map_mul, ← hnd]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Λ.smul_mem n hsx`.
-/
private lemma aux {K W : Type} [Field K] [NumberField K] [AddCommGroup W] [Module K W]
    [Module (NumberField.RingOfIntegers K) W]
    [IsScalarTower (NumberField.RingOfIntegers K) K W]
    (Λ : Submodule (NumberField.RingOfIntegers K) W)
    (hspan : Submodule.span K (Λ : Set W) = ⊤) (v : W) :
    ∃ s : NumberField.RingOfIntegers K, s ≠ 0 ∧ s • v ∈ Λ := by
  have hv : v ∈ Submodule.span K (Λ : Set W) := by rw [hspan]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Λ.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, hty⟩ := hy
    refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
    have e : (s * t) • (x + y) = t • (s • x) + s • (t • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm t s]
    rw [e]
    exact Λ.add_mem (Λ.smul_mem t hsx) (Λ.smul_mem s hty)
  | smul a x _ hx =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨⟨n, d⟩, hnd⟩ :=
      IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers K)) a
    dsimp only at hnd
    refine ⟨(d : NumberField.RingOfIntegers K) * s,
      mul_ne_zero (nonZeroDivisors.ne_zero d.2) hs, ?_⟩
    have e : ((d : NumberField.RingOfIntegers K) * s) • (a • x) = n • (s • x) := by
      rw [← algebraMap_smul K ((d : NumberField.RingOfIntegers K) * s) (a • x),
        ← algebraMap_smul K s x, ← algebraMap_smul K n, smul_smul, smul_smul]
      congr 1
      rw [map_mul, ← hnd]
      ring
    rw [e]
    exact Λ.smul_mem n hsx

/- English proof (translation)
Introduce `K W _ _ _ _ _ _ Λ hΛ v`. Conclude with `aux Λ hΛ.2 v`.
-/
theorem goal1 :
  ∀ {K W : Type} [inst : Field.{0} K] [NumberField.{0} K] [inst_2 : AddCommGroup.{0} W] [inst_3 : Module.{0, 0} K W]
  [inst_4 : Module.{0, 0} (NumberField.RingOfIntegers.{0} K) W]
  [inst_5 : IsScalarTower.{0, 0, 0} (NumberField.RingOfIntegers.{0} K) K W]
  (Λ : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} K) W) [hΛ : Submodule.IsLattice.{0, 0, 0} K Λ] (v : W),
  Exists.{1} fun (s : NumberField.RingOfIntegers.{0} K) ↦
    And (Ne.{1} s 0) (Membership.mem.{0, 0} Λ (HSMul.hSMul.{0, 0, 0} s v)) := by
  intro K W _ _ _ _ _ _ Λ hΛ v
  exact aux Λ hΛ.2 v

end Bl.general_b_fact_third_ter_form
