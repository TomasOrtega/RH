import Mathlib

namespace Bl.general_b_fact_second_form

/- English proof (translation)
Introduce `K V _ _ _ _ _ _ _ Λ hΛ v`. Establish `hv : v ∈ Submodule.span K (Λ : Set V)`. Rewrite using `[hΛ.span_eq_top]`. Conclude with `Submodule.mem_top`. Proceed by induction on `hv using Submodule.span_induction with`.

Consider the case `mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Λ.zero_mem⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨r, hr, hrx⟩` from `hx`. Take `⟨s, hs, hsy⟩` from `hy`.

Use `⟨r * s, mul_ne_zero hr hs, ?_⟩` and prove the remaining obligations. Establish `h1 : (r * s) • x ∈ Λ` using `by rw [mul_comm, mul_smul]; exact Λ.smul_mem s hrx`. Establish `h2 : (r * s) • y ∈ Λ` using `by rw [mul_smul]; exact Λ.smul_mem r hsy`. Rewrite using `[smul_add]`. Conclude with `Λ.add_mem h1 h2`.

Consider the case `smul c x _ hx`. Take `⟨r, hr, hrx⟩` from `hx`. Take `⟨⟨a, b⟩, hab⟩` from `IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers K)) c`. Simplify using `only at hab`. Use `⟨r * (b : NumberField.RingOfIntegers K), mul_ne_zero hr (nonZeroDivisors.coe_ne_zero b), ?_⟩` and prove the remaining obligations.

Establish `hb : (b : NumberField.RingOfIntegers K) • (c • x) = a • x`. Rewrite using `[← algebraMap_smul K (b : NumberField.RingOfIntegers K) (c • x), smul_smul, mul_comm, hab, algebraMap_smul]`. Rewrite using `[mul_smul, hb, smul_smul, mul_comm, ← smul_smul]`. Conclude with `Λ.smul_mem a hrx`.
-/
theorem goal1 :
  ∀ {K V : Type} [inst : Field.{0} K] [NumberField.{0} K] [StarRing.{0} K] [inst_3 : AddCommGroup.{0} V]
  [inst_4 : Module.{0, 0} K V] [inst_5 : Module.{0, 0} (NumberField.RingOfIntegers.{0} K) V]
  [inst_6 : IsScalarTower.{0, 0, 0} (NumberField.RingOfIntegers.{0} K) K V]
  {Λ : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} K) V},
  Submodule.IsLattice.{0, 0, 0} K Λ →
    ∀ (v : V),
      Exists.{1} fun (r : NumberField.RingOfIntegers.{0} K) ↦
        And (Ne.{1} r 0) (Membership.mem.{0, 0} Λ (HSMul.hSMul.{0, 0, 0} r v)) := by
  intro K V _ _ _ _ _ _ _ Λ hΛ v
  have hv : v ∈ Submodule.span K (Λ : Set V) := by
    rw [hΛ.span_eq_top]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Λ.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨r, hr, hrx⟩ := hx
    obtain ⟨s, hs, hsy⟩ := hy
    refine ⟨r * s, mul_ne_zero hr hs, ?_⟩
    have h1 : (r * s) • x ∈ Λ := by rw [mul_comm, mul_smul]; exact Λ.smul_mem s hrx
    have h2 : (r * s) • y ∈ Λ := by rw [mul_smul]; exact Λ.smul_mem r hsy
    rw [smul_add]; exact Λ.add_mem h1 h2
  | smul c x _ hx =>
    obtain ⟨r, hr, hrx⟩ := hx
    obtain ⟨⟨a, b⟩, hab⟩ :=
      IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers K)) c
    dsimp only at hab
    refine ⟨r * (b : NumberField.RingOfIntegers K),
      mul_ne_zero hr (nonZeroDivisors.coe_ne_zero b), ?_⟩
    have hb : (b : NumberField.RingOfIntegers K) • (c • x) = a • x := by
      rw [← algebraMap_smul K (b : NumberField.RingOfIntegers K) (c • x), smul_smul, mul_comm,
        hab, algebraMap_smul]
    rw [mul_smul, hb, smul_smul, mul_comm, ← smul_smul]
    exact Λ.smul_mem a hrx

end Bl.general_b_fact_second_form
