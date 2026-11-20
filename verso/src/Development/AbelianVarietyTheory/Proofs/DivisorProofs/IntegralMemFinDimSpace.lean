import Mathlib
open MeasureTheory Filter Topology

namespace GlobalTheory

/- English proof (translation)
Set `G : Y → V` to `fun y => ⟨Fm y, hFm y⟩`. Set `ev : X → Module.Dual ℂ V` to `fun x => (LinearMap.proj x).comp V.subtype`. Establish `hev : ∀ x v, ev x v = (v : X → ℂ) x` using `fun x v => rfl`. Establish `hspan : Submodule.span ℂ (Set.range ev) = ⊤`. Establish `h0 : (Submodule.span ℂ (Set.range ev)).dualCoannihilator = ⊥`.

Rewrite using `[eq_bot_iff]`. Introduce `v hv`. Rewrite `hv` using `[Submodule.mem_dualCoannihilator]`. Rewrite using `[Submodule.mem_bot]`. Use extensionality with `x`.

Use `hv (ev x) (Submodule.subset_span ⟨x, rfl⟩)` as an intermediate fact. Simplify `this` using `[hev]`. Rewrite using `[← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range ev)), h0]`. Conclude with `Submodule.dualAnnihilator_bot`. Set `P : Submodule ℂ (Module.Dual ℂ V)` to `{ carrier := {φ | Integrable (fun y => φ (G y)) μ} add_mem' := fun {a b} ha hb => by show Integrable (fun y => a (G y) + b (G y)) μ`.

Conclude with `ha.add hb`. Use the proof step `zero_mem' := by simp`. Use the proof step `smul_mem' := fun c φ hφ => by simpa using hφ.const_mul c }`. Establish `hP : ∀ φ : Module.Dual ℂ V, Integrable (fun y => φ (G y)) μ`. Introduce `φ`.

Establish `hle : Submodule.span ℂ (Set.range ev) ≤ P`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `hint x`. Conclude with `hle (hspan ▸ Submodule.mem_top)`.

Set `b` to `Module.finBasis ℂ V`. Set `E` to `b.equivFun`. Establish `hEi : Integrable (fun y => E (G y)) μ`. Rewrite using `[integrable_pi_iff]`. Introduce `j`.

Simplify `hP (b.coord j)` using `[E]`. Use `set c := ∫ y, E (G y) ∂μ`. Establish `key : ∀ x, ∫ y, Fm y x ∂μ = ((E.symm c : V) : X → ℂ) x`. Introduce `x`. Set `ℓ : (Fin (Module.finrank ℂ V) → ℂ) →L[ℂ] ℂ` to `LinearMap.toContinuousLinearMap ((ev x).comp E.symm.toLinearMap)`.

Establish `h1` using `ℓ.integral_comp_comm hEi`. Establish `h2 : ∀ y, ℓ (E (G y)) = Fm y x` using `by intro y; simp [ℓ, hev, G]`. Simplify using `only [h2] at h1`. Rewrite using `[h1]`. Both sides reduce to the same expression.

Establish `: (fun x => ∫ y, Fm y x ∂μ) = ((E.symm c : V) : X → ℂ)` using `funext key`. Rewrite using `[this]`. Conclude with `(E.symm c).2`.
-/
theorem integral_mem_of_finiteDimensional_fun {X Y : Type} [MeasurableSpace Y] (μ : Measure Y)
    (V : Submodule ℂ (X → ℂ)) (hV : FiniteDimensional ℂ V)
    (Fm : Y → X → ℂ) (hFm : ∀ y, Fm y ∈ V) (hint : ∀ x, Integrable (fun y => Fm y x) μ) :
    (fun x => ∫ y, Fm y x ∂μ) ∈ V := by
  classical
  let G : Y → V := fun y => ⟨Fm y, hFm y⟩
  let ev : X → Module.Dual ℂ V := fun x => (LinearMap.proj x).comp V.subtype
  have hev : ∀ x v, ev x v = (v : X → ℂ) x := fun x v => rfl
  have hspan : Submodule.span ℂ (Set.range ev) = ⊤ := by
    have h0 : (Submodule.span ℂ (Set.range ev)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_dualCoannihilator] at hv
      rw [Submodule.mem_bot]
      ext x
      have := hv (ev x) (Submodule.subset_span ⟨x, rfl⟩)
      simpa [hev] using this
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range ev)), h0]
    exact Submodule.dualAnnihilator_bot
  let P : Submodule ℂ (Module.Dual ℂ V) :=
    { carrier := {φ | Integrable (fun y => φ (G y)) μ}
      add_mem' := fun {a b} ha hb => by
        show Integrable (fun y => a (G y) + b (G y)) μ
        exact ha.add hb
      zero_mem' := by simp
      smul_mem' := fun c φ hφ => by simpa using hφ.const_mul c }
  have hP : ∀ φ : Module.Dual ℂ V, Integrable (fun y => φ (G y)) μ := by
    intro φ
    have hle : Submodule.span ℂ (Set.range ev) ≤ P := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact hint x
    exact hle (hspan ▸ Submodule.mem_top)
  let b := Module.finBasis ℂ V
  let E := b.equivFun
  have hEi : Integrable (fun y => E (G y)) μ := by
    rw [integrable_pi_iff]
    intro j
    simpa [E] using hP (b.coord j)
  set c := ∫ y, E (G y) ∂μ
  have key : ∀ x, ∫ y, Fm y x ∂μ = ((E.symm c : V) : X → ℂ) x := by
    intro x
    let ℓ : (Fin (Module.finrank ℂ V) → ℂ) →L[ℂ] ℂ :=
      LinearMap.toContinuousLinearMap ((ev x).comp E.symm.toLinearMap)
    have h1 := ℓ.integral_comp_comm hEi
    have h2 : ∀ y, ℓ (E (G y)) = Fm y x := by intro y; simp [ℓ, hev, G]
    simp only [h2] at h1
    rw [h1]
    rfl
  have : (fun x => ∫ y, Fm y x ∂μ) = ((E.symm c : V) : X → ℂ) := funext key
  rw [this]
  exact (E.symm c).2

/- English proof (translation)
The claim follows from `@integral_mem_of_finiteDimensional_fun`.
-/
example : ∀ {X Y : Type} [MeasurableSpace Y] (μ : Measure Y) (V : Submodule ℂ (X → ℂ)), FiniteDimensional ℂ V →
  ∀ Fm : Y → X → ℂ, (∀ y, Fm y ∈ V) → (∀ x, Integrable (fun y => Fm y x) μ) → (fun x => ∫ y, Fm y x ∂μ) ∈ V :=
  @integral_mem_of_finiteDimensional_fun

end GlobalTheory
