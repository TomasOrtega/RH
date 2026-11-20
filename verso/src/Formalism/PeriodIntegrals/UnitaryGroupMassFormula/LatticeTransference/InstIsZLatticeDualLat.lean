import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.DualTransport
import Formalism.LatticeTheta.ThetaShiftInversion

open Module

noncomputable section

namespace PI.Tr

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- English proof (translation)
Use extensionality with `y`. Rewrite using `[LinearMap.BilinForm.mem_dualSubmodule]`. Use `show (∀ x ∈ Λ, ∃ n : ℤ, inner ℝ x y = (n : ℝ)) ↔ _`. Use `forall₂_congr fun x _ => ?_` and prove the remaining obligations. Rewrite using `[innerₗ_apply_apply, real_inner_comm, Submodule.mem_one]`.

Simplify using `only [algebraMap_int_eq, eq_intCast]`. Conclude with `⟨fun ⟨n, hn⟩ => ⟨n, hn.symm⟩, fun ⟨n, hn⟩ => ⟨n, hn.symm⟩⟩`.
-/
theorem dualLat_eq (Λ : Submodule ℤ E) :
    dualLat Λ = LinearMap.BilinForm.dualSubmodule (innerₗ E) Λ := by
  ext y
  rw [LinearMap.BilinForm.mem_dualSubmodule]
  show (∀ x ∈ Λ, ∃ n : ℤ, inner ℝ x y = (n : ℝ)) ↔ _
  refine forall₂_congr fun x _ => ?_
  rw [innerₗ_apply_apply, real_inner_comm, Submodule.mem_one]
  simp only [algebraMap_int_eq, eq_intCast]
  exact ⟨fun ⟨n, hn⟩ => ⟨n, hn.symm⟩, fun ⟨n, hn⟩ => ⟨n, hn.symm⟩⟩

/- English proof (translation)
Use extensionality with `x`. Use `show (∀ y ∈ M, ∃ z : ℤ, inner ℝ x y = (z : ℝ)) ↔ (∀ y ∈ M, ∃ n : ℤ, inner ℝ y x = (n : ℝ))`. Simplify using `only [real_inner_comm]`.
-/
theorem dualZ_eq_dualLat {N : ℕ} (M : Submodule ℤ (EuclideanSpace ℝ (Fin N))) :
    PI.dualZ M = dualLat M := by
  ext x
  show (∀ y ∈ M, ∃ z : ℤ, inner ℝ x y = (z : ℝ)) ↔ (∀ y ∈ M, ∃ n : ℤ, inner ℝ y x = (n : ℝ))
  simp only [real_inner_comm]

/- English proof (translation)
Introduce `x hx`. Use `show ∀ y ∈ dualLat Λ, ∃ n : ℤ, inner ℝ y x = (n : ℝ)`. Introduce `y hy`. Establish `hy' : ∀ z ∈ Λ, ∃ n : ℤ, inner ℝ z y = (n : ℝ)` using `hy`. Take `⟨n, hn⟩` from `hy' x hx`.

Conclude with `⟨n, by rw [real_inner_comm]; exact hn⟩`.
-/
theorem le_dualLat_dualLat (Λ : Submodule ℤ E) : Λ ≤ dualLat (dualLat Λ) := by
  intro x hx
  show ∀ y ∈ dualLat Λ, ∃ n : ℤ, inner ℝ y x = (n : ℝ)
  intro y hy
  have hy' : ∀ z ∈ Λ, ∃ n : ℤ, inner ℝ z y = (n : ℝ) := hy
  obtain ⟨n, hn⟩ := hy' x hx
  exact ⟨n, by rw [real_inner_comm]; exact hn⟩

/- English proof (translation)
Introduce `_ hy x hx` and use `(show ∀ z ∈ Λ₂, ∃ n : ℤ, inner ℝ z _ = (n : ℝ) from hy) x (h hx)`.
-/
theorem dualLat_anti {Λ₁ Λ₂ : Submodule ℤ E} (h : Λ₁ ≤ Λ₂) : dualLat Λ₂ ≤ dualLat Λ₁ :=
  fun _ hy x hx => (show ∀ z ∈ Λ₂, ∃ n : ℤ, inner ℝ z _ = (n : ℝ) from hy) x (h hx)

section lattice

variable [FiniteDimensional ℝ E] (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

instance instDiscreteDualLat : DiscreteTopology (dualLat Λ) := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  rw [dualLat_eq]
  exact (Formalism.H.dualIsLattice E Λ).1

instance instIsZLatticeDualLat : IsZLattice ℝ (dualLat Λ) := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  have h := Formalism.H.dualIsLattice E Λ
  haveI := h.1
  have h2 : IsZLattice ℝ (Formalism.H.dual Λ) := h.2
  constructor
  rw [dualLat_eq]
  exact h2.span_top

/- English proof (translation)
Set `b` to `(Module.Free.chooseBasis ℤ Λ).ofZLatticeBasis ℝ Λ`. Establish `hspan : Submodule.span ℤ (Set.range b) = Λ` using `Module.Basis.ofZLatticeBasis_span ℝ Λ _`. Establish `hnd : LinearMap.BilinForm.Nondegenerate (innerₗ E)`. Rewrite using `[LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `m hm`.

Establish `h0` using `congrArg (fun f => f m) hm`. Simplify using `only [innerₗ_apply_apply, LinearMap.zero_apply] at h0`. Conclude with `inner_self_eq_zero.1 h0`. Establish `hsym : LinearMap.BilinForm.IsSymm (innerₗ E)` using `LinearMap.BilinForm.isSymm_def.2 fun x y => by simp [innerₗ_apply_apply, real_inner_comm]`. Rewrite using `[dualLat_eq, dualLat_eq, ← hspan, LinearMap.BilinForm.dualSubmodule_dualSubmodule_of_basis _ hnd hsym]`.
-/
theorem dualLat_dualLat : dualLat (dualLat Λ) = Λ := by
  classical
  let b := (Module.Free.chooseBasis ℤ Λ).ofZLatticeBasis ℝ Λ
  have hspan : Submodule.span ℤ (Set.range b) = Λ := Module.Basis.ofZLatticeBasis_span ℝ Λ _
  have hnd : LinearMap.BilinForm.Nondegenerate (innerₗ E) := by
    rw [LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    have h0 := congrArg (fun f => f m) hm
    simp only [innerₗ_apply_apply, LinearMap.zero_apply] at h0
    exact inner_self_eq_zero.1 h0
  have hsym : LinearMap.BilinForm.IsSymm (innerₗ E) :=
    LinearMap.BilinForm.isSymm_def.2 fun x y => by simp [innerₗ_apply_apply, real_inner_comm]
  rw [dualLat_eq, dualLat_eq, ← hspan,
    LinearMap.BilinForm.dualSubmodule_dualSubmodule_of_basis _ hnd hsym]

end lattice

end PI.Tr
