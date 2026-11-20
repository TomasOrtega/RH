import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantTopologyComparison.LinearIndependentOneBeta
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantTopologyComparison.CoordFin

noncomputable section

namespace PI.InvTopW

open NumberField IsDedekindDomain Matrix Topology Filter
open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge

variable (I : AutInst)

def finCoordL (j : Fin 2) : (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) →ₗ[I.F] Formalism.MainNotions.S.Af I.F :=
  (TensorProduct.lid I.F (Formalism.MainNotions.S.Af I.F)).toLinearMap ∘ₗ
    ((basisE I).coord j).rTensor (Formalism.MainNotions.S.Af I.F)

/- English proof (translation)
Use `set eb := NumberField.RingOfIntegers.basis I.E`. Take `⟨y, hy0, hy⟩` from `exists_integral_multiples ℤ ℚ ((Finset.univ : Finset (_ × Fin 2)).image (fun p => (basisE I).repr ((eb p.1 : 𝓞 I.E) : I.E) p.2))`. Use `⟨y.natAbs, Nat.one_le_iff_ne_zero.2 (Int.natAbs_ne_zero.2 hy0), ?_⟩` and prove the remaining obligations. Establish `hint : ∀ c : I.F, IsIntegral ℤ (y • c) → IsIntegral ℤ ((y.natAbs : I.F) * c)`. Introduce `c hc`.

Break down `Int.natAbs_eq y with h | h` into its components or cases. Establish `: ((y.natAbs : ℤ) : I.F) * c = y • c` using `by rw [← h, zsmul_eq_mul]`. Rewrite using `[← Int.cast_natCast, this]`. Conclude with `hc`. Establish `: ((y.natAbs : ℤ) : I.F) * c = -(y • c)`.

Rewrite using `[zsmul_eq_mul]`. Use `conv_rhs => rw [h]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← Int.cast_natCast, this]`.

Conclude with `hc.neg`. Establish `gen : ∀ i j, ∃ r : 𝓞 I.F, (y.natAbs : I.F) * (basisE I).repr ((eb i : 𝓞 I.E) : I.E) j = algebraMap (𝓞 I.F) I.F r`. Introduce `i j`. Establish `hm` using `hy _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))`. Conclude with `⟨⟨_, hint _ hm⟩, rfl⟩`.

Introduce `o`. Establish `ho : o ∈ Submodule.span ℤ (Set.range eb)` using `by rw [eb.span_eq]; exact Submodule.mem_top`. Proceed by induction on `ho using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨i, rfl⟩` from `hx`.

Conclude with `gen i`. Consider the case `zero`. Introduce `j`. Conclude with `⟨0, by simp⟩`. Consider the case `add x y' _ _ hx hy'`.

Introduce `j`. Take `⟨r, hr⟩` from `hx j`. Take `⟨r', hr'⟩` from `hy' j`. Use `⟨r + r', ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, ← hr, ← hr']`.

Use `push_cast`. Rewrite using `[map_add, Finsupp.add_apply, mul_add]`. Consider the case `smul a x _ hx`. Introduce `j`. Take `⟨r, hr⟩` from `hx j`.

Use `⟨a • r, ?_⟩` and prove the remaining obligations. Rewrite using `[map_zsmul, ← hr]`. Establish `e : ((a • x : 𝓞 I.E) : I.E) = a • (x : I.E)` using `by push_cast; rfl`. Rewrite using `[e, map_zsmul, Finsupp.smul_apply, zsmul_eq_mul, zsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_denom : ∃ D : ℕ, 1 ≤ D ∧ ∀ o : 𝓞 I.E, ∀ j : Fin 2,
    ∃ r : 𝓞 I.F, (D : I.F) * (basisE I).repr (o : I.E) j = algebraMap (𝓞 I.F) I.F r := by
  classical
  set eb := NumberField.RingOfIntegers.basis I.E
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    ((Finset.univ : Finset (_ × Fin 2)).image
      (fun p => (basisE I).repr ((eb p.1 : 𝓞 I.E) : I.E) p.2))
  refine ⟨y.natAbs, Nat.one_le_iff_ne_zero.2 (Int.natAbs_ne_zero.2 hy0), ?_⟩
  have hint : ∀ c : I.F, IsIntegral ℤ (y • c) → IsIntegral ℤ ((y.natAbs : I.F) * c) := by
    intro c hc
    rcases Int.natAbs_eq y with h | h
    · have : ((y.natAbs : ℤ) : I.F) * c = y • c := by rw [← h, zsmul_eq_mul]
      rw [← Int.cast_natCast, this]
      exact hc
    · have : ((y.natAbs : ℤ) : I.F) * c = -(y • c) := by
        rw [zsmul_eq_mul]
        conv_rhs => rw [h]
        push_cast
        ring
      rw [← Int.cast_natCast, this]
      exact hc.neg
  have gen : ∀ i j, ∃ r : 𝓞 I.F,
      (y.natAbs : I.F) * (basisE I).repr ((eb i : 𝓞 I.E) : I.E) j = algebraMap (𝓞 I.F) I.F r := by
    intro i j
    have hm := hy _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))
    exact ⟨⟨_, hint _ hm⟩, rfl⟩
  intro o
  have ho : o ∈ Submodule.span ℤ (Set.range eb) := by rw [eb.span_eq]; exact Submodule.mem_top
  induction ho using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact gen i
  | zero =>
    intro j
    exact ⟨0, by simp⟩
  | add x y' _ _ hx hy' =>
    intro j
    obtain ⟨r, hr⟩ := hx j
    obtain ⟨r', hr'⟩ := hy' j
    refine ⟨r + r', ?_⟩
    rw [map_add, ← hr, ← hr']
    push_cast
    rw [map_add, Finsupp.add_apply, mul_add]
  | smul a x _ hx =>
    intro j
    obtain ⟨r, hr⟩ := hx j
    refine ⟨a • r, ?_⟩
    rw [map_zsmul, ← hr]
    have e : ((a • x : 𝓞 I.E) : I.E) = a • (x : I.E) := by push_cast; rfl
    rw [e, map_zsmul, Finsupp.smul_apply, zsmul_eq_mul, zsmul_eq_mul]
    ring

def sumsInt : AddSubgroup (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) :=
  AddSubgroup.closure {x | ∃ o ∈ Formalism.UG.intOE I.E, ∃ a ∈ Formalism.UG.intAd I.F, x = o ⊗ₜ[I.F] a}

end PI.InvTopW
