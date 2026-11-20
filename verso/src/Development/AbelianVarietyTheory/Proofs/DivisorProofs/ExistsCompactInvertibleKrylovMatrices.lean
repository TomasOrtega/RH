import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrylovApply
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LeviDesc.Krylov

/- English proof (translation)
Introduce `E _ _ w r Ω hΩ hcov`. Set `kr : (Fin r → w.adicCompletion E) → GLw r w → Matrix (Fin r) (Fin r) (w.adicCompletion E)` to `fun e y => GlobalTheory.LeviDesc.Krylov.krylov y.val e`. Establish `hkc : ∀ e, Continuous (kr e)`. Introduce `e`. Establish `hv : Continuous fun y : GLw r w => (y.val : Matrix (Fin r) (Fin r) (w.adicCompletion E))` using `Units.continuous_val`.

Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Simplify using `only [kr, GlobalTheory.LeviDesc.Krylov.krylov_apply]`. Conclude with `(continuous_apply i).comp ((hv.pow (j : ℕ)).matrix_mulVec continuous_const)`. Set `U : (Fin r → w.adicCompletion E) → Set (GLw r w)` to `fun e => {y | (kr e y).det ≠ 0}`. Establish `hU : ∀ e, IsOpen (U e)` using `fun e => isOpen_ne_fun ((hkc e).matrix_det) continuous_const`.

Establish `hsub : Ω ⊆ ⋃ e, U e`. Introduce `y hy`. Take `⟨e, he⟩` from `hcov y hy`. Conclude with `Set.mem_iUnion.2 ⟨e, he.ne_zero⟩`. Take `⟨t, ht⟩` from `hΩ.elim_finite_subcover U hU hsub`.

Take `⟨K, hKc, hKU, hΩK⟩` from `hΩ.finite_compact_cover t U (fun e _ => hU e) ht`. Establish `hunit : ∀ e, ∀ y : K e, IsUnit (kr e y.1)` using `fun e y => (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hKU e y.2))`. Set `f : ∀ e, K e → GLw r w` to `fun e y => (hunit e y).unit`. Establish `hf : ∀ e, Continuous (f e)`. Introduce `e`.

Rewrite using `[Units.continuous_iff]`. Prove the components needed by the constructor for the conclusion. Conclude with `(hkc e).comp continuous_subtype_val`. Establish `: (fun y : K e => ((f e y)⁻¹ : GLw r w).val) = fun y => (kr e y.1)⁻¹`. Use function extensionality and compare the values at `y`.

Rewrite using `[Matrix.coe_units_inv]`. Both sides reduce to the same expression. Rewrite using `[this]`. Simplify using `only [Matrix.inv_def, Ring.inverse_eq_inv']`. Conclude with `(((hkc e).comp continuous_subtype_val).matrix_det.inv₀ fun y => hKU e y.2).smul ((hkc e).comp continuous_subtype_val).matrix_adjugate`.

Use `⟨⋃ e ∈ t, Set.range (f e), t.isCompact_biUnion fun e _ => ?_, ?_⟩` and prove the remaining obligations. Use `haveI := isCompact_iff_compactSpace.1 (hKc e)`. Conclude with `isCompact_range (hf e)`. Introduce `y hy`. Rewrite `hy` using `[hΩK]`.

Simplify using `only [Set.mem_iUnion] at hy`. Take `⟨e, he, hyK⟩` from `hy`. Conclude with `⟨e, f e ⟨y, hyK⟩, Set.mem_biUnion he ⟨⟨y, hyK⟩, rfl⟩, rfl⟩`.
-/
theorem exists_isCompact_krylov_units : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (r : ℕ) (Ω : Set (GLw r w)), IsCompact Ω → (∀ y ∈ Ω, ∃ e, IsUnit (GlobalTheory.LeviDesc.Krylov.krylov y.val e).det) → ∃ C : Set (GLw r w), IsCompact C ∧ ∀ y ∈ Ω, ∃ e, ∃ c ∈ C, c.val = GlobalTheory.LeviDesc.Krylov.krylov y.val e := by
  intro E _ _ w r Ω hΩ hcov
  classical
  let kr : (Fin r → w.adicCompletion E) → GLw r w → Matrix (Fin r) (Fin r) (w.adicCompletion E) :=
    fun e y => GlobalTheory.LeviDesc.Krylov.krylov y.val e
  have hkc : ∀ e, Continuous (kr e) := by
    intro e
    have hv : Continuous fun y : GLw r w => (y.val : Matrix (Fin r) (Fin r) (w.adicCompletion E)) :=
      Units.continuous_val
    refine continuous_matrix fun i j => ?_
    simp only [kr, GlobalTheory.LeviDesc.Krylov.krylov_apply]
    exact (continuous_apply i).comp ((hv.pow (j : ℕ)).matrix_mulVec continuous_const)
  let U : (Fin r → w.adicCompletion E) → Set (GLw r w) := fun e => {y | (kr e y).det ≠ 0}
  have hU : ∀ e, IsOpen (U e) := fun e => isOpen_ne_fun ((hkc e).matrix_det) continuous_const
  have hsub : Ω ⊆ ⋃ e, U e := by
    intro y hy
    obtain ⟨e, he⟩ := hcov y hy
    exact Set.mem_iUnion.2 ⟨e, he.ne_zero⟩
  obtain ⟨t, ht⟩ := hΩ.elim_finite_subcover U hU hsub
  obtain ⟨K, hKc, hKU, hΩK⟩ := hΩ.finite_compact_cover t U (fun e _ => hU e) ht
  have hunit : ∀ e, ∀ y : K e, IsUnit (kr e y.1) := fun e y =>
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hKU e y.2))
  let f : ∀ e, K e → GLw r w := fun e y => (hunit e y).unit
  have hf : ∀ e, Continuous (f e) := by
    intro e
    rw [Units.continuous_iff]
    constructor
    · exact (hkc e).comp continuous_subtype_val
    · have : (fun y : K e => ((f e y)⁻¹ : GLw r w).val) = fun y => (kr e y.1)⁻¹ := by
        funext y
        rw [Matrix.coe_units_inv]
        rfl
      rw [this]
      simp only [Matrix.inv_def, Ring.inverse_eq_inv']
      exact (((hkc e).comp continuous_subtype_val).matrix_det.inv₀ fun y => hKU e y.2).smul
        ((hkc e).comp continuous_subtype_val).matrix_adjugate
  refine ⟨⋃ e ∈ t, Set.range (f e), t.isCompact_biUnion fun e _ => ?_, ?_⟩
  · haveI := isCompact_iff_compactSpace.1 (hKc e)
    exact isCompact_range (hf e)
  · intro y hy
    rw [hΩK] at hy
    simp only [Set.mem_iUnion] at hy
    obtain ⟨e, he, hyK⟩ := hy
    exact ⟨e, f e ⟨y, hyK⟩, Set.mem_biUnion he ⟨⟨y, hyK⟩, rfl⟩, rfl⟩

end GlobalTheory.LeviDesc.Krylov
