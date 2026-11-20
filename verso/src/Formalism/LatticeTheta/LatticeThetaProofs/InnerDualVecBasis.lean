import Formalism.LatticeTheta.LatticeSummableDecay

open MeasureTheory Filter Complex
open scoped RealInnerProductSpace

noncomputable section

namespace Formalism.H

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem innerₗ_nondegenerate : (innerₗ V : LinearMap.BilinForm ℝ V).Nondegenerate := by
  constructor <;> intro m hm <;> simpa using hm m

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev dualB (e : Module.Basis ι ℝ V) : Module.Basis ι ℝ V :=
  LinearMap.BilinForm.dualBasis (innerₗ V) innerₗ_nondegenerate e

/- English proof (translation)
Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem inner_dualB (e : Module.Basis ι ℝ V) (i j : ι) :
    ⟪dualB e i, e j⟫ = if j = i then 1 else 0 := by
  have h := LinearMap.BilinForm.apply_dualBasis_left (innerₗ_nondegenerate (V := V)) e i j
  simpa using h

def dualVec (e : Module.Basis ι ℝ V) (m : ι → ℤ) : V := ∑ i, m i • dualB e i

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem dualVec_eq (e : Module.Basis ι ℝ V) (m : ι → ℤ) :
    dualVec e m = ∑ i, (m i : ℝ) • dualB e i := by
  unfold dualVec
  exact Finset.sum_congr rfl fun i _ => (Int.cast_smul_eq_zsmul ℝ (m i) _).symm

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem inner_dualVec_basis (e : Module.Basis ι ℝ V) (m : ι → ℤ) (j : ι) :
    ⟪dualVec e m, e j⟫ = m j := by
  rw [dualVec_eq, sum_inner]
  simp_rw [real_inner_smul_left, inner_dualB]
  simp

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dual_span_eq (e : Module.Basis ι ℝ V) :
    dual (Submodule.span ℤ (Set.range e)) = Submodule.span ℤ (Set.range (dualB e)) := by
  exact LinearMap.BilinForm.dualSubmodule_span_of_basis (innerₗ V) innerₗ_nondegenerate e

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem dualVec_mem (e : Module.Basis ι ℝ V) (m : ι → ℤ) :
    dualVec e m ∈ dual (Submodule.span ℤ (Set.range e)) := by
  rw [dual_span_eq]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem dualVec_injective (e : Module.Basis ι ℝ V) : Function.Injective (dualVec e) := by
  intro m n h
  funext j
  have h1 := congrArg (fun x => ⟪x, e j⟫) h
  simp only [inner_dualVec_basis] at h1
  exact_mod_cast h1

/- English proof (translation)
Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem dualVec_surjective (e : Module.Basis ι ℝ V) (μ : V)
    (hμ : μ ∈ dual (Submodule.span ℤ (Set.range e))) : ∃ m, dualVec e m = μ := by
  rw [dual_span_eq] at hμ
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hμ
  exact ⟨c, hc⟩

def dualEquiv (e : Module.Basis ι ℝ V) : (ι → ℤ) ≃ dual (Submodule.span ℤ (Set.range e)) :=
  Equiv.ofBijective (fun m => ⟨dualVec e m, dualVec_mem e m⟩)
    ⟨fun m n h => dualVec_injective e (congrArg Subtype.val h),
     fun μ => by
      obtain ⟨m, hm⟩ := dualVec_surjective e μ μ.2
      exact ⟨m, Subtype.ext hm⟩⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem dualEquiv_apply (e : Module.Basis ι ℝ V) (m : ι → ℤ) :
    ((dualEquiv e m : dual (Submodule.span ℤ (Set.range e))) : V) = dualVec e m := rfl

end Formalism.H
