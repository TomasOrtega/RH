import Formalism.LatticeTheta.LatticeSummableDecay

open MeasureTheory Filter Complex
open scoped RealInnerProductSpace

noncomputable section

namespace Formalism.H

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/- English proof (translation)
Apply the tactic sequence `constructor <;> intro m hm <;> simpa using hm m`.
-/
theorem innerₗ_nondegenerate : (innerₗ V : LinearMap.BilinForm ℝ V).Nondegenerate := by
  constructor <;> intro m hm <;> simpa using hm m

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev dualB (e : Module.Basis ι ℝ V) : Module.Basis ι ℝ V :=
  LinearMap.BilinForm.dualBasis (innerₗ V) innerₗ_nondegenerate e

/- English proof (translation)
Establish `h` using `LinearMap.BilinForm.apply_dualBasis_left (innerₗ_nondegenerate (V := V)) e i j`. Simplify using `using h`.
-/
theorem inner_dualB (e : Module.Basis ι ℝ V) (i j : ι) :
    ⟪dualB e i, e j⟫ = if j = i then 1 else 0 := by
  have h := LinearMap.BilinForm.apply_dualBasis_left (innerₗ_nondegenerate (V := V)) e i j
  simpa using h

def dualVec (e : Module.Basis ι ℝ V) (m : ι → ℤ) : V := ∑ i, m i • dualB e i

/- English proof (translation)
Unfold `dualVec`. Conclude with `Finset.sum_congr rfl fun i _ => (Int.cast_smul_eq_zsmul ℝ (m i) _).symm`.
-/
theorem dualVec_eq (e : Module.Basis ι ℝ V) (m : ι → ℤ) :
    dualVec e m = ∑ i, (m i : ℝ) • dualB e i := by
  unfold dualVec
  exact Finset.sum_congr rfl fun i _ => (Int.cast_smul_eq_zsmul ℝ (m i) _).symm

/- English proof (translation)
Rewrite using `[dualVec_eq, sum_inner]`. Repeatedly rewrite using `[real_inner_smul_left, inner_dualB]`. Simplify using the standard rewrite rules.
-/
theorem inner_dualVec_basis (e : Module.Basis ι ℝ V) (m : ι → ℤ) (j : ι) :
    ⟪dualVec e m, e j⟫ = m j := by
  rw [dualVec_eq, sum_inner]
  simp_rw [real_inner_smul_left, inner_dualB]
  simp

/- English proof (translation)
Conclude with `LinearMap.BilinForm.dualSubmodule_span_of_basis (innerₗ V) innerₗ_nondegenerate e`.
-/
theorem dual_span_eq (e : Module.Basis ι ℝ V) :
    dual (Submodule.span ℤ (Set.range e)) = Submodule.span ℤ (Set.range (dualB e)) := by
  exact LinearMap.BilinForm.dualSubmodule_span_of_basis (innerₗ V) innerₗ_nondegenerate e

/- English proof (translation)
Rewrite using `[dual_span_eq]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem dualVec_mem (e : Module.Basis ι ℝ V) (m : ι → ℤ) :
    dualVec e m ∈ dual (Submodule.span ℤ (Set.range e)) := by
  rw [dual_span_eq]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/- English proof (translation)
Introduce `m n h`. Use function extensionality and compare the values at `j`. Establish `h1` using `congrArg (fun x => ⟪x, e j⟫) h`. Simplify using `only [inner_dualVec_basis] at h1`. Conclude with `h1` after adjusting the coercions.
-/
theorem dualVec_injective (e : Module.Basis ι ℝ V) : Function.Injective (dualVec e) := by
  intro m n h
  funext j
  have h1 := congrArg (fun x => ⟪x, e j⟫) h
  simp only [inner_dualVec_basis] at h1
  exact_mod_cast h1

/- English proof (translation)
Rewrite `hμ` using `[dual_span_eq]`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ).mp hμ`. Conclude with `⟨c, hc⟩`.
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
