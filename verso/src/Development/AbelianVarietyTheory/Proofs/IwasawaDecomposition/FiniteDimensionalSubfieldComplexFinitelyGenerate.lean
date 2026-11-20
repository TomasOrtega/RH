import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `M hM`. Set `b` to `Module.finBasis ℚ M`. Use `⟨Finset.univ.image (fun i => ((b i : M) : ℂ)), ?_, ?_⟩` and prove the remaining obligations. Introduce `z hz`. Take `⟨i, -, rfl⟩` from `Finset.mem_image.mp hz`.

Establish `: IsIntegral ℚ (b i)` using `Algebra.IsIntegral.isIntegral _`. Conclude with `(this.map M.val).isAlgebraic`. Introduce `Lf hS x hx`. Establish `hb : ∀ i, ((b i : M) : ℂ) ∈ Lf` using `fun i => hS (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))`. Establish `hx' : (⟨x, hx⟩ : M) = ∑ i, (b.repr ⟨x, hx⟩ i) • b i` using `(b.sum_repr _).symm`.

Establish `: x = ((∑ i, (b.repr ⟨x, hx⟩ i) • b i : M) : ℂ)` using `by rw [← hx']`. Rewrite using `[this, IntermediateField.coe_sum]`. Simplify using `only [IntermediateField.coe_smul]`. Conclude with `Lf.sum_mem fun i _ => Lf.smul_mem (hb i)`.
-/
theorem GlobalTheory.finDimSubfield_finGen : ∀ (M : IntermediateField ℚ ℂ), FiniteDimensional ℚ M → ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧ ∀ Lf : IntermediateField ℚ ℂ, (↑S : Set ℂ) ⊆ Lf → M ≤ Lf := by
  intro M hM
  classical
  let b := Module.finBasis ℚ M
  refine ⟨Finset.univ.image (fun i => ((b i : M) : ℂ)), ?_, ?_⟩
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    have : IsIntegral ℚ (b i) := Algebra.IsIntegral.isIntegral _
    exact (this.map M.val).isAlgebraic
  · intro Lf hS x hx
    have hb : ∀ i, ((b i : M) : ℂ) ∈ Lf := fun i =>
      hS (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
    have hx' : (⟨x, hx⟩ : M) = ∑ i, (b.repr ⟨x, hx⟩ i) • b i := (b.sum_repr _).symm
    have : x = ((∑ i, (b.repr ⟨x, hx⟩ i) • b i : M) : ℂ) := by rw [← hx']
    rw [this, IntermediateField.coe_sum]
    simp only [IntermediateField.coe_smul]
    exact Lf.sum_mem fun i _ => Lf.smul_mem (hb i)
