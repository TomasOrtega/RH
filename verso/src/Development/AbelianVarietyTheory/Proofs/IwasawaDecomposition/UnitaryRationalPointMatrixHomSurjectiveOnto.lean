import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.AlgWtF

/- English proof (translation)
Simplify using `[conjAL, Algebra.TensorProduct.map_tmul]`.
-/
theorem conjAL_includeLeft {L : Type} [Field L] [NumberField L] [IsCMField L] (x : L) :
    conjAL L ((Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) x) =
      (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) ((IsCMField.complexConj L : L →+* L) x) := by
  simp [conjAL, Algebra.TensorProduct.map_tmul]

/- English proof (translation)
Establish `h0 : (γ₀ : Matrix (Fin n) (Fin n) L) * conjT (IsCMField.complexConj L : L →+* L) γ₀ = 1` using `h`. Use `show ((incGL γ₀ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) * conjT (conjAL L) (incGL γ₀) = 1`. Establish `hc : conjT (conjAL L) ((incGL γ₀ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = (conjT (IsCMField.complexConj L : L →+* L) (γ₀ : Matrix (Fin n) (Fin n) L)).map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L)`. Use extensionality with `i j`. Simplify using `only [conjT, Matrix.transpose_apply, Matrix.map_apply, incGL, Matrix.GeneralLinearGroup.map_apply]`.

Conclude with `conjAL_includeLeft _`. Rewrite using `[hc]`. Establish `e : ((incGL γ₀ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L)` using `rfl`. Rewrite using `[e, ← Matrix.map_mul, h0, Matrix.map_one _ (map_zero _) (map_one _)]`.
-/
theorem incGL_mem_GA {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (γ₀ : GL (Fin n) L)
    (h : γ₀ ∈ GQ0 L n) : incGL γ₀ ∈ GA L n := by
  have h0 : (γ₀ : Matrix (Fin n) (Fin n) L) * conjT (IsCMField.complexConj L : L →+* L) γ₀ = 1 := h
  show ((incGL γ₀ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) * conjT (conjAL L) (incGL γ₀) = 1
  have hc : conjT (conjAL L) ((incGL γ₀ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      (conjT (IsCMField.complexConj L : L →+* L) (γ₀ : Matrix (Fin n) (Fin n) L)).map
        (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) := by
    ext i j
    simp only [conjT, Matrix.transpose_apply, Matrix.map_apply, incGL,
      Matrix.GeneralLinearGroup.map_apply]
    exact conjAL_includeLeft _
  rw [hc]
  have e : ((incGL γ₀ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) := rfl
  rw [e, ← Matrix.map_mul, h0, Matrix.map_one _ (map_zero _) (map_one _)]

/- English proof (translation)
Introduce `L _ _ _ n γ₀ h`. Set `g : GA L n` to `⟨incGL γ₀, incGL_mem_GA γ₀ h⟩`. Establish `hg : g ∈ GQ L n` using `Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨γ₀, h, rfl⟩)`. Use `⟨⟨g, hg⟩, ?_⟩` and prove the remaining obligations. Apply `incGL_injective` to reduce the goal to its premises.

Conclude with `incGL_ratFun (L := L) (n := n) ⟨g, hg⟩`.
-/
theorem ratHom_surjective : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (γ₀ : GL (Fin n) L),
    γ₀ ∈ GQ0 L n → ∃ γ : GQ L n, GlobalTheory.AlgWtF.ratHom γ = γ₀ := by
  intro L _ _ _ n γ₀ h
  let g : GA L n := ⟨incGL γ₀, incGL_mem_GA γ₀ h⟩
  have hg : g ∈ GQ L n := Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨γ₀, h, rfl⟩)
  refine ⟨⟨g, hg⟩, ?_⟩
  apply incGL_injective
  exact incGL_ratFun (L := L) (n := n) ⟨g, hg⟩

end GlobalTheory.AlgWtF
