import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DiscreteSpectrumResidual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

namespace GlobalTheory.LieFin

/- English proof (translation)
Introduce `E _ _ _ N X φ hφ`. Set `S : Submodule ℂ (Sm E N)` to `Submodule.span ℂ (Set.range fun k => cptRep E N k φ)`. Use `haveI : FiniteDimensional ℂ S := hφ`. Set `b` to `Module.finBasis ℝ (Lie E N)`. Set `T : Submodule ℂ (Sm E N)` to `⨆ s, S.map (lie E N (b s))`.

Use `haveI : FiniteDimensional ℂ T := by haveI : ∀ s, FiniteDimensional ℂ (S.map (lie E N (b s))) := fun s => inferInstance`. Conclude with `Submodule.finiteDimensional_iSup _`. Establish `key : ∀ (Z : Lie E N) (ψ : Sm E N), ψ ∈ S → lie E N Z ψ ∈ T`. Introduce `Z ψ hψ`. Rewrite using `[← b.sum_repr Z, map_sum, LinearMap.sum_apply]`.

Use `Submodule.sum_mem _ fun s _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, LinearMap.smul_apply]`. Establish `h1 : lie E N (b s) ψ ∈ T` using `(le_iSup (fun s => S.map (lie E N (b s))) s) (Submodule.mem_map_of_mem hψ)`. Establish `h2 : ((b.repr Z s : ℝ) : ℂ) • lie E N (b s) ψ ∈ T` using `T.smul_mem _ h1`. Simplify `h2` using `[Complex.coe_smul]`.

Use `show FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E N k (lie E N X φ)))`. Use `Submodule.finiteDimensional_of_le (S₂ := T) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Establish `e` using `congrArg (fun f : Module.End ℂ (Sm E N) => f φ) (GlobalTheory.CapAdInv.rt_lie (Unitary.toUnits k) (Matrix.of X))`. Simplify using `only [Module.End.mul_apply] at e`.

Express the relevant statement in the definitionally equal form `rt E N (infGL E N (Unitary.toUnits k)) (lie E N X φ) ∈ T`. Establish `eX : toL (Matrix.of X) = X` using `rfl`. Rewrite `e` using `[eX]`. Rewrite using `[e]`. Conclude with `key _ _ (Submodule.subset_span ⟨k, rfl⟩)`.
-/
theorem lie_mem_finVec : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ} (X : Lie E N) (φ : Sm E N),
    φ ∈ finVec (cptRep E N) → lie E N X φ ∈ finVec (cptRep E N) := by
  intro E _ _ _ N X φ hφ
  let S : Submodule ℂ (Sm E N) := Submodule.span ℂ (Set.range fun k => cptRep E N k φ)
  haveI : FiniteDimensional ℂ S := hφ
  let b := Module.finBasis ℝ (Lie E N)
  let T : Submodule ℂ (Sm E N) := ⨆ s, S.map (lie E N (b s))
  haveI : FiniteDimensional ℂ T := by
    haveI : ∀ s, FiniteDimensional ℂ (S.map (lie E N (b s))) := fun s => inferInstance
    exact Submodule.finiteDimensional_iSup _
  have key : ∀ (Z : Lie E N) (ψ : Sm E N), ψ ∈ S → lie E N Z ψ ∈ T := by
    intro Z ψ hψ
    rw [← b.sum_repr Z, map_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun s _ => ?_
    rw [map_smul, LinearMap.smul_apply]
    have h1 : lie E N (b s) ψ ∈ T :=
      (le_iSup (fun s => S.map (lie E N (b s))) s) (Submodule.mem_map_of_mem hψ)
    have h2 : ((b.repr Z s : ℝ) : ℂ) • lie E N (b s) ψ ∈ T := T.smul_mem _ h1
    simpa [Complex.coe_smul] using h2
  show FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E N k (lie E N X φ)))
  refine Submodule.finiteDimensional_of_le (S₂ := T) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  have e := congrArg (fun f : Module.End ℂ (Sm E N) => f φ) (GlobalTheory.CapAdInv.rt_lie (Unitary.toUnits k) (Matrix.of X))
  simp only [Module.End.mul_apply] at e
  change rt E N (infGL E N (Unitary.toUnits k)) (lie E N X φ) ∈ T
  have eX : toL (Matrix.of X) = X := rfl
  rw [eX] at e
  rw [e]
  exact key _ _ (Submodule.subset_span ⟨k, rfl⟩)

end GlobalTheory.LieFin
