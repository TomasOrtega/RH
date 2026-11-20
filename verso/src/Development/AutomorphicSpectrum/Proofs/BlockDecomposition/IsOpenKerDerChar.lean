import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteSupport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentFiniteSetCompactSubgroupStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

namespace GlobalTheory.CompanionTheory.PRep.DerExact

/- English proof (translation)
Take `⟨s, hs⟩` from `GlobalTheory.SplitWeil.exists_cball_addChar_eq_one ψ hψ`. Set `F : derUnip k N n → k` to `fun u => ∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1 ∧ n ≤ (p.1 : ℕ), (u : GL (Fin N) k).val p.1 p.2`. Establish `hF : Continuous F`. Use `continuous_finsetSum _ fun p _ => ?_` and prove the remaining obligations. Establish `h1 : Continuous fun u : derUnip k N n => ((u : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)` using `Units.continuous_val.comp continuous_subtype_val`.

Conclude with `(continuous_apply p.2).comp ((continuous_apply p.1).comp h1)`. Establish `hsub : F ⁻¹' GlobalTheory.SplitWeil.cball s ⊆ ((derChar k ψ N n).ker : Set (derUnip k N n))`. Introduce `u hu`. Simplify using `only [SetLike.mem_coe, MonoidHom.mem_ker]`. Use `show Circle.toUnits (ψ (F u)) = 1`.

Rewrite using `[hs _ hu, map_one]`. Establish `h1 : F 1 = 0`. Use `Finset.sum_eq_zero fun p hp => ?_` and prove the remaining obligations. Use `show ((1 : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) p.1 p.2 = 0`. Rewrite using `[Units.val_one]`.

Conclude with `Matrix.one_apply_ne fun e => by`. Use `(Finset.mem_filter.1 hp).2.1` as an intermediate fact. Rewrite `this` using `[e]`. Use linear arithmetic over natural numbers and integers. Establish `hmem : F ⁻¹' GlobalTheory.SplitWeil.cball s ∈ nhds (1 : derUnip k N n)` using `hF.continuousAt.preimage_mem_nhds (by rw [h1]; exact GlobalTheory.SplitWeil.cball_mem_nhds s)`.

Conclude with `Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset hmem hsub)`.
-/
theorem isOpen_ker_derChar (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (hψ : Continuous ψ) (N n : ℕ) :
    IsOpen ((derChar k ψ N n).ker : Set (derUnip k N n)) := by
  classical
  obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_addChar_eq_one ψ hψ
  let F : derUnip k N n → k := fun u => ∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1 ∧ n ≤ (p.1 : ℕ),
    (u : GL (Fin N) k).val p.1 p.2
  have hF : Continuous F := by
    refine continuous_finsetSum _ fun p _ => ?_
    have h1 : Continuous fun u : derUnip k N n => ((u : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) :=
      Units.continuous_val.comp continuous_subtype_val
    exact (continuous_apply p.2).comp ((continuous_apply p.1).comp h1)
  have hsub : F ⁻¹' GlobalTheory.SplitWeil.cball s ⊆ ((derChar k ψ N n).ker : Set (derUnip k N n)) := by
    intro u hu
    simp only [SetLike.mem_coe, MonoidHom.mem_ker]
    show Circle.toUnits (ψ (F u)) = 1
    rw [hs _ hu, map_one]
  have h1 : F 1 = 0 := by
    refine Finset.sum_eq_zero fun p hp => ?_
    show ((1 : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) p.1 p.2 = 0
    rw [Units.val_one]
    exact Matrix.one_apply_ne fun e => by
      have := (Finset.mem_filter.1 hp).2.1; rw [e] at this; omega
  have hmem : F ⁻¹' GlobalTheory.SplitWeil.cball s ∈ nhds (1 : derUnip k N n) :=
    hF.continuousAt.preimage_mem_nhds (by rw [h1]; exact GlobalTheory.SplitWeil.cball_mem_nhds s)
  exact Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset hmem hsub)

end GlobalTheory.CompanionTheory.PRep.DerExact
