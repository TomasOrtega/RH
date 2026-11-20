import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WtRInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHighestWeightInInvariantSubmoduleStatement
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.RealCountG

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hKtop : LinearMap.ker R ≠ ⊤` using `fun h => hne (LinearMap.ker_eq_top.mp h)`. Establish `hN : (LinearMap.ker R)ᗮ ≠ ⊥` using `fun h => hKtop ((Submodule.orthogonal_eq_bot_iff).mp h)`. Establish `hstable : ∀ a b, ∀ w ∈ (LinearMap.ker R)ᗮ, G a b w ∈ (LinearMap.ker R)ᗮ`. Introduce `a b w hw`.

Rewrite using `[Submodule.mem_orthogonal]`. Introduce `u hu`. Establish `hu' : G b a u ∈ LinearMap.ker R`. Rewrite `hu`, the goal using `[LinearMap.mem_ker]`. Rewrite using `[hR, hu, map_zero]`.

Rewrite using `[← hadj]`. Conclude with `(Submodule.mem_orthogonal _ _).mp hw _ hu'`. Take `⟨μ, v, hvN, hv0, hk⟩` from `GlobalTheory.T.exists_highest_weight_in_invariant_submodule H G hrel hadj _ hN hstable`. Establish `hvK : v ∈ LinearMap.ker R` using `hhigh μ v hk`. Conclude with `hv0 (inner_self_eq_zero.mp ((Submodule.mem_orthogonal _ _).mp hvN v hvK))`.
-/
theorem intertwiner_eq_zero_of_highest {n : ℕ} (H V : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [AddCommGroup V] [Module ℂ V]
    (G : Fin n → Fin n → Module.End ℂ H) (D : Fin n → Fin n → Module.End ℂ V)
    (hrel : Formalism.REAL.GlRel G)
    (hadj : ∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ)
    (R : H →ₗ[ℂ] V) (hR : ∀ a b w, R (G a b w) = D a b (R w))
    (hhigh : ∀ (μ : Fin n → ℝ) (v : H), Formalism.REAL.KHighest (fun _ => true) G μ v → R v = 0) :
    R = 0 := by
  by_contra hne
  have hKtop : LinearMap.ker R ≠ ⊤ := fun h => hne (LinearMap.ker_eq_top.mp h)
  have hN : (LinearMap.ker R)ᗮ ≠ ⊥ := fun h =>
    hKtop ((Submodule.orthogonal_eq_bot_iff).mp h)
  have hstable : ∀ a b, ∀ w ∈ (LinearMap.ker R)ᗮ, G a b w ∈ (LinearMap.ker R)ᗮ := by
    intro a b w hw
    rw [Submodule.mem_orthogonal]
    intro u hu
    have hu' : G b a u ∈ LinearMap.ker R := by
      rw [LinearMap.mem_ker] at hu ⊢
      rw [hR, hu, map_zero]
    rw [← hadj]
    exact (Submodule.mem_orthogonal _ _).mp hw _ hu'
  obtain ⟨μ, v, hvN, hv0, hk⟩ := GlobalTheory.T.exists_highest_weight_in_invariant_submodule H G hrel hadj _ hN hstable
  have hvK : v ∈ LinearMap.ker R := hhigh μ v hk
  exact hv0 (inner_self_eq_zero.mp ((Submodule.mem_orthogonal _ _).mp hvN v hvK))

end GlobalTheory.CompanionTheory.RealCountG
