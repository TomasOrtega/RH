import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntEasy
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntPull

noncomputable section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.MomPull

variable {D : D7} {N N' : ℕ}

def tPullL (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) : VC D N N' →ₗ[ℂ] VC D N N' where
  toFun := Formalism.L2.KerInert.tPull D (tor0 D cc δ) γ γ'
  map_add' := Formalism.L2.KerInert.ie_tPull_add cc δ γ γ'
  map_smul' := Formalism.L2.KerInert.ie_tPull_smul cc δ γ γ'

/- English proof (translation)
Use `letI := D.host.cmStar`. Unfold `Hf`. Use `congr 1`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Establish `h1` using `Formalism.L2.KerInert.PullbackComparison.map_mul_star D (embT D τ) γ hγ`.

Establish `h2` using `Formalism.L2.KerInert.PullbackComparison.map_mul_star D (embT D τ) γ' hγ'`. Rewrite `h1`, `h2` using `[Matrix.star_eq_conjTranspose]`. Conclude with `Formalism.L2.KerInert.PullbackComparison.sum_mul_star_conj (γ.map (embT D τ)) (γ'.map (embT D τ)) h1 h2 (Matrix.of (z τ)) (Matrix.of (w τ))`.
-/
theorem hf_tPull (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) (hγ : (letI := D.host.cmStar; γ * star γ) = 1)
    (hγ' : (letI := D.host.cmStar; γ' * star γ') = 1) (z w : VC D N N') :
    Hf D (tor0 D cc δ) (Formalism.L2.KerInert.tPull D (tor0 D cc δ) γ γ' z)
      (Formalism.L2.KerInert.tPull D (tor0 D cc δ) γ γ' w) = Hf D (tor0 D cc δ) z w := by
  letI := D.host.cmStar
  unfold Hf
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h1 := Formalism.L2.KerInert.PullbackComparison.map_mul_star D (embT D τ) γ hγ
  have h2 := Formalism.L2.KerInert.PullbackComparison.map_mul_star D (embT D τ) γ' hγ'
  rw [Matrix.star_eq_conjTranspose] at h1 h2
  exact Formalism.L2.KerInert.PullbackComparison.sum_mul_star_conj (γ.map (embT D τ)) (γ'.map (embT D τ)) h1 h2
    (Matrix.of (z τ)) (Matrix.of (w τ))

end GlobalTheory.MomPull

open GlobalTheory.MomPull in

/- English proof (translation)
Introduce `D cc δ N N'`. Use `letI := D.host.cmStar`. Introduce `γ γ' M M'`. Establish `h1' : star (γ' : Matrix (Fin N') (Fin N') D.host.E) * γ' = 1` using `Matrix.mem_unitaryGroup_iff'.mp γ'.2`. Establish `hγ : (γ : Matrix (Fin N) (Fin N) D.host.E) * star (γ : Matrix (Fin N) (Fin N) D.host.E) = 1` using `Matrix.mem_unitaryGroup_iff.mp γ.2`.

Establish `hγ' : (γ' : Matrix (Fin N') (Fin N') D.host.E) * star (γ' : Matrix (Fin N') (Fin N') D.host.E) = 1` using `Matrix.mem_unitaryGroup_iff.mp γ'.2`. Use `⟨LinearMap.toContinuousLinearMap (tPullL cc δ (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)), fun x hx => ?_, fun t G => ?_⟩` and prove the remaining obligations. Establish `h` using `Formalism.L2.KerInert.ie_La_pull cc δ _ _ h1' M M' hx`. Conclude with `h`. Use function extensionality and compare the values at `z show G (Formalism.L2.KerInert.tPull D (tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) (z + t)) * _ = G (Formalism.L2.KerInert.tPull D (tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) z + Fo …`.

Establish `e : ∀ y, (LinearMap.toContinuousLinearMap (tPullL cc δ (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E))) y = Formalism.L2.KerInert.tPull D (tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) y` using `fun _ => rfl`. Simplify using `only [e]`. Rewrite using `[hf_tPull cc δ _ _ hγ hγ', hf_tPull cc δ _ _ hγ hγ', Formalism.L2.KerInert.ie_tPull_add]`.
-/
theorem GlobalTheory.MomPull.pull_unitary : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ), letI := D.host.cmStar; ∀ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E) (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), ∃ g : VC D N N' →L[ℂ] VC D N N', (∀ x ∈ La D (tor0 D cc δ) (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M) (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M'), g x ∈ La D (tor0 D cc δ) M M') ∧ ∀ (t : VC D N N') (G : VC D N N' → ℂ), U D (tor0 D cc δ) t (pull D (tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) G) = fun z => U D (tor0 D cc δ) (g t) G (g z) := by
  intro D cc δ N N'
  letI := D.host.cmStar
  intro γ γ' M M'
  have h1' : star (γ' : Matrix (Fin N') (Fin N') D.host.E) * γ' = 1 := Matrix.mem_unitaryGroup_iff'.mp γ'.2
  have hγ : (γ : Matrix (Fin N) (Fin N) D.host.E) * star (γ : Matrix (Fin N) (Fin N) D.host.E) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp γ.2
  have hγ' : (γ' : Matrix (Fin N') (Fin N') D.host.E) * star (γ' : Matrix (Fin N') (Fin N') D.host.E) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp γ'.2
  refine ⟨LinearMap.toContinuousLinearMap (tPullL cc δ (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E)), fun x hx => ?_, fun t G => ?_⟩
  · have h := Formalism.L2.KerInert.ie_La_pull cc δ _ _ h1' M M' hx
    exact h
  · funext z
    show G (Formalism.L2.KerInert.tPull D (tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E)
        (γ' : Matrix (Fin N') (Fin N') D.host.E) (z + t)) * _ =
      G (Formalism.L2.KerInert.tPull D (tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E)
        (γ' : Matrix (Fin N') (Fin N') D.host.E) z + Formalism.L2.KerInert.tPull D (tor0 D cc δ)
        (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) t) * _
    have e : ∀ y, (LinearMap.toContinuousLinearMap (tPullL cc δ (γ : Matrix (Fin N) (Fin N) D.host.E)
        (γ' : Matrix (Fin N') (Fin N') D.host.E))) y = Formalism.L2.KerInert.tPull D (tor0 D cc δ)
        (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) y := fun _ => rfl
    simp only [e]
    rw [hf_tPull cc δ _ _ hγ hγ', hf_tPull cc δ _ _ hγ hγ', Formalism.L2.KerInert.ie_tPull_add]
