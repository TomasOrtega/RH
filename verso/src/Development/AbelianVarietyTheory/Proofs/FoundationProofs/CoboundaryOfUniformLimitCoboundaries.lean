import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory

/- English proof (translation)
Take `⟨s₀, hs₀, hk⟩` from `hne`. Establish `hd : k s₀ - 1 ≠ 0` using `sub_ne_zero.mpr hk`. Establish `hdpos : 0 < ‖k s₀ - 1‖` using `norm_pos_iff.mpr hd`. Use `⟨f s₀ / (k s₀ - 1), fun s hs => ?_⟩` and prove the remaining obligations. Establish `hCpos : 0 < 1 + ‖k s - 1‖ / ‖k s₀ - 1‖` using `by positivity`.

Establish `key : ∀ ε : ℝ, 0 < ε → ‖f s - (k s * (f s₀ / (k s₀ - 1)) - f s₀ / (k s₀ - 1))‖ ≤ ε * (1 + ‖k s - 1‖ / ‖k s₀ - 1‖)`. Introduce `ε hε`. Take `⟨X, hX⟩` from `happ ε hε`. Establish `h0` using `hX s₀ hs₀`. Establish `e0 : f s₀ - (k s₀ * X - X) = (k s₀ - 1) * (f s₀ / (k s₀ - 1) - X)`.

Clear the denominators using the available nonvanishing facts. Rewrite `h0` using `[e0, norm_mul]`. Establish `hXX : ‖X - f s₀ / (k s₀ - 1)‖ ≤ ε / ‖k s₀ - 1‖`. Rewrite using `[norm_sub_rev, le_div_iff₀ hdpos, mul_comm]`. Conclude with `h0`.

Establish `e1 : f s - (k s * (f s₀ / (k s₀ - 1)) - f s₀ / (k s₀ - 1)) = (f s - (k s * X - X)) + (k s - 1) * (X - f s₀ / (k s₀ - 1))` using `by ring`. Combine the equalities or inequalities in the displayed calculation. Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Use `_ ≤ ε + ‖k s - 1‖ * (ε / ‖k s₀ - 1‖) := by gcongr`.

Conclude with `hX s hs`. Use `_ = ε * (1 + ‖k s - 1‖ / ‖k s₀ - 1‖) := by ring`. Establish `hz : ‖f s - (k s * (f s₀ / (k s₀ - 1)) - f s₀ / (k s₀ - 1))‖ ≤ 0`. Use `le_of_forall_pos_le_add fun ε hε => ?_` and prove the remaining obligations. Establish `h` using `key (ε / (1 + ‖k s - 1‖ / ‖k s₀ - 1‖)) (div_pos hε hCpos)`.

Rewrite `h` using `[div_mul_cancel₀ _ hCpos.ne']`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `sub_eq_zero.mp (norm_le_zero_iff.mp hz)`.
-/
theorem coboundary_closed_of_uniform_approx {𝕜 : Type} [NormedField 𝕜] {Γ : Type} (H : Set Γ)
    (k f : Γ → 𝕜) (hne : ∃ s ∈ H, k s ≠ 1)
    (happ : ∀ ε : ℝ, 0 < ε → ∃ X : 𝕜, ∀ s ∈ H, ‖f s - (k s * X - X)‖ ≤ ε) :
    ∃ X : 𝕜, ∀ s ∈ H, f s = k s * X - X := by
  obtain ⟨s₀, hs₀, hk⟩ := hne
  have hd : k s₀ - 1 ≠ 0 := sub_ne_zero.mpr hk
  have hdpos : 0 < ‖k s₀ - 1‖ := norm_pos_iff.mpr hd
  refine ⟨f s₀ / (k s₀ - 1), fun s hs => ?_⟩
  have hCpos : 0 < 1 + ‖k s - 1‖ / ‖k s₀ - 1‖ := by positivity
  have key : ∀ ε : ℝ, 0 < ε → ‖f s - (k s * (f s₀ / (k s₀ - 1)) - f s₀ / (k s₀ - 1))‖
      ≤ ε * (1 + ‖k s - 1‖ / ‖k s₀ - 1‖) := by
    intro ε hε
    obtain ⟨X, hX⟩ := happ ε hε
    have h0 := hX s₀ hs₀
    have e0 : f s₀ - (k s₀ * X - X) = (k s₀ - 1) * (f s₀ / (k s₀ - 1) - X) := by
      field_simp
    rw [e0, norm_mul] at h0
    have hXX : ‖X - f s₀ / (k s₀ - 1)‖ ≤ ε / ‖k s₀ - 1‖ := by
      rw [norm_sub_rev, le_div_iff₀ hdpos, mul_comm]; exact h0
    have e1 : f s - (k s * (f s₀ / (k s₀ - 1)) - f s₀ / (k s₀ - 1))
        = (f s - (k s * X - X)) + (k s - 1) * (X - f s₀ / (k s₀ - 1)) := by ring
    calc ‖f s - (k s * (f s₀ / (k s₀ - 1)) - f s₀ / (k s₀ - 1))‖
        = ‖(f s - (k s * X - X)) + (k s - 1) * (X - f s₀ / (k s₀ - 1))‖ := by rw [e1]
      _ ≤ ‖f s - (k s * X - X)‖ + ‖k s - 1‖ * ‖X - f s₀ / (k s₀ - 1)‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul]
      _ ≤ ε + ‖k s - 1‖ * (ε / ‖k s₀ - 1‖) := by
          gcongr
          exact hX s hs
      _ = ε * (1 + ‖k s - 1‖ / ‖k s₀ - 1‖) := by ring
  have hz : ‖f s - (k s * (f s₀ / (k s₀ - 1)) - f s₀ / (k s₀ - 1))‖ ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have h := key (ε / (1 + ‖k s - 1‖ / ‖k s₀ - 1‖)) (div_pos hε hCpos)
    rw [div_mul_cancel₀ _ hCpos.ne'] at h
    linarith
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hz)

end GlobalTheory
