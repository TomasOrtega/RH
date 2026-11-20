import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum

/- English proof (translation)
Introduce `n ε H _ _ _ σ hS hB a c ha ha0 hc hc0 N`. Take `⟨Sa, Ca, hSa, hCa, ba⟩` from `hB a ha ha0 N`. Take `⟨Sc, Cc, hSc, hCc, bc⟩` from `hB c hc hc0 N`. Use `⟨Sa ++ Sc, Ca * Cc, words_append hSa hSc, mul_nonneg hCa hCc, ?_⟩` and prove the remaining obligations. Introduce `γ h1 h2 M hM hγ b w hb hw`.

Establish `step : ∀ g' ∈ UJset ε, ‖γ (σ g' c) w‖ ≤ (Ca * M * sobNorm σ Sa w) * (1 + hs g') ^ N`. Introduce `g' hg'`. Take `⟨ℓ, hℓ, e⟩` from `(h1 _ (hc.translate hS.1 hg')).exists_ext`. Establish `hp : 0 ≤ (1 + hs g') ^ N` using `pow_nonneg (by linarith [hs_nonneg g']) N`. Use `ba ℓ hℓ (M * (1 + hs g') ^ N) (mul_nonneg hM hp) (fun g hg => by` as an intermediate fact.

Rewrite using `[e _ (ha.translate hS.1 hg)]`. Conclude with `(hγ g hg g' hg').trans (le_of_eq (by ring))) w hw`. Rewrite `this` using `[e _ hw]`. Conclude with `this.trans (le_of_eq (by ring))`. Take `⟨ℓ, hℓ, e⟩` from `(h2 w hw).exists_ext`.

Establish `n1` using `sobNorm_nonneg σ Sa w`. Establish `n2` using `sobNorm_nonneg σ Sc w`. Establish `n3` using `sobNorm_nonneg σ Sa b`. Establish `n4` using `sobNorm_nonneg σ Sc b`. Establish `key` using `bc ℓ hℓ (Ca * M * sobNorm σ Sa w) (by positivity) (fun g hg => by`.

Rewrite using `[e _ (hc.translate hS.1 hg), norm_star]`. Conclude with `step g hg) b hb`. Rewrite `key` using `[e _ hb, norm_star]`. Rewrite using `[sobNorm_append, sobNorm_append]`. Use `key.trans ?_` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem coefBound_two :
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → CoefBound ε σ → ∀ a c : H, Sm ε σ a → a ≠ 0 → Sm ε σ c → c ≠ 0 → ∀ N : ℕ, ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧ ∀ γ : H → H → ℂ, (∀ b, Sm ε σ b → SobFun ε σ (γ b)) → (∀ w, Sm ε σ w → SobFun ε σ (fun b => star (γ b w))) → ∀ M : ℝ, 0 ≤ M → (∀ g ∈ UJset ε, ∀ g' ∈ UJset ε, ‖γ (σ g' c) (σ g a)‖ ≤ M * (1 + hs g) ^ N * (1 + hs g') ^ N) → ∀ b w, Sm ε σ b → Sm ε σ w → ‖γ b w‖ ≤ C * M * sobNorm σ S b * sobNorm σ S w := by
  intro n ε H _ _ _ σ hS hB a c ha ha0 hc hc0 N
  obtain ⟨Sa, Ca, hSa, hCa, ba⟩ := hB a ha ha0 N
  obtain ⟨Sc, Cc, hSc, hCc, bc⟩ := hB c hc hc0 N
  refine ⟨Sa ++ Sc, Ca * Cc, words_append hSa hSc, mul_nonneg hCa hCc, ?_⟩
  intro γ h1 h2 M hM hγ b w hb hw
  have step : ∀ g' ∈ UJset ε, ‖γ (σ g' c) w‖ ≤ (Ca * M * sobNorm σ Sa w) * (1 + hs g') ^ N := by
    intro g' hg'
    obtain ⟨ℓ, hℓ, e⟩ := (h1 _ (hc.translate hS.1 hg')).exists_ext
    have hp : 0 ≤ (1 + hs g') ^ N := pow_nonneg (by linarith [hs_nonneg g']) N
    have := ba ℓ hℓ (M * (1 + hs g') ^ N) (mul_nonneg hM hp) (fun g hg => by
      rw [e _ (ha.translate hS.1 hg)]
      exact (hγ g hg g' hg').trans (le_of_eq (by ring))) w hw
    rw [e _ hw] at this
    exact this.trans (le_of_eq (by ring))
  obtain ⟨ℓ, hℓ, e⟩ := (h2 w hw).exists_ext
  have n1 := sobNorm_nonneg σ Sa w
  have n2 := sobNorm_nonneg σ Sc w
  have n3 := sobNorm_nonneg σ Sa b
  have n4 := sobNorm_nonneg σ Sc b
  have key := bc ℓ hℓ (Ca * M * sobNorm σ Sa w) (by positivity) (fun g hg => by
    rw [e _ (hc.translate hS.1 hg), norm_star]
    exact step g hg) b hb
  rw [e _ hb, norm_star] at key
  rw [sobNorm_append, sobNorm_append]
  refine key.trans ?_
  calc Cc * (Ca * M * sobNorm σ Sa w) * sobNorm σ Sc b
      = Ca * Cc * M * sobNorm σ Sc b * sobNorm σ Sa w := by ring
    _ ≤ _ := by gcongr <;> linarith

end GlobalTheory.TypeSum
