import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreePartIntegralDifferentialOfCoboundaryStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

/- English proof (translation)
Introduce `p _ k _ _ _ d μ hμ f hlin hcob`. Establish `key : ∀ N, ∀ α : Fin d →₀ ℕ, α.degree = N → ∀ i, ∃ w : WittVector p k, (α i : Fr p k) * coeff α f = algebraMap (WittVector p k) (Fr p k) w`. Introduce `N`. Proceed by induction on `N using Nat.strong_induction_on with`. Consider the case `_ N ih`.

Introduce `α hα i`. Break down `Nat.lt_or_ge N 2 with hN | hN` into its components or cases. Use `interval_cases N`. Establish `h0 : α = 0` using `(Finsupp.degree_eq_zero_iff α).1 hα`. Substitute `h0` using the available equality.

Conclude with `⟨0, by simp⟩`. Distinguish the cases in `hi : α i = 0`. Conclude with `⟨0, by simp [hi]⟩`. Establish `hα' : α ∈ Set.range (fun a : Fin d ↦ Finsupp.single a 1)`. Rewrite using `[Finsupp.range_single_one]`.

Conclude with `hα`. Take `⟨a, rfl⟩` from `hα'`. Establish `hai : a = i`. Assume the negation of the conclusion as `hne`. Conclude with `hi (Finsupp.single_eq_of_ne (Ne.symm hne))`.

Substitute `hai` using the available equality. Take `⟨w, hw⟩` from `hlin a`. Use `⟨w, ?_⟩` and prove the remaining obligations. Simplify using `only [Finsupp.single_eq_same, Nat.cast_one, one_mul]`. Conclude with `hw`.

Set `g : MvPowerSeries (Fin d) (Fr p k)` to `fun β => if β.degree < N then coeff β f else 0`. Establish `hg : ∀ β, coeff β g = if β.degree < N then coeff β f else 0` using `fun β => rfl`. Establish `hgq : g ∈ quasiInt p k (Fin d)` using `by show ∀ (β : Fin d →₀ ℕ) (j : Fin d), ∃ w : WittVector p k, (β j : Fr p k) * coeff β g = algebraMap _ (Fr p k) w`. Introduce `β j`. Distinguish the cases in `hβ : β.degree < N`.

Take `⟨w, hw⟩` from `ih β.degree hβ β rfl j`. Use `⟨w, ?_⟩` and prove the remaining obligations. Rewrite using `[hg, if_pos hβ]`. Conclude with `hw`. Conclude with `⟨0, by rw [hg, if_neg hβ]; simp⟩`.

Establish `hh : ∀ β : Fin d →₀ ℕ, β.degree < N → coeff β (f - g) = 0`. Introduce `β hβ`. Rewrite using `[map_sub, hg, if_pos hβ, sub_self]`. Establish `hc : ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree = N → ∃ w : WittVector p k, coeff γ (cob1 (fun i => Katz.lift p (μ i)) (g + (f - g))) = algebraMap (WittVector p k) (Fr p k) w`. Introduce `γ _`.

Rewrite using `[add_sub_cancel]`. Take `⟨w, hw⟩` from `hcob γ`. Conclude with `⟨1 * w, hw⟩`. Take `⟨w, hw⟩` from `GlobalTheory.T.degree_part_integralDifferential_of_coboundary p k d μ hμ N g (f - g) hN hgq hh hc α i hα`. Use `⟨w, ?_⟩` and prove the remaining obligations.

Establish `hfα : coeff α (f - g) = coeff α f`. Rewrite using `[map_sub, hg, if_neg (by omega), sub_zero]`. Rewrite using `[← hfα]`. Conclude with `hw`. Use `show ∀ (α : Fin d →₀ ℕ) (i : Fin d), ∃ w : WittVector p k, (α i : Fr p k) * coeff α f = algebraMap _ (Fr p k) w`.

Introduce `α i`. Conclude with `key _ α rfl i`.
-/
theorem quasiInt_of_cob1_int_of_lin_int : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), IsLaw μ → ∀ f : MvPowerSeries (Fin d) (Fr p k), (∀ i, ∃ w : WittVector p k, lin f i = algebraMap (WittVector p k) (Fr p k) w) → cob1 (fun i => Katz.lift p (μ i)) f ∈ intBy p k _ 1 → f ∈ quasiInt p k (Fin d) := by
  intro p _ k _ _ _ d μ hμ f hlin hcob
  have key : ∀ N, ∀ α : Fin d →₀ ℕ, α.degree = N → ∀ i, ∃ w : WittVector p k,
      (α i : Fr p k) * coeff α f = algebraMap (WittVector p k) (Fr p k) w := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro α hα i
      rcases Nat.lt_or_ge N 2 with hN | hN
      · interval_cases N
        · have h0 : α = 0 := (Finsupp.degree_eq_zero_iff α).1 hα
          subst h0
          exact ⟨0, by simp⟩
        · by_cases hi : α i = 0
          · exact ⟨0, by simp [hi]⟩
          · have hα' : α ∈ Set.range (fun a : Fin d ↦ Finsupp.single a 1) := by
              rw [Finsupp.range_single_one]; exact hα
            obtain ⟨a, rfl⟩ := hα'
            have hai : a = i := by
              by_contra hne
              exact hi (Finsupp.single_eq_of_ne (Ne.symm hne))
            subst hai
            obtain ⟨w, hw⟩ := hlin a
            refine ⟨w, ?_⟩
            simp only [Finsupp.single_eq_same, Nat.cast_one, one_mul]
            exact hw
      · let g : MvPowerSeries (Fin d) (Fr p k) := fun β => if β.degree < N then coeff β f else 0
        have hg : ∀ β, coeff β g = if β.degree < N then coeff β f else 0 := fun β => rfl
        have hgq : g ∈ quasiInt p k (Fin d) := by
          show ∀ (β : Fin d →₀ ℕ) (j : Fin d), ∃ w : WittVector p k,
            (β j : Fr p k) * coeff β g = algebraMap _ (Fr p k) w
          intro β j
          by_cases hβ : β.degree < N
          · obtain ⟨w, hw⟩ := ih β.degree hβ β rfl j
            refine ⟨w, ?_⟩
            rw [hg, if_pos hβ]; exact hw
          · exact ⟨0, by rw [hg, if_neg hβ]; simp⟩
        have hh : ∀ β : Fin d →₀ ℕ, β.degree < N → coeff β (f - g) = 0 := by
          intro β hβ
          rw [map_sub, hg, if_pos hβ, sub_self]
        have hc : ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree = N → ∃ w : WittVector p k,
            coeff γ (cob1 (fun i => Katz.lift p (μ i)) (g + (f - g))) =
              algebraMap (WittVector p k) (Fr p k) w := by
          intro γ _
          rw [add_sub_cancel]
          obtain ⟨w, hw⟩ := hcob γ
          exact ⟨1 * w, hw⟩
        obtain ⟨w, hw⟩ := GlobalTheory.T.degree_part_integralDifferential_of_coboundary p k d μ hμ N g (f - g) hN hgq hh hc α i hα
        refine ⟨w, ?_⟩
        have hfα : coeff α (f - g) = coeff α f := by
          rw [map_sub, hg, if_neg (by omega), sub_zero]
        rw [← hfα]; exact hw
  show ∀ (α : Fin d →₀ ℕ) (i : Fin d), ∃ w : WittVector p k,
    (α i : Fr p k) * coeff α f = algebraMap _ (Fr p k) w
  intro α i
  exact key _ α rfl i

end GlobalTheory.Katz
