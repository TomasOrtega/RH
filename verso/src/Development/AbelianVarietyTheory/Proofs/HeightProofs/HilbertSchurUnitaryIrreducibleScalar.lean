import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
open Formalism.MainNotions.S Matrix MeasureTheory

namespace GlobalTheory

/- English proof (translation)
Establish `hsub : (spectrum ℝ A).Subsingleton`. Establish `key : ∀ a ∈ spectrum ℝ A, ∀ b ∈ spectrum ℝ A, ¬ a < b`. Introduce `a ha b hb hab`. Use `set m : ℝ := (a + b) / 2 with hm`. Set `f : ℝ → ℝ` to `fun x => max (m - x) 0`.

Set `g : ℝ → ℝ` to `fun x => max (x - m) 0`. Establish `hf : Continuous f` using `by fun_prop`. Establish `hg : Continuous g` using `by fun_prop`. Establish `hfg : cfc f A * cfc g A = 0`. Rewrite using `[← cfc_mul f g A hf.continuousOn hg.continuousOn]`.

Establish `: (fun x => f x * g x) = (0 : ℝ → ℝ)`. Use function extensionality and compare the values at `x`. Simplify using `only [f, g, Pi.zero_apply]`. Break down `le_total x m with h | h` into its components or cases. Rewrite using `[max_eq_right (by linarith : x - m ≤ 0), mul_zero]`.

Rewrite using `[max_eq_right (by linarith : m - x ≤ 0), zero_mul]`. Rewrite using `[this, cfc_zero]`. Establish `hne : ∀ (k : ℝ → ℝ), Continuous k → ∀ x ∈ spectrum ℝ A, k x ≠ 0 → cfc k A ≠ 0`. Introduce `k hk x hx hkx h0`. Establish `h1 : cfc k A = cfc (0 : ℝ → ℝ) A` using `by rw [h0, cfc_zero]`.

Conclude with `hkx (eqOn_of_cfc_eq_cfc h1 hk.continuousOn continuousOn_const hA hx)`. Establish `hf0 : cfc f A ≠ 0` using `hne f hf a ha (by`. Establish `: 0 < m - a` using `by rw [hm]; linarith`. Simplify using `only [f]`. Rewrite using `[max_eq_left this.le]`.

Conclude with `this.ne')`. Establish `hg0 : cfc g A ≠ 0` using `hne g hg b hb (by`. Establish `: 0 < b - m` using `by rw [hm]; linarith`. Simplify using `only [g]`. Rewrite using `[max_eq_left this.le]`.

Conclude with `this.ne')`. Establish `hcomm : ∀ x, Commute (cfc f A) (π x)` using `fun x => hA.commute_cfc (show Commute A (π x) from (hc x).symm) f`. Break down `hirr (LinearMap.ker (cfc f A : H →L[ℂ] H).toLinearMap) (cfc f A).isClosed_ker (by` into its components or cases. Introduce `x v hv`. Establish `hv' : cfc f A v = 0` using `hv`.

Use `show cfc f A (π x v) = 0`. Use `congrArg (fun T : H →L[ℂ] H => T v) (hcomm x).eq` as an intermediate fact. Simplify using `only [ContinuousLinearMap.mul_apply] at this`. Rewrite using `[this, hv', map_zero]) with h | h`. Apply `hg0` to reduce the goal to its premises.

Use extensionality with `v`. Establish `: cfc g A v ∈ LinearMap.ker (cfc f A : H →L[ℂ] H).toLinearMap` using `by show cfc f A (cfc g A v) = 0`. Use `congrArg (fun T : H →L[ℂ] H => T v) hfg` as an intermediate fact. Simplify using `using this`. Rewrite `this` using `[h]`.

Simplify using `using this`. Apply `hf0` to reduce the goal to its premises. Use extensionality with `v`. Establish `: v ∈ LinearMap.ker (cfc f A : H →L[ℂ] H).toLinearMap`. Rewrite using `[h]`.

Discharge the goal by the elementary cases of `trivial`. Conclude with `this`. Introduce `a ha b hb`. Conclude with `le_antisymm (not_lt.1 (key b hb a ha)) (not_lt.1 (key a ha b hb))`. Choose the witnesses or unpack the hypotheses as in `⟨r, hr⟩ : ∃ r : ℝ, spectrum ℝ A ⊆ {r} := by`.

Break down `hsub.eq_empty_or_singleton with h | ⟨r, h⟩` into its components or cases. Conclude with `⟨0, by rw [h]; exact Set.empty_subset _⟩`. Conclude with `⟨r, h.subset⟩`. Use `⟨r, ?_⟩` and prove the remaining obligations. Rewrite using `[CFC.eq_algebraMap_of_spectrum_subset_singleton A r hr hA, Algebra.algebraMap_eq_smul_one, Complex.coe_smul]`.
-/
theorem hilbert_schur_selfAdjoint (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (G : Type) (π : G → (H →L[ℂ] H))
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, π g v ∈ S) → S = ⊥ ∨ S = ⊤)
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (hc : ∀ g, π g * A = A * π g) :
    ∃ c : ℂ, A = c • (1 : H →L[ℂ] H) := by
  have hsub : (spectrum ℝ A).Subsingleton := by
    have key : ∀ a ∈ spectrum ℝ A, ∀ b ∈ spectrum ℝ A, ¬ a < b := by
      intro a ha b hb hab
      set m : ℝ := (a + b) / 2 with hm
      let f : ℝ → ℝ := fun x => max (m - x) 0
      let g : ℝ → ℝ := fun x => max (x - m) 0
      have hf : Continuous f := by fun_prop
      have hg : Continuous g := by fun_prop
      have hfg : cfc f A * cfc g A = 0 := by
        rw [← cfc_mul f g A hf.continuousOn hg.continuousOn]
        have : (fun x => f x * g x) = (0 : ℝ → ℝ) := by
          funext x
          simp only [f, g, Pi.zero_apply]
          rcases le_total x m with h | h
          · rw [max_eq_right (by linarith : x - m ≤ 0), mul_zero]
          · rw [max_eq_right (by linarith : m - x ≤ 0), zero_mul]
        rw [this, cfc_zero]
      have hne : ∀ (k : ℝ → ℝ), Continuous k → ∀ x ∈ spectrum ℝ A, k x ≠ 0 → cfc k A ≠ 0 := by
        intro k hk x hx hkx h0
        have h1 : cfc k A = cfc (0 : ℝ → ℝ) A := by rw [h0, cfc_zero]
        exact hkx (eqOn_of_cfc_eq_cfc h1 hk.continuousOn continuousOn_const hA hx)
      have hf0 : cfc f A ≠ 0 := hne f hf a ha (by
        have : 0 < m - a := by rw [hm]; linarith
        simp only [f]; rw [max_eq_left this.le]; exact this.ne')
      have hg0 : cfc g A ≠ 0 := hne g hg b hb (by
        have : 0 < b - m := by rw [hm]; linarith
        simp only [g]; rw [max_eq_left this.le]; exact this.ne')
      have hcomm : ∀ x, Commute (cfc f A) (π x) := fun x =>
        hA.commute_cfc (show Commute A (π x) from (hc x).symm) f
      rcases hirr (LinearMap.ker (cfc f A : H →L[ℂ] H).toLinearMap) (cfc f A).isClosed_ker (by
        intro x v hv
        have hv' : cfc f A v = 0 := hv
        show cfc f A (π x v) = 0
        have := congrArg (fun T : H →L[ℂ] H => T v) (hcomm x).eq
        simp only [ContinuousLinearMap.mul_apply] at this
        rw [this, hv', map_zero]) with h | h
      · apply hg0
        ext v
        have : cfc g A v ∈ LinearMap.ker (cfc f A : H →L[ℂ] H).toLinearMap := by
          show cfc f A (cfc g A v) = 0
          have := congrArg (fun T : H →L[ℂ] H => T v) hfg
          simpa using this
        rw [h] at this
        simpa using this
      · apply hf0
        ext v
        have : v ∈ LinearMap.ker (cfc f A : H →L[ℂ] H).toLinearMap := by
          rw [h]; trivial
        exact this
    intro a ha b hb
    exact le_antisymm (not_lt.1 (key b hb a ha)) (not_lt.1 (key a ha b hb))
  obtain ⟨r, hr⟩ : ∃ r : ℝ, spectrum ℝ A ⊆ {r} := by
    rcases hsub.eq_empty_or_singleton with h | ⟨r, h⟩
    · exact ⟨0, by rw [h]; exact Set.empty_subset _⟩
    · exact ⟨r, h.subset⟩
  refine ⟨r, ?_⟩
  rw [CFC.eq_algebraMap_of_spectrum_subset_singleton A r hr hA, Algebra.algebraMap_eq_smul_one,
    Complex.coe_smul]

/- English proof (translation)
Introduce `H _ _ _ G _ π hn hirr A hc`. Establish `hstar : ∀ g, star (π g) = π g⁻¹`. Introduce `g`. Establish `h1 : star (π g) * π g = 1` using `(ContinuousLinearMap.norm_map_iff_adjoint_comp_self (π g)).1 (hn g)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← map_mul, mul_inv_cancel, map_one, mul_one]`. Use `_ = π g⁻¹ := by rw [← mul_assoc, h1, one_mul]`. Establish `hc' : ∀ g, π g * star A = star A * π g`. Introduce `g`. Use `congrArg star (hc g⁻¹)` as an intermediate fact.

Rewrite `this` using `[star_mul, star_mul, hstar, inv_inv]`. Conclude with `this.symm`. Take `⟨b, hb⟩` from `hilbert_schur_selfAdjoint H G π hirr (A + star A) (IsSelfAdjoint.add_star_self A) (fun g => by rw [mul_add, add_mul, hc, hc'])`. Take `⟨c, hc2⟩` from `hilbert_schur_selfAdjoint H G π hirr (Complex.I • (A - star A)) (by`. Rewrite using `[IsSelfAdjoint, star_smul, star_sub, star_star, Complex.star_def, Complex.conj_I, neg_smul, ← smul_neg, neg_sub])`.

Use the proof step `(fun g => by rw [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, hc, hc'])`. Use `⟨(1 / 2 : ℂ) * (b - Complex.I * c), ?_⟩` and prove the remaining obligations. Establish `h3 : A - star A = (-(Complex.I * c)) • (1 : H →L[ℂ] H)`. Rewrite using `[neg_smul, mul_smul, ← hc2, smul_smul, Complex.I_mul_I, neg_smul, neg_neg, one_smul]`. Rewrite using `[mul_smul, sub_eq_add_neg, add_smul, ← hb, ← h3]`.

Use `module`.
-/
theorem hilbert_schur :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (G : Type) [Group G] (π : G →* (H →L[ℂ] H)), (∀ g v, ‖π g v‖ = ‖v‖) → (∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, π g v ∈ S) → S = ⊥ ∨ S = ⊤) → ∀ A : H →L[ℂ] H, (∀ g, π g * A = A * π g) → ∃ c : ℂ, A = c • (1 : H →L[ℂ] H) := by
  intro H _ _ _ G _ π hn hirr A hc
  have hstar : ∀ g, star (π g) = π g⁻¹ := by
    intro g
    have h1 : star (π g) * π g = 1 :=
      (ContinuousLinearMap.norm_map_iff_adjoint_comp_self (π g)).1 (hn g)
    calc star (π g) = star (π g) * (π g * π g⁻¹) := by
          rw [← map_mul, mul_inv_cancel, map_one, mul_one]
      _ = π g⁻¹ := by rw [← mul_assoc, h1, one_mul]
  have hc' : ∀ g, π g * star A = star A * π g := by
    intro g
    have := congrArg star (hc g⁻¹)
    rw [star_mul, star_mul, hstar, inv_inv] at this
    exact this.symm
  obtain ⟨b, hb⟩ := hilbert_schur_selfAdjoint H G π hirr (A + star A)
    (IsSelfAdjoint.add_star_self A) (fun g => by rw [mul_add, add_mul, hc, hc'])
  obtain ⟨c, hc2⟩ := hilbert_schur_selfAdjoint H G π hirr (Complex.I • (A - star A))
    (by
      rw [IsSelfAdjoint, star_smul, star_sub, star_star, Complex.star_def, Complex.conj_I,
        neg_smul, ← smul_neg, neg_sub])
    (fun g => by rw [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, hc, hc'])
  refine ⟨(1 / 2 : ℂ) * (b - Complex.I * c), ?_⟩
  have h3 : A - star A = (-(Complex.I * c)) • (1 : H →L[ℂ] H) := by
    rw [neg_smul, mul_smul, ← hc2, smul_smul, Complex.I_mul_I, neg_smul, neg_neg, one_smul]
  rw [mul_smul, sub_eq_add_neg, add_smul, ← hb, ← h3]
  module

end GlobalTheory
