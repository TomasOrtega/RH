import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusDoubleSeriesHasSumAndNormBoundsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusSeriesOntoAndIndependentZerosStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusSeriesLinearIndependentOfFirstTerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftHasSumZeroOfSurjectiveModPrimeStatement
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSerExist

/- English proof (translation)
Establish `h` using `PadicComplex.norm_extends' l (l : ℚ_[l])`. Establish `h2 : ‖(l : ℚ_[l])‖ < 1` using `Padic.norm_p_lt_one`. Establish `h3 : ((l : ℚ_[l]) : ℂ_[l]) = (l : ℂ_[l])` using `by push_cast; rfl`. Rewrite `h` using `[h3]`. Rewrite using `[h]`.

Conclude with `h2`.
-/
theorem norm_l_lt_one (l : ℕ) [Fact l.Prime] : ‖(l : ℂ_[l])‖ < 1 := by
  have h := PadicComplex.norm_extends' l (l : ℚ_[l])
  have h2 : ‖(l : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one
  have h3 : ((l : ℚ_[l]) : ℂ_[l]) = (l : ℂ_[l]) := by push_cast; rfl
  rw [h3] at h
  rw [h]; exact h2

/- English proof (translation)
Establish `h1 : 1 ≤ h` using `le_trans (by norm_num) hh`. Take `⟨τ, hsurj, x, hxS, hxη, hxind⟩` from `GlobalTheory.T.untiltFrobeniusSeries_onto_and_independent_zeros l h μ h1 hμ`. Set `η : Fl l → Unit → ℂ_[l]` to `fun y _ => ∑ i : Fin h, μ i * lam h i y`. Set `S : Set (Fl l)` to `{y | ‖sh y‖ ≤ ‖(l : ℂ_[l])‖}`. Establish `hlift` using `GlobalTheory.T.lift_hasSum_zero_of_surjective_mod_prime l (Fl l) Unit η (fun _ => τ) S (fun t ht => by`.

Take `⟨y, hy, hyt⟩` from `hsurj (t ()) (ht ())`. Conclude with `⟨y, hy, fun i => by cases i; exact hyt⟩)`. Establish `hy : ∀ a : Fin h, ∃ z : ℕ → Fl l, z 0 = x a ∧ (∀ k, z k ∈ S) ∧ ∀ i, HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * η (z k) i) 0` using `fun a => hlift (x a) (hxS a) (fun _ => hxη a)`. Use `choose y hy0 hyS hysum using hy`. Establish `hr : ‖(l : ℂ_[l])‖ < 1` using `norm_l_lt_one l`.

Establish `hyS' : ∀ a k, ‖sh (y a k)‖ ≤ ‖(l : ℂ_[l])‖` using `fun a k => hyS a k`. Use `⟨y, hyS', ?_, ?_⟩` and prove the remaining obligations. Introduce `a`. Establish `hs : ∀ i : Fin h, HasSum (fun k : ℕ => μ i * ((l : ℂ_[l]) ^ k * lam h i (y a k))) (μ i * abelian₂ h i (y a))` using `fun i => ((GlobalTheory.T.untiltFrobeniusDoubleSeries_hasSum_and_norm_bounds l h i ‖(l : ℂ_[l])‖ (y a) h1 hr (hyS' a)).1).mul_left (μ i)`. Establish `hsum` using `hasSum_sum (s := Finset.univ) (fun i _ => hs i)`.

Establish `hsum' : HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * η (y a k) ()) (∑ i : Fin h, μ i * abelian₂ h i (y a))`. Use `hsum using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Simplify using `only [η, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => by ring` and prove the remaining obligations.

Conclude with `hsum'.unique (hysum a ())`. Use `GlobalTheory.T.untiltFrobeniusSeries_linearIndependent_of_firstTerms l h h ‖(l : ℂ_[l])‖ y hh (norm_nonneg _) hr hyS' ?_` and prove the remaining obligations. Introduce `n hn a`. Simplify using `only [hy0] at hn`. Conclude with `hxind n hn a`.
-/
theorem exists_zeros (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]) (hh : 2 ≤ h) (hμ : μ ≠ 0) :
    ∃ y : Fin h → ℕ → Fl l, (∀ a k, ‖sh (y a k)‖ ≤ ‖(l : ℂ_[l])‖) ∧
      (∀ a, ∑ i : Fin h, μ i * abelian₂ h i (y a) = 0) ∧
      ∀ c : Fin h → ℚ_[l], (∀ j : ℕ, j < 2 → ∑ a, algebraMap ℚ_[l] ℂ_[l] (c a) * abelian₂ h j (y a) = 0) →
        c = 0 := by
  have h1 : 1 ≤ h := le_trans (by norm_num) hh
  obtain ⟨τ, hsurj, x, hxS, hxη, hxind⟩ := GlobalTheory.T.untiltFrobeniusSeries_onto_and_independent_zeros l h μ h1 hμ
  let η : Fl l → Unit → ℂ_[l] := fun y _ => ∑ i : Fin h, μ i * lam h i y
  let S : Set (Fl l) := {y | ‖sh y‖ ≤ ‖(l : ℂ_[l])‖}
  have hlift := GlobalTheory.T.lift_hasSum_zero_of_surjective_mod_prime l (Fl l) Unit η (fun _ => τ) S
    (fun t ht => by
      obtain ⟨y, hy, hyt⟩ := hsurj (t ()) (ht ())
      exact ⟨y, hy, fun i => by cases i; exact hyt⟩)
  have hy : ∀ a : Fin h, ∃ z : ℕ → Fl l, z 0 = x a ∧ (∀ k, z k ∈ S) ∧
      ∀ i, HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * η (z k) i) 0 :=
    fun a => hlift (x a) (hxS a) (fun _ => hxη a)
  choose y hy0 hyS hysum using hy
  have hr : ‖(l : ℂ_[l])‖ < 1 := norm_l_lt_one l
  have hyS' : ∀ a k, ‖sh (y a k)‖ ≤ ‖(l : ℂ_[l])‖ := fun a k => hyS a k
  refine ⟨y, hyS', ?_, ?_⟩
  · intro a
    have hs : ∀ i : Fin h, HasSum (fun k : ℕ => μ i * ((l : ℂ_[l]) ^ k * lam h i (y a k)))
        (μ i * abelian₂ h i (y a)) := fun i =>
      ((GlobalTheory.T.untiltFrobeniusDoubleSeries_hasSum_and_norm_bounds l h i ‖(l : ℂ_[l])‖ (y a) h1 hr (hyS' a)).1).mul_left (μ i)
    have hsum := hasSum_sum (s := Finset.univ) (fun i _ => hs i)
    have hsum' : HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * η (y a k) ())
        (∑ i : Fin h, μ i * abelian₂ h i (y a)) := by
      convert hsum using 1
      funext k
      simp only [η, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    exact hsum'.unique (hysum a ())
  · refine GlobalTheory.T.untiltFrobeniusSeries_linearIndependent_of_firstTerms l h h ‖(l : ℂ_[l])‖ y hh (norm_nonneg _) hr hyS' ?_
    intro n hn a
    simp only [hy0] at hn
    exact hxind n hn a

end GlobalTheory.PSerExist
