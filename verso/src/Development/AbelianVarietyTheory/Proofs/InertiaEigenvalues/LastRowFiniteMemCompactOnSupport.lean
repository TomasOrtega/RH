import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjLowUni
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

/- English proof (translation)
Introduce `E _ _ m S β ⟨C, hC, hCβ⟩`. Set `F : GA E (m + 1) → (Fin (m + 1) → Af E)` to `fun c j => pFin E ((c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j)`. Establish `hF : Continuous F`. Use `continuous_pi fun j => ?_` and prove the remaining obligations. Establish `h0 : Continuous fun c : GA E (m + 1) => (c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E))` using `Units.continuous_val`.

Establish `h1 : Continuous fun c : GA E (m + 1) => (c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j` using `h0.matrix_elem (Fin.last m) j`. Conclude with `continuous_snd.comp h1`. Use `⟨F '' C, hC.image hF, fun h hS hβ => ?_⟩` and prove the remaining obligations. Take `⟨u, hu, huC⟩` from `hCβ h hS hβ`. Use `⟨u⁻¹ * h, huC, ?_⟩` and prove the remaining obligations.

Use `set c : GA E (m + 1) := u⁻¹ * h with hc`. Establish `hh : h = u * c` using `by rw [hc]; group`. Establish `key : ∀ j, (h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j = (c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j`. Introduce `j`. Establish `hm : (h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) = (u : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) * (c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E))`.

Rewrite using `[hh]`. Both sides reduce to the same expression. Rewrite using `[hm, Matrix.mul_apply, Finset.sum_eq_single (Fin.last m)]`. Rewrite using `[hu.2, one_mul]`. Introduce `l _ hl`.

Rewrite using `[hu.1 (Fin.last m) l (lt_of_le_of_ne (Fin.le_last l) hl), zero_mul]`. Introduce `h'`. Conclude with `absurd (Finset.mem_univ _) h'`. Use function extensionality and compare the values at `j`. Simplify using `only [F, key j]`.
-/
theorem GlobalTheory.JSW.lastRow_finite_compact : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (β : GA E (m + 1) → ℂ), (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S, β h ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * h ∈ C) → ∃ K : Set (Fin (m + 1) → Af E), IsCompact K ∧ ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S, β h ≠ 0 → (fun j => pFin E ((h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j)) ∈ K := by
  intro E _ _ m S β ⟨C, hC, hCβ⟩
  let F : GA E (m + 1) → (Fin (m + 1) → Af E) :=
    fun c j => pFin E ((c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j)
  have hF : Continuous F := by
    refine continuous_pi fun j => ?_
    have h0 : Continuous fun c : GA E (m + 1) => (c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) :=
      Units.continuous_val
    have h1 : Continuous fun c : GA E (m + 1) => (c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j :=
      h0.matrix_elem (Fin.last m) j
    exact continuous_snd.comp h1
  refine ⟨F '' C, hC.image hF, fun h hS hβ => ?_⟩
  obtain ⟨u, hu, huC⟩ := hCβ h hS hβ
  refine ⟨u⁻¹ * h, huC, ?_⟩
  set c : GA E (m + 1) := u⁻¹ * h with hc
  have hh : h = u * c := by rw [hc]; group
  have key : ∀ j, (h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j =
      (c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j := by
    intro j
    have hm : (h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) =
        (u : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) * (c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) := by
      rw [hh]; rfl
    rw [hm, Matrix.mul_apply, Finset.sum_eq_single (Fin.last m)]
    · rw [hu.2, one_mul]
    · intro l _ hl
      rw [hu.1 (Fin.last m) l (lt_of_le_of_ne (Fin.le_last l) hl), zero_mul]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  funext j
  simp only [F, key j]
