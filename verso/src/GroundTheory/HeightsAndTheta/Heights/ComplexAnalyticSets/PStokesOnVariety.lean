import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StStokesOffDiscriminant
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCutOffLimit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

/- English proof (translation)
Establish `key : ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (f g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ), J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → SmoothNear (zeroSet J) f → SmoothNear (zeroSet J) g → (∀ i, SmoothNear (zeroSet J) (φ i)) → HasCompa …`. Introduce `n d J f g φ hJ hdim hf hg hφ hc`. Unfold `varInt`. Use `split_ifs with hA`. Establish `hAf` using `hA.choose_spec`.

Generalize the expression as in `hA.choose = A at hAf ⊢`. Take `⟨P, hP0, hPcov⟩` from `hD n (d + 1) J A hJ hdim hAf`. Establish `hsheet : ∀ x ∈ zeroSet J, eval (A *ᵥ x) P ≠ 0 → ∃ s, IsSheetAt J A x s`. Introduce `x hx hPx`. Take `⟨-, -, hloc⟩` from `hPcov (A *ᵥ x) hPx`.

Take `⟨U, V, s, hU, hyU, hV, hxV, hs, hsy, hAs, hZV⟩` from `hloc x ⟨hx, rfl⟩`. Use `⟨s, U, hU, hyU, hs, hsy, fun w hw => ⟨hAs w hw, ?_⟩, V, hV.mem_nhds hxV, ?_⟩` and prove the remaining obligations. Establish `hw' : s w ∈ zeroSet J ∩ V` using `hZV ▸ Set.mem_image_of_mem s hw`. Conclude with `hw'.1`. Introduce and unpack `x' hx' -`.

Rewrite `hx'` using `[hZV]`. Take `⟨w, hw, rfl⟩` from `hx'`. Rewrite using `[hAs w hw]`. Take `⟨χ, hχs, hχU, hlim⟩` from `hL n d J A P hJ hdim hAf hP0`. Take `⟨h1, h2⟩` from `hlim f g φ hf hg hφ hc`.

Use `tendsto_nhds_unique h1 (Tendsto.congr (fun k => ?_) h2)` and prove the remaining obligations. Take `⟨U, hU, hDU, hχ0⟩` from `hχU k`. Take `⟨V, hV, hZV, hfV⟩` from `hf`. Establish `hcχ : HasCompactSupport (fun x => χ k x * f x)` using `hc.mul_left (f := χ k)`. Use `(hS n d J A P hJ hdim hAf hP0 hsheet (fun x => χ k x * f x) g φ ⟨V, hV, hZV, (hχs k).contDiffOn.mul hfV⟩ hg hφ hcχ ⟨U, hU, hDU, fun x hx => ?_⟩).symm` and prove the remaining obligations.

Rewrite using `[hχ0 x hx, zero_mul]`. Both sides reduce to the same expression. Introduce `n d J f g φ hJ hdim hf hg hφ hc`. Break down `hc with hc | hc` into its components or cases. Conclude with `key n d J f g φ hJ hdim hf hg hφ hc`.

Conclude with `(key n d J g f φ hJ hdim hg hf hφ hc).symm`.
-/
theorem StokesOnVariety.proof (hD : ComplexSets.DiscriminantCover.Statement)
    (hS : StokesOffDiscriminant.Statement) (hL : CutOffLimit.Statement) :
    StokesOnVariety.Statement := by
  have key : ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (f g : (Fin n → ℂ) → ℝ)
      (φ : Fin d → (Fin n → ℂ) → ℝ), J.IsPrime →
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) →
      SmoothNear (zeroSet J) f → SmoothNear (zeroSet J) g → (∀ i, SmoothNear (zeroSet J) (φ i)) →
      HasCompactSupport f → varInt J (d + 1) f (vecCons g φ) = varInt J (d + 1) g (vecCons f φ) := by
    intro n d J f g φ hJ hdim hf hg hφ hc
    unfold varInt
    split_ifs with hA
    · have hAf := hA.choose_spec
      generalize hA.choose = A at hAf ⊢
      obtain ⟨P, hP0, hPcov⟩ := hD n (d + 1) J A hJ hdim hAf

      have hsheet : ∀ x ∈ zeroSet J, eval (A *ᵥ x) P ≠ 0 → ∃ s, IsSheetAt J A x s := by
        intro x hx hPx
        obtain ⟨-, -, hloc⟩ := hPcov (A *ᵥ x) hPx
        obtain ⟨U, V, s, hU, hyU, hV, hxV, hs, hsy, hAs, hZV⟩ := hloc x ⟨hx, rfl⟩
        refine ⟨s, U, hU, hyU, hs, hsy, fun w hw => ⟨hAs w hw, ?_⟩, V, hV.mem_nhds hxV, ?_⟩
        · have hw' : s w ∈ zeroSet J ∩ V := hZV ▸ Set.mem_image_of_mem s hw
          exact hw'.1
        · rintro x' hx' -
          rw [hZV] at hx'
          obtain ⟨w, hw, rfl⟩ := hx'
          rw [hAs w hw]
      obtain ⟨χ, hχs, hχU, hlim⟩ := hL n d J A P hJ hdim hAf hP0
      obtain ⟨h1, h2⟩ := hlim f g φ hf hg hφ hc
      refine tendsto_nhds_unique h1 (Tendsto.congr (fun k => ?_) h2)
      obtain ⟨U, hU, hDU, hχ0⟩ := hχU k
      obtain ⟨V, hV, hZV, hfV⟩ := hf
      have hcχ : HasCompactSupport (fun x => χ k x * f x) := hc.mul_left (f := χ k)
      refine (hS n d J A P hJ hdim hAf hP0 hsheet (fun x => χ k x * f x) g φ
        ⟨V, hV, hZV, (hχs k).contDiffOn.mul hfV⟩ hg hφ hcχ ⟨U, hU, hDU, fun x hx => ?_⟩).symm
      rw [hχ0 x hx, zero_mul]
    · rfl
  intro n d J f g φ hJ hdim hf hg hφ hc
  rcases hc with hc | hc
  · exact key n d J f g φ hJ hdim hf hg hφ hc
  · exact (key n d J g f φ hJ hdim hg hf hφ hc).symm

end GroundTheory.Heights₂.Heights
