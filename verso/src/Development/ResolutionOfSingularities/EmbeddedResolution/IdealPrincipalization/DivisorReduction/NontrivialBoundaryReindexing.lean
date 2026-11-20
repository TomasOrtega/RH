import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.SmoothPullbackCompatibility
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.BoundaryReindexing
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.BaseChangeMorphismProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

/- English proof (translation)
Establish `key : ∀ L : List α, List.filter p (L.map g) = List.filter p ((List.filter p L).map g)`. Introduce `L`. Proceed by induction on `L with`. Consider the case `nil => rfl`. Consider the case `cons a t ih`.

Distinguish the cases in `ha : p a = true`. Simplify using `[List.filter_cons, ha, ih]`. Establish `ha' : p a = false` using `by simpa using ha`. Establish `hga : p (g a) = false` using `hpg a ha'`. Simplify using `[ha', hga, ih]`.

Rewrite using `[key A, key B, hAB]`.
-/
private theorem filter_map_eq_of_filter_eq {α : Type*} (p : α → Bool) (g : α → α)
    (hpg : ∀ a, p a = false → p (g a) = false) {A B : List α}
    (hAB : List.filter p A = List.filter p B) :
    List.filter p (A.map g) = List.filter p (B.map g) := by
  have key : ∀ L : List α,
      List.filter p (L.map g) = List.filter p ((List.filter p L).map g) := by
    intro L
    induction L with
    | nil => rfl
    | cons a t ih =>
      by_cases ha : p a = true
      · simp [List.filter_cons, ha, ih]
      · have ha' : p a = false := by simpa using ha
        have hga : p (g a) = false := hpg a ha'
        simp [ha', hga, ih]
  rw [key A, key B, hAB]

/- English proof (translation)
Rewrite `h`, the goal using `[MarkedIdealWithBoundary.sameNontrivialBoundary_iff]`. Unfold `MarkedIdealWithBoundary.nontrivialPart at h ⊢`. Use `filter_map_eq_of_filter_eq _ g ?_ h` and prove the remaining obligations. Introduce `a ha`. Establish `ha' : a = ⊤` using `by simpa using ha`.

Substitute `ha'` using the available equality. Simplify using `[hg]`.
-/
private theorem sameNontrivialBoundary_map {X : Scheme.{u}} (g : X.IdealSheafData → X.IdealSheafData)
    (hg : g ⊤ = ⊤) {A B : List X.IdealSheafData} (h : MarkedIdealWithBoundary.SameNontrivialBoundary A B) :
    MarkedIdealWithBoundary.SameNontrivialBoundary (A.map g) (B.map g) := by
  rw [MarkedIdealWithBoundary.sameNontrivialBoundary_iff] at h ⊢
  unfold MarkedIdealWithBoundary.nontrivialPart at h ⊢
  refine filter_map_eq_of_filter_eq _ g ?_ h
  intro a ha
  have ha' : a = ⊤ := by simpa using ha
  subst ha'
  simp [hg]

/- English proof (translation)
Establish `hcomap : ∀ I : X.IdealSheafData, I.comap (𝟙 X) = I`. Introduce `I`. Simplify using the standard rewrite rules. Establish `hgtop : (fun D : X.IdealSheafData => Blowup.strictTransform (𝟙 X) Z (D.comap (𝟙 X))) ⊤ = (⊤ : X.IdealSheafData)` using `by show Blowup.strictTransform (𝟙 X) Z ((⊤ : X.IdealSheafData).comap (𝟙 X)) = ⊤`. Rewrite using `[hcomap]`.

Establish `h1` using `comap_le_strictTransform (𝟙 X) Z (⊤ : X.IdealSheafData)`. Rewrite `h1` using `[hcomap]`. Conclude with `le_antisymm le_top h1`. Establish `key : ∀ (C : List X.IdealSheafData) (c : ℕ), c < C.length → List.take (C.length - 1) ((List.map (Blowup.strictTransform (𝟙 X) Z) (List.map (fun D => D.comap (𝟙 X)) C) ++ [Blowup.exceptionalIdeal (𝟙 X) Z]).eraseIdx c) = List.map (fun D : X.IdealSheafData => Blowup.strictTransform …`. Introduce `C c hc`.

Establish `hlen : (List.map (fun D : X.IdealSheafData => Blowup.strictTransform (𝟙 X) Z (D.comap (𝟙 X))) (C.eraseIdx c)).length = C.length - 1`. Rewrite using `[List.length_map]`. Conclude with `List.length_eraseIdx_of_lt hc`. Establish `hmap : ∀ f : X.IdealSheafData → X.IdealSheafData, c < (C.map f).length`. Introduce `f`.

Rewrite using `[List.length_map]`. Conclude with `hc`. Simplify using `only [List.map_map, Function.comp_def]`. Rewrite using `[List.eraseIdx_append_of_lt_length (hmap _)]`. Rewrite using `[List.eraseIdx_map, ← hlen, List.take_append_of_le_length (Nat.le_refl _), List.take_length]`.

Rewrite using `[key A a ha, key B b hb]`. Conclude with `sameNontrivialBoundary_map (fun D : X.IdealSheafData => Blowup.strictTransform (𝟙 X) Z (D.comap (𝟙 X))) hgtop h`.
-/
private theorem sameNontrivialBoundary_take_eraseIdx_strictTransform {X : Scheme.{u}} (Z : X.IdealSheafData)
    (A B : List X.IdealSheafData) (a b : ℕ) (ha : a < A.length) (hb : b < B.length)
    (h : MarkedIdealWithBoundary.SameNontrivialBoundary (A.eraseIdx a) (B.eraseIdx b)) :
    MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.take (A.length - 1)
        ((List.map (Blowup.strictTransform (𝟙 X) Z) (List.map (fun D => D.comap (𝟙 X)) A)
          ++ [Blowup.exceptionalIdeal (𝟙 X) Z]).eraseIdx a))
      (List.take (B.length - 1)
        ((List.map (Blowup.strictTransform (𝟙 X) Z) (List.map (fun D => D.comap (𝟙 X)) B)
          ++ [Blowup.exceptionalIdeal (𝟙 X) Z]).eraseIdx b)) := by
  have hcomap : ∀ I : X.IdealSheafData, I.comap (𝟙 X) = I := by
    intro I
    simp
  have hgtop : (fun D : X.IdealSheafData => Blowup.strictTransform (𝟙 X) Z (D.comap (𝟙 X))) ⊤
      = (⊤ : X.IdealSheafData) := by
    show Blowup.strictTransform (𝟙 X) Z ((⊤ : X.IdealSheafData).comap (𝟙 X)) = ⊤
    rw [hcomap]
    have h1 := comap_le_strictTransform (𝟙 X) Z (⊤ : X.IdealSheafData)
    rw [hcomap] at h1
    exact le_antisymm le_top h1
  have key : ∀ (C : List X.IdealSheafData) (c : ℕ), c < C.length →
      List.take (C.length - 1)
        ((List.map (Blowup.strictTransform (𝟙 X) Z) (List.map (fun D => D.comap (𝟙 X)) C)
          ++ [Blowup.exceptionalIdeal (𝟙 X) Z]).eraseIdx c)
        = List.map (fun D : X.IdealSheafData => Blowup.strictTransform (𝟙 X) Z (D.comap (𝟙 X)))
            (C.eraseIdx c) := by
    intro C c hc
    have hlen : (List.map (fun D : X.IdealSheafData =>
        Blowup.strictTransform (𝟙 X) Z (D.comap (𝟙 X))) (C.eraseIdx c)).length = C.length - 1 := by
      rw [List.length_map]
      exact List.length_eraseIdx_of_lt hc
    have hmap : ∀ f : X.IdealSheafData → X.IdealSheafData, c < (C.map f).length := by
      intro f
      rw [List.length_map]
      exact hc
    simp only [List.map_map, Function.comp_def]
    rw [List.eraseIdx_append_of_lt_length (hmap _)]
    rw [List.eraseIdx_map, ← hlen, List.take_append_of_le_length (Nat.le_refl _),
      List.take_length]
  rw [key A a ha, key B b hb]
  exact sameNontrivialBoundary_map (fun D : X.IdealSheafData => Blowup.strictTransform (𝟙 X) Z (D.comap (𝟙 X)))
    hgtop h

/- English proof (translation)
Unfold `lowerIdealAfterBlowup`. Rewrite using `[containedComponentsIdeal_withBoundary_congr T L₁ L₂ j₁ hj₁ j₂ hj₂ heq]`. Both sides reduce to the same expression.
-/
theorem lowerIdealAfterBlowup_withBoundary_eq_of_get_eq (T : MarkedIdealWithBoundary.{u}) (L₁ L₂ : List T.scheme.IdealSheafData)
    (j₁ : ℕ) (hj₁ : j₁ < L₁.length) (j₂ : ℕ) (hj₂ : j₂ < L₂.length)
    (heq : L₁.get ⟨j₁, hj₁⟩ = L₂.get ⟨j₂, hj₂⟩) :
    lowerIdealAfterBlowup (T.withBoundary L₂) j₂ hj₂ = lowerIdealAfterBlowup (T.withBoundary L₁) j₁ hj₁ := by
  unfold lowerIdealAfterBlowup
  rw [containedComponentsIdeal_withBoundary_congr T L₁ L₂ j₁ hj₁ j₂ hj₂ heq]
  rfl

/- English proof (translation)
Unfold `lowerBoundaryAfterBlowup`. Rewrite using `[containedComponentsIdeal_withBoundary_congr T L₁ L₂ j₁ hj₁ j₂ hj₂ heq]`. Conclude with `sameNontrivialBoundary_take_eraseIdx_strictTransform (containedComponentsIdeal (T.withBoundary L₂) j₂ hj₂) L₂ L₁ j₂ j₁ hj₂ hj₁ hBE`.
-/
theorem sameNontrivialBoundary_lowerBoundaryAfterBlowup_of_get_eq (T : MarkedIdealWithBoundary.{u}) (L₁ L₂ : List T.scheme.IdealSheafData)
    (j₁ : ℕ) (hj₁ : j₁ < L₁.length) (j₂ : ℕ) (hj₂ : j₂ < L₂.length)
    (heq : L₁.get ⟨j₁, hj₁⟩ = L₂.get ⟨j₂, hj₂⟩)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (L₂.eraseIdx j₂) (L₁.eraseIdx j₁)) :
    MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.take (L₂.length - 1) ((lowerBoundaryAfterBlowup (T.withBoundary L₂) j₂ hj₂).eraseIdx j₂))
      (List.take (L₁.length - 1) ((lowerBoundaryAfterBlowup (T.withBoundary L₁) j₁ hj₁).eraseIdx j₁)) := by
  unfold lowerBoundaryAfterBlowup
  rw [containedComponentsIdeal_withBoundary_congr T L₁ L₂ j₁ hj₁ j₂ hj₂ heq]
  exact sameNontrivialBoundary_take_eraseIdx_strictTransform
    (containedComponentsIdeal (T.withBoundary L₂) j₂ hj₂) L₂ L₁ j₂ j₁ hj₂ hj₁ hBE

/- English proof (translation)
Assemble the required witnesses or components as `⟨smooth_id, surjective_id, lowerIdealAfterBlowup_withBoundary_eq_of_get_eq, sameNontrivialBoundary_lowerBoundaryAfterBlowup_of_get_eq⟩`.
-/
theorem boundaryReindexingInvariance : BoundaryReindexingInvariance.{u} :=
  ⟨smooth_id, surjective_id, lowerIdealAfterBlowup_withBoundary_eq_of_get_eq, sameNontrivialBoundary_lowerBoundaryAfterBlowup_of_get_eq⟩

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
