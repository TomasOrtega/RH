import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

/- English proof (translation)
Take `⟨u, hu⟩` from `h0`. Take `⟨v, hv⟩` from `h1`. Use `isUnit_iff_exists_inv.2 ⟨⟨(↑u⁻¹ : L), -(↑u⁻¹ : L) ^ l * x.snd * ↑v⁻¹⟩, ?_⟩` and prove the remaining obligations. Use `W2.ext ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `x.fst * (↑u⁻¹ : L) = 1`.

Rewrite using `[← hu]`. Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `x.fst ^ l * (-(↑u⁻¹ : L) ^ l * x.snd * ↑v⁻¹) + (↑u⁻¹ : L) ^ l * x.snd + (l : L) * x.snd * (-(↑u⁻¹ : L) ^ l * x.snd * ↑v⁻¹) = 0`. Establish `hg : (↑v⁻¹ : L) * (x.fst ^ l + (l : L) * x.snd) = 1`. Express the relevant statement in the definitionally equal form `(↑v⁻¹ : L) * W2.gh x = 1`.

Rewrite using `[← hv]`. Simplify using the standard rewrite rules. Take the linear combination `(-(↑u⁻¹ : L) ^ l * x.snd) * hg`.
-/
theorem W2.isUnit_of_fst_gh {l : ℕ} [Fact l.Prime] {L : Type} [CommRing L] (x : W2 l L) (h0 : IsUnit x.fst)
    (h1 : IsUnit (W2.gh x)) : IsUnit x := by
  obtain ⟨u, hu⟩ := h0
  obtain ⟨v, hv⟩ := h1
  refine isUnit_iff_exists_inv.2 ⟨⟨(↑u⁻¹ : L), -(↑u⁻¹ : L) ^ l * x.snd * ↑v⁻¹⟩, ?_⟩
  refine W2.ext ?_ ?_
  · change x.fst * (↑u⁻¹ : L) = 1
    rw [← hu]; simp
  · change x.fst ^ l * (-(↑u⁻¹ : L) ^ l * x.snd * ↑v⁻¹) + (↑u⁻¹ : L) ^ l * x.snd +
      (l : L) * x.snd * (-(↑u⁻¹ : L) ^ l * x.snd * ↑v⁻¹) = 0
    have hg : (↑v⁻¹ : L) * (x.fst ^ l + (l : L) * x.snd) = 1 := by
      change (↑v⁻¹ : L) * W2.gh x = 1
      rw [← hv]; simp
    linear_combination (-(↑u⁻¹ : L) ^ l * x.snd) * hg

/- English proof (translation)
Set `s0 : A →+* W2 l (Localization M)` to `(W2.map (algebraMap A (Localization M))).comp (deltaSectionToWittLengthTwo D)`. Establish `hs0 : ∀ m : M, IsUnit (s0 m)` using `fun m => by`. Apply `W2.isUnit_of_fst_gh` to reduce the goal to its premises. Conclude with `IsLocalization.map_units (Localization M) m`. Establish `: W2.gh (s0 m) = algebraMap A (Localization M) (D.φ m)`.

Rewrite using `[D.φ_eq]`. Express the relevant statement in the definitionally equal form `(algebraMap A _ m) ^ l + (l : Localization M) * algebraMap A _ (D.δ m) = _`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `IsLocalization.map_units (Localization M) (⟨D.φ m, hM m m.2⟩ : M)`.

Set `s : Localization M →+* W2 l (Localization M)` to `IsLocalization.lift hs0`. Establish `hsa : ∀ a : A, s (algebraMap A _ a) = s0 a` using `fun a => IsLocalization.lift_eq hs0 a`. Establish `hsec : ∀ y, (s y).fst = y` using `fun y => by`. Establish `: (W2.fstHom.comp s : Localization M →+* Localization M) = RingHom.id _` using `IsLocalization.ringHom_ext M (RingHom.ext fun a => by`. Simplify using `only [RingHom.comp_apply, RingHom.id_apply]`.

Rewrite using `[hsa]`. Use the proof step `rfl)`. Conclude with `RingHom.congr_fun this y`. Use `⟨deltaStructureOfWittLengthTwoSection s hsec, fun a => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap A _ (D.δ a) = (s (algebraMap A _ a)).snd`.

Rewrite using `[hsa]`. Both sides reduce to the same expression.
-/
theorem delta_localization (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A)
    (M : Submonoid A) (hM : ∀ x ∈ M, D.φ x ∈ M) :
    ∃ D' : Delta l (Localization M), IsδMap D D' (algebraMap A (Localization M)) := by
  let s0 : A →+* W2 l (Localization M) := (W2.map (algebraMap A (Localization M))).comp (deltaSectionToWittLengthTwo D)
  have hs0 : ∀ m : M, IsUnit (s0 m) := fun m => by
    apply W2.isUnit_of_fst_gh
    · exact IsLocalization.map_units (Localization M) m
    · have : W2.gh (s0 m) = algebraMap A (Localization M) (D.φ m) := by
        rw [D.φ_eq]; change (algebraMap A _ m) ^ l + (l : Localization M) * algebraMap A _ (D.δ m) = _
        simp
      rw [this]
      exact IsLocalization.map_units (Localization M) (⟨D.φ m, hM m m.2⟩ : M)
  let s : Localization M →+* W2 l (Localization M) := IsLocalization.lift hs0
  have hsa : ∀ a : A, s (algebraMap A _ a) = s0 a := fun a => IsLocalization.lift_eq hs0 a
  have hsec : ∀ y, (s y).fst = y := fun y => by
    have : (W2.fstHom.comp s : Localization M →+* Localization M) = RingHom.id _ :=
      IsLocalization.ringHom_ext M (RingHom.ext fun a => by
        simp only [RingHom.comp_apply, RingHom.id_apply]
        rw [hsa]; rfl)
    exact RingHom.congr_fun this y
  refine ⟨deltaStructureOfWittLengthTwoSection s hsec, fun a => ?_⟩
  change algebraMap A _ (D.δ a) = (s (algebraMap A _ a)).snd
  rw [hsa]; rfl

end GlobalTheory.BSP
