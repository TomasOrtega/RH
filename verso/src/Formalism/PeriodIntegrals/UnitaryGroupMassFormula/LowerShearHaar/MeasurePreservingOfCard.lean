import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerShearHaar.TriShear

open MeasureTheory

noncomputable section

namespace PI.LowSplitHaarW

def extNe {ι : Type} [DecidableEq ι] (a : ι) (y : {i // i ≠ a} → ℂ) : ι → ℂ :=
  fun j => if h : j ≠ a then y ⟨j, h⟩ else 0

/- English proof (translation)
Use `measurable_pi_lambda _ fun j => ?_` and prove the remaining obligations. Distinguish the cases in `h : j ≠ a`. Simplify using `only [extNe, dif_pos h]`. Conclude with `measurable_pi_apply _`. Simplify using `only [extNe, dif_neg h]`.

Conclude with `measurable_const`.
-/
theorem measurable_extNe {ι : Type} [DecidableEq ι] (a : ι) : Measurable (extNe a) := by
  refine measurable_pi_lambda _ fun j => ?_
  by_cases h : j ≠ a
  · simp only [extNe, dif_pos h]
    exact measurable_pi_apply _
  · simp only [extNe, dif_neg h]
    exact measurable_const

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `ι _ _ hcard r g _ _`. Use `haveI : IsEmpty ι := Fintype.card_eq_zero_iff.1 hcard`. Establish `: (fun x : ι → ℂ => fun i => x i + g i x) = id`.

Use function extensionality and compare the values at `x i`. Conclude with `isEmptyElim i`. Rewrite using `[this]`. Conclude with `MeasurePreserving.id _`. Consider the case `succ n ih`.

Introduce `ι _ _ hcard r g hg hdep`. Use `haveI : Nonempty ι := Fintype.card_pos_iff.1 (by omega)`. Take `⟨a, -, ha⟩` from `Finset.exists_max_image Finset.univ r Finset.univ_nonempty`. Establish `hja : ∀ i j, r j < r i → j ≠ a`. Introduce and unpack `i j hj rfl`.

Conclude with `absurd (ha i (Finset.mem_univ _)) (not_le.2 hj)`. Establish `hext : ∀ (x : ι → ℂ) (i : ι), g i x = g i (extNe a (fun j : {j // j ≠ a} => x j))`. Introduce `x i`. Use `hdep i _ _ fun j hj => ?_` and prove the remaining obligations. Simplify using `[extNe, hja i j hj]`.

Establish `hcard' : Fintype.card {j // j ≠ a} = n`. Simplify using `[Fintype.card_subtype_compl, hcard]`. Establish `hF` using `ih {j // j ≠ a} hcard' (fun j => r j) (fun j y => g j (extNe a y)) (fun j => (hg j).comp (measurable_extNe a)) (by`. Introduce `j y z hyz`. Use `hdep j _ _ fun l hl => ?_` and prove the remaining obligations.

Distinguish the cases in `h : l ≠ a`. Simplify using `only [extNe, dif_pos h]`. Conclude with `hyz ⟨l, h⟩ hl`. Simplify using `only [extNe, dif_neg h])`. Set `e` to `MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℂ) (fun j => j ≠ a)`.

Establish `he : MeasurePreserving e volume volume` using `volume_preserving_piEquivPiSubtypeProd (fun _ : ι => ℂ) (fun j => j ≠ a)`. Establish `hG` using `hF.skew_product (g := fun y (z : {j // ¬ j ≠ a} → ℂ) => fun q => z q + g a (extNe a y)) (by`. Use `measurable_pi_lambda _ fun q => ?_` and prove the remaining obligations. Conclude with `((measurable_pi_apply q).comp measurable_snd).add ((hg a).comp ((measurable_extNe a).comp measurable_fst)))`. Use the proof step `(Filter.Eventually.of_forall fun y => (measurePreserving_add_right (volume : Measure ({j // ¬ j ≠ a} → ℂ)) (fun _ => g a (extNe a y))).map_eq)`.

Establish `key : (fun x : ι → ℂ => fun i => x i + g i x) = e.symm ∘ (fun p => ((fun i : {j // j ≠ a} => p.1 i + g i (extNe a p.1)), fun q : {j // ¬ j ≠ a} => p.2 q + g a (extNe a p.1))) ∘ e`. Use function extensionality and compare the values at `x i`. Distinguish the cases in `h : i ≠ a`. Simplify using `[e, h, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hext x i]`. Establish `h' : i = a` using `not_not.1 h`.

Substitute `h'` using the available equality. Simplify using `[e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hext x i]`. Rewrite using `[key]`. Conclude with `he.symm.comp (hG.comp he)`.
-/
theorem measurePreserving_of_card (n : ℕ) : ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = n →
    ∀ (r : ι → ℕ) (g : ι → (ι → ℂ) → ℂ), (∀ i, Measurable (g i)) →
    (∀ i (x y : ι → ℂ), (∀ j, r j < r i → x j = y j) → g i x = g i y) →
    MeasurePreserving (fun x : ι → ℂ => fun i => x i + g i x) volume volume := by
  induction n with
  | zero =>
    intro ι _ _ hcard r g _ _
    haveI : IsEmpty ι := Fintype.card_eq_zero_iff.1 hcard
    have : (fun x : ι → ℂ => fun i => x i + g i x) = id := by
      funext x i
      exact isEmptyElim i
    rw [this]
    exact MeasurePreserving.id _
  | succ n ih =>
    intro ι _ _ hcard r g hg hdep
    haveI : Nonempty ι := Fintype.card_pos_iff.1 (by omega)

    obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ r Finset.univ_nonempty
    have hja : ∀ i j, r j < r i → j ≠ a := by
      rintro i j hj rfl
      exact absurd (ha i (Finset.mem_univ _)) (not_le.2 hj)
    have hext : ∀ (x : ι → ℂ) (i : ι), g i x = g i (extNe a (fun j : {j // j ≠ a} => x j)) := by
      intro x i
      refine hdep i _ _ fun j hj => ?_
      simp [extNe, hja i j hj]
    have hcard' : Fintype.card {j // j ≠ a} = n := by
      simp [Fintype.card_subtype_compl, hcard]

    have hF := ih {j // j ≠ a} hcard' (fun j => r j) (fun j y => g j (extNe a y))
      (fun j => (hg j).comp (measurable_extNe a)) (by
        intro j y z hyz
        refine hdep j _ _ fun l hl => ?_
        by_cases h : l ≠ a
        · simp only [extNe, dif_pos h]
          exact hyz ⟨l, h⟩ hl
        · simp only [extNe, dif_neg h])
    let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℂ) (fun j => j ≠ a)
    have he : MeasurePreserving e volume volume :=
      volume_preserving_piEquivPiSubtypeProd (fun _ : ι => ℂ) (fun j => j ≠ a)

    have hG := hF.skew_product (g := fun y (z : {j // ¬ j ≠ a} → ℂ) => fun q => z q + g a (extNe a y))
      (by
        refine measurable_pi_lambda _ fun q => ?_
        exact ((measurable_pi_apply q).comp measurable_snd).add
          ((hg a).comp ((measurable_extNe a).comp measurable_fst)))
      (Filter.Eventually.of_forall fun y =>
        (measurePreserving_add_right (volume : Measure ({j // ¬ j ≠ a} → ℂ))
          (fun _ => g a (extNe a y))).map_eq)
    have key : (fun x : ι → ℂ => fun i => x i + g i x) =
        e.symm ∘ (fun p => ((fun i : {j // j ≠ a} => p.1 i + g i (extNe a p.1)),
          fun q : {j // ¬ j ≠ a} => p.2 q + g a (extNe a p.1))) ∘ e := by
      funext x i
      by_cases h : i ≠ a
      · simp [e, h, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hext x i]
      · have h' : i = a := not_not.1 h
        subst h'
        simp [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hext x i]
    rw [key]
    exact he.symm.comp (hG.comp he)

/- English proof (translation)
Introduce `ι _ _ r g hg hdep`. Conclude with `measurePreserving_of_card (Fintype.card ι) ι rfl r g hg hdep`.
-/
theorem triShear : TriShear := by
  intro ι _ _ r g hg hdep
  exact measurePreserving_of_card (Fintype.card ι) ι rfl r g hg hdep

end PI.LowSplitHaarW
