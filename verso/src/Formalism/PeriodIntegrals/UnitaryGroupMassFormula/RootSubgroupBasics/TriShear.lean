import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupBasics.TriDefs

open MeasureTheory

noncomputable section

namespace PI.AmpRootCommon.Tri

def extNe {ι : Type} [DecidableEq ι] (a : ι) (y : {i // i ≠ a} → ℂ) : ι → ℂ :=
  fun j => if h : j ≠ a then y ⟨j, h⟩ else 0

/- English proof (translation)
Use `measurable_pi_lambda _ (fun j => ?_)` and prove the remaining obligations. Distinguish the cases in `h : j ≠ a`. Simplify using `only [extNe, dif_pos h]`. Conclude with `measurable_pi_apply _`. Simplify using `only [extNe, dif_neg h]`.

Conclude with `measurable_const`.
-/
theorem measurable_extNe {ι : Type} [DecidableEq ι] (a : ι) : Measurable (extNe a) := by
  refine measurable_pi_lambda _ (fun j => ?_)
  by_cases h : j ≠ a
  · simp only [extNe, dif_pos h]
    exact measurable_pi_apply _
  · simp only [extNe, dif_neg h]
    exact measurable_const

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `ι _ _ hcard r g hg hdep`. Establish `: IsEmpty ι` using `Fintype.card_eq_zero_iff.mp hcard`. Establish `hid : (fun x : ι → ℂ => fun i => x i + g i x) = id`.

Use function extensionality and compare the values at `fun x => funext fun i => isEmptyElim i`. Rewrite using `[hid]`. Conclude with `MeasurePreserving.id _`. Consider the case `succ n ih`. Introduce `ι _ _ hcard r g hg hdep`.

Establish `: Nonempty ι` using `Fintype.card_pos_iff.mp (by omega)`. Take `⟨a, ha⟩` from `Finite.exists_max r`. Establish `hcard' : Fintype.card {i // i ≠ a} = n`. Rewrite using `[Fintype.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, hcard]`. Both sides reduce to the same expression.

Establish `hext : ∀ i (x : ι → ℂ), g i x = g i (extNe a (fun j : {j // j ≠ a} => x j.1))`. Introduce `i x`. Apply `hdep i` to reduce the goal to its premises. Introduce `j hj`. Distinguish the cases in `hja : j ≠ a`.

Simplify using `only [extNe, dif_pos hja]`. Establish `hja' : j = a` using `not_not.mp hja`. Rewrite `hj` using `[hja']`. Use `ha i` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hT` using `ih {i // i ≠ a} hcard' (fun i => r i.1) (fun i y => g i.1 (extNe a y)) (fun i => (hg i.1).comp (measurable_extNe a)) (fun i y y' hyy' => hdep i.1 _ _ (fun j hj => by`. Distinguish the cases in `hja : j ≠ a`. Simplify using `only [extNe, dif_pos hja]`. Conclude with `hyy' ⟨j, hja⟩ hj`. Simplify using `only [extNe, dif_neg hja]))`.

Establish `hc : Measurable (fun (y : {i // i ≠ a} → ℂ) (_ : {i // ¬ i ≠ a}) => g a (extNe a y))` using `measurable_pi_lambda _ fun _ => (hg a).comp (measurable_extNe a)`. Establish `hS : MeasurePreserving (fun p : ({i // i ≠ a} → ℂ) × ({i // ¬ i ≠ a} → ℂ) => ((fun i => p.1 i + g i.1 (extNe a p.1)), p.2 + fun (_ : {i // ¬ i ≠ a}) => g a (extNe a p.1))) volume volume` using `hT.skew_product (g := fun y z => z + fun (_ : {i // ¬ i ≠ a}) => g a (extNe a y)) (measurable_snd.add (hc.comp measurable_fst)) (ae_of_all _ fun y => map_add_right_eq_self volume _)`. Establish `hΦ` using `volume_preserving_piEquivPiSubtypeProd (fun _ : ι => ℂ) (fun i => i ≠ a)`. Establish `hF : (fun x : ι → ℂ => fun i => x i + g i x) = (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℂ) (fun i => i ≠ a)).symm ∘ (fun p : ({i // i ≠ a} → ℂ) × ({i // ¬ i ≠ a} → ℂ) => ((fun i => p.1 i + g i.1 (extNe a p.1)), p.2 + fun (_ : {i // ¬ i ≠ a}) => g a (extNe a p.1))) ∘ (M …`. Use function extensionality and compare the values at `x i`.

Use `show x i + g i x = (if h : i ≠ a then _ else _)`. Distinguish the cases in `hi : i ≠ a`. Rewrite using `[dif_pos hi] show x i + g i x = x i + g i (extNe a (fun j : {j // j ≠ a} => x j.1))`. Rewrite using `[← hext i x]`. Rewrite using `[dif_neg hi] show x i + g i x = x i + g a (extNe a (fun j : {j // j ≠ a} => x j.1))`.

Establish `hia : i = a` using `not_not.mp hi`. Rewrite using `[hia, ← hext a x]`. Rewrite using `[hF]`. Conclude with `(MeasurePreserving.symm _ hΦ).comp (hS.comp hΦ)`.
-/
theorem measurePreserving_of_card (n : ℕ) : ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = n →
    ∀ (r : ι → ℕ) (g : ι → (ι → ℂ) → ℂ), (∀ i, Measurable (g i)) →
    (∀ i (x y : ι → ℂ), (∀ j, r j < r i → x j = y j) → g i x = g i y) →
    MeasurePreserving (fun x : ι → ℂ => fun i => x i + g i x) volume volume := by
  induction n with
  | zero =>
    intro ι _ _ hcard r g hg hdep
    have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hcard
    have hid : (fun x : ι → ℂ => fun i => x i + g i x) = id :=
      funext fun x => funext fun i => isEmptyElim i
    rw [hid]
    exact MeasurePreserving.id _
  | succ n ih =>
    intro ι _ _ hcard r g hg hdep
    have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨a, ha⟩ := Finite.exists_max r
    have hcard' : Fintype.card {i // i ≠ a} = n := by
      rw [Fintype.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ a),
        Finset.card_univ, hcard]
      rfl
    have hext : ∀ i (x : ι → ℂ), g i x = g i (extNe a (fun j : {j // j ≠ a} => x j.1)) := by
      intro i x
      apply hdep i
      intro j hj
      by_cases hja : j ≠ a
      · simp only [extNe, dif_pos hja]
      · have hja' : j = a := not_not.mp hja
        rw [hja'] at hj
        have := ha i
        omega
    have hT := ih {i // i ≠ a} hcard' (fun i => r i.1)
      (fun i y => g i.1 (extNe a y))
      (fun i => (hg i.1).comp (measurable_extNe a))
      (fun i y y' hyy' => hdep i.1 _ _ (fun j hj => by
        by_cases hja : j ≠ a
        · simp only [extNe, dif_pos hja]
          exact hyy' ⟨j, hja⟩ hj
        · simp only [extNe, dif_neg hja]))
    have hc : Measurable (fun (y : {i // i ≠ a} → ℂ) (_ : {i // ¬ i ≠ a}) => g a (extNe a y)) :=
      measurable_pi_lambda _ fun _ => (hg a).comp (measurable_extNe a)
    have hS : MeasurePreserving
        (fun p : ({i // i ≠ a} → ℂ) × ({i // ¬ i ≠ a} → ℂ) =>
          ((fun i => p.1 i + g i.1 (extNe a p.1)),
            p.2 + fun (_ : {i // ¬ i ≠ a}) => g a (extNe a p.1))) volume volume :=
      hT.skew_product (g := fun y z => z + fun (_ : {i // ¬ i ≠ a}) => g a (extNe a y))
        (measurable_snd.add (hc.comp measurable_fst))
        (ae_of_all _ fun y => map_add_right_eq_self volume _)
    have hΦ := volume_preserving_piEquivPiSubtypeProd (fun _ : ι => ℂ) (fun i => i ≠ a)
    have hF : (fun x : ι → ℂ => fun i => x i + g i x) =
        (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℂ) (fun i => i ≠ a)).symm ∘
          (fun p : ({i // i ≠ a} → ℂ) × ({i // ¬ i ≠ a} → ℂ) =>
            ((fun i => p.1 i + g i.1 (extNe a p.1)),
              p.2 + fun (_ : {i // ¬ i ≠ a}) => g a (extNe a p.1))) ∘
          (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℂ) (fun i => i ≠ a)) := by
      funext x i
      show x i + g i x = (if h : i ≠ a then _ else _)
      by_cases hi : i ≠ a
      · rw [dif_pos hi]
        show x i + g i x = x i + g i (extNe a (fun j : {j // j ≠ a} => x j.1))
        rw [← hext i x]
      · rw [dif_neg hi]
        show x i + g i x = x i + g a (extNe a (fun j : {j // j ≠ a} => x j.1))
        have hia : i = a := not_not.mp hi
        rw [hia, ← hext a x]
    rw [hF]
    exact (MeasurePreserving.symm _ hΦ).comp (hS.comp hΦ)

/- English proof (translation)
Introduce `ι _ _ r g hg hdep` and use `measurePreserving_of_card (Fintype.card ι) ι rfl r g hg hdep`.
-/
theorem triShear : TriShear :=
  fun ι _ _ r g hg hdep => measurePreserving_of_card (Fintype.card ι) ι rfl r g hg hdep

end PI.AmpRootCommon.Tri
