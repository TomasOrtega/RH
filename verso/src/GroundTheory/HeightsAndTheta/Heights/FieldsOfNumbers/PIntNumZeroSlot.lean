import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open GroundTheory.Heights₂.Heights.NumbersDVR Filter

universe u

section

variable {K : Type*}

/- English proof (translation)
Use function extensionality and compare the values at `m`. Simplify using `[diffStep]`.
-/
theorem diffStep_zero_left (h : (K → ℤ) → ℤ) : diffStep 0 h = 0 := by
  funext m
  simp [diffStep]

/- English proof (translation)
Use function extensionality and compare the values at `m`. Simplify using `[diffStep]`.
-/
theorem diffStep_zero_right (b : K → ℤ) : diffStep b (0 : (K → ℤ) → ℤ) = 0 := by
  funext m
  simp [diffStep]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp at hl`. Consider the case `cons a t ih`. Rewrite using `[List.foldr_cons]`. Break down `List.mem_cons.mp hl with rfl | ht` into its components or cases.

Conclude with `diffStep_zero_left _`. Rewrite using `[ih ht]`. Conclude with `diffStep_zero_right a`.
-/
theorem foldr_diffStep_eq_zero_of_mem (l : List (K → ℤ)) (hl : (0 : K → ℤ) ∈ l)
    (h : (K → ℤ) → ℤ) : l.foldr diffStep h = 0 := by
  induction l with
  | nil => simp at hl
  | cons a t ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp hl with rfl | ht
    · exact diffStep_zero_left _
    · rw [ih ht]
      exact diffStep_zero_right a

/- English proof (translation)
The claim follows from `foldr_diffStep_eq_zero_of_mem _ (List.mem_ofFn.mpr ⟨i, hi⟩) h`.
-/
theorem mixedDiff_coord_zero {n : ℕ} (bs : Fin n → K → ℤ) (i : Fin n) (hi : bs i = 0)
    (h : (K → ℤ) → ℤ) : mixedDiff bs h = 0 :=
  foldr_diffStep_eq_zero_of_mem _ (List.mem_ofFn.mpr ⟨i, hi⟩) h

/- English proof (translation)
Establish `hs : ∀ᶠ m in atTop, h (m + -b) = 0` using `(tendsto_atTop_add_const_right atTop (-b) tendsto_id).eventually hh`. Use `filter_upwards [hh, hs] with m h1 h2`. Simplify using `only [diffStep, h1, ← sub_eq_add_neg] at h2 ⊢`. Rewrite using `[h2, sub_zero]`.
-/
theorem diffStep_eventually_zero {b : K → ℤ} {h : (K → ℤ) → ℤ}
    (hh : ∀ᶠ m in atTop, h m = 0) : ∀ᶠ m in atTop, diffStep b h m = 0 := by
  have hs : ∀ᶠ m in atTop, h (m + -b) = 0 :=
    (tendsto_atTop_add_const_right atTop (-b) tendsto_id).eventually hh
  filter_upwards [hh, hs] with m h1 h2
  simp only [diffStep, h1, ← sub_eq_add_neg] at h2 ⊢
  rw [h2, sub_zero]

/- English proof (translation)
Unfold `mixedDiff`. Proceed by induction on `List.ofFn bs with`. Consider the case `nil => simpa using hh`. Consider the case `cons a t ih => exact diffStep_eventually_zero ih`.
-/
theorem mixedDiff_eventually_zero {n : ℕ} (bs : Fin n → K → ℤ) {h : (K → ℤ) → ℤ}
    (hh : ∀ᶠ m in atTop, h m = 0) : ∀ᶠ m in atTop, mixedDiff bs h m = 0 := by
  unfold mixedDiff
  induction List.ofFn bs with
  | nil => simpa using hh
  | cons a t ih => exact diffStep_eventually_zero ih

/- English proof (translation)
Unfold `eventualValue`. Establish `hex : ∃ c, ∀ᶠ m in atTop, f m = c` using `⟨0, hf⟩`. Rewrite using `[dif_pos hex]`. Take `⟨m, h1, h2⟩` from `(hex.choose_spec.and hf).exists`. Rewrite using `[← h1, h2]`.
-/
theorem eventualValue_eq_zero {f : (K → ℤ) → ℤ} (hf : ∀ᶠ m in atTop, f m = 0) :
    eventualValue f = 0 := by
  unfold eventualValue
  have hex : ∃ c, ∀ᶠ m in atTop, f m = c := ⟨0, hf⟩
  rw [dif_pos hex]
  obtain ⟨m, h1, h2⟩ := (hex.choose_spec.and hf).exists
  rw [← h1, h2]

end

/- English proof (translation)
Rewrite `h1`, `h2` using `[← WithBot.coe_natCast, ← WithTop.coe_natCast]`. Proceed by induction on `x using WithBot.recBotCoe with`. Consider the case `bot => exact absurd h1 (not_le.mpr (WithBot.bot_lt_coe _))`. Consider the case `coe y`. Proceed by induction on `y using WithTop.recTopCoe with`.

Consider the case `top => exact absurd h2 (not_lt.mpr (WithBot.coe_le_coe.mpr le_top))`. Consider the case `coe z`. Establish `hz : (t : ℤ) ≤ z` using `WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp h1)`. Use `⟨z.toNat, ?_⟩` and prove the remaining obligations. Rewrite using `[← WithBot.coe_natCast, ← WithTop.coe_natCast, Int.toNat_of_nonneg (by omega)]`.
-/
theorem exists_nat_of_le_of_lt {x : WithBot (WithTop ℤ)} {t n : ℕ}
    (h1 : (t : WithBot (WithTop ℤ)) ≤ x) (h2 : x < n) : ∃ d : ℕ, x = d := by
  rw [← WithBot.coe_natCast, ← WithTop.coe_natCast] at h1 h2
  induction x using WithBot.recBotCoe with
  | bot => exact absurd h1 (not_le.mpr (WithBot.bot_lt_coe _))
  | coe y =>
    induction y using WithTop.recTopCoe with
    | top => exact absurd h2 (not_lt.mpr (WithBot.coe_le_coe.mpr le_top))
    | coe z =>
      have hz : (t : ℤ) ≤ z := WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp h1)
      refine ⟨z.toNat, ?_⟩
      rw [← WithBot.coe_natCast, ← WithTop.coe_natCast, Int.toNat_of_nonneg (by omega)]

/- English proof (translation)
Introduce `F _ K _ _ ι _ I`. Use `⟨fun n bs i hi => ?_, fun hI n bs hn => ?_⟩` and prove the remaining obligations. Unfold `intNum`. Use `eventualValue_eq_zero (Eventually.of_forall fun m => ?_)` and prove the remaining obligations. Rewrite using `[mixedDiff_coord_zero bs i hi]`.

Both sides reduce to the same expression. Unfold `intNum`. Apply `eventualValue_eq_zero` to reduce the goal to its premises. Distinguish the cases in `hR : IsRelevant I`. Distinguish the cases in `hd : ∃ d : ℕ, relDim I = d`.

Take `⟨d, hd⟩` from `hd`. Establish `hdn : d < n`. Rewrite `hn` using `[hd]`. Conclude with `hn` after adjusting the coercions. Conclude with `(h₁ F K ι I hI hR d hd).2 n hdn bs`.

Take `⟨p, hp⟩` from `h₂ F K ι I hI`. Establish `hp0 : p = 0`. Assume the negation of the conclusion as `hne`. Conclude with `hd (exists_nat_of_le_of_lt ((h₃ F K ι I hI).1 hR p hp hne) hn)`. Apply `mixedDiff_eventually_zero` to reduce the goal to its premises.

Use `filter_upwards [hp] with m hm`. Rewrite `hm` using `[hp0, map_zero]`. Conclude with `hm` after adjusting the coercions. Conclude with `mixedDiff_eventually_zero bs ((h₃ F K ι I hI).2 hR)`.
-/
theorem IntNumZeroSlot.proof (h₁ : MixedDiffConst.Statement.{u})
    (h₂ : HilbEventuallyPoly.Statement.{u}) (h₃ : HilbDegreeBound.Statement.{u}) :
    IntNumZeroSlot.Statement.{u} := by
  intro F _ K _ _ ι _ I
  refine ⟨fun n bs i hi => ?_, fun hI n bs hn => ?_⟩
  · unfold intNum
    refine eventualValue_eq_zero (Eventually.of_forall fun m => ?_)
    rw [mixedDiff_coord_zero bs i hi]
    rfl
  · unfold intNum
    apply eventualValue_eq_zero
    by_cases hR : IsRelevant I
    · by_cases hd : ∃ d : ℕ, relDim I = d
      · obtain ⟨d, hd⟩ := hd
        have hdn : d < n := by
          rw [hd] at hn
          exact_mod_cast hn
        exact (h₁ F K ι I hI hR d hd).2 n hdn bs
      · obtain ⟨p, hp⟩ := h₂ F K ι I hI
        have hp0 : p = 0 := by
          by_contra hne
          exact hd (exists_nat_of_le_of_lt ((h₃ F K ι I hI).1 hR p hp hne) hn)
        apply mixedDiff_eventually_zero
        filter_upwards [hp] with m hm
        rw [hp0, map_zero] at hm
        exact_mod_cast hm
    · exact mixedDiff_eventually_zero bs ((h₃ F K ι I hI).2 hR)

end GroundTheory.Heights₂.Heights.FieldNumbers
