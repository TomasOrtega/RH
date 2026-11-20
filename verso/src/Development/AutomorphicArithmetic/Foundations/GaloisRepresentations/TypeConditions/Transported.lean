import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.N

namespace UpperTheory.GalS

open Classical in

def thr {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) : ℕ :=
  if ∃ p : ℕ, p.Prime ∧ w ∈ placesOver E p ∧ (placesOver E p).ncard = Module.finrank ℚ E ∧ (n = 1 ∨ 16 * n ^ 2 < p) then 2 else 1

/- English proof (translation)
Unfold `thr`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
theorem thr_pos {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {n : ℕ} : 0 < thr w n := by
  unfold thr
  split_ifs <;> norm_num

/- English proof (translation)
The claim follows from `if_pos ⟨p, hp, hw, hs, Or.inr hn⟩`.
-/
theorem thr_split {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {p : ℕ} (hp : p.Prime)
    (hw : w ∈ placesOver E p) (hs : (placesOver E p).ncard = Module.finrank ℚ E) {n : ℕ} (hn : 16 * n ^ 2 < p) :
    thr w n = 2 := if_pos ⟨p, hp, hw, hs, Or.inr hn⟩

/- English proof (translation)
Unfold `thr`. Distinguish the cases in `hm : ∃ p : ℕ, p.Prime ∧ w ∈ placesOver E p ∧ (placesOver E p).ncard = Module.finrank ℚ E ∧ (m = 1 ∨ 16 * m ^ 2 < p)`. Apply the tactic sequence `rw [if_pos hm] split_ifs <;> norm_num`. Rewrite using `[if_neg hm]`. Establish `hn : ¬ ∃ p : ℕ, p.Prime ∧ w ∈ placesOver E p ∧ (placesOver E p).ncard = Module.finrank ℚ E ∧ (n = 1 ∨ 16 * n ^ 2 < p)`.

Introduce and unpack `⟨p, hp, hw, hs, hc⟩`. Apply `hm` to reduce the goal to its premises. Use `⟨p, hp, hw, hs, ?_⟩` and prove the remaining obligations. Break down `hc with rfl | hc` into its components or cases. Use `interval_cases m`.

Use `right`. Simplify using `using hp.pos`. Use `left`. Both sides reduce to the same expression. Use `right`.

Establish `: m ^ 2 ≤ n ^ 2` using `Nat.pow_le_pow_left h 2`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg hn]`.
-/
theorem thr_anti {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {m n : ℕ} (h : m ≤ n) : thr w n ≤ thr w m := by
  unfold thr
  by_cases hm : ∃ p : ℕ, p.Prime ∧ w ∈ placesOver E p ∧ (placesOver E p).ncard = Module.finrank ℚ E ∧ (m = 1 ∨ 16 * m ^ 2 < p)
  · rw [if_pos hm]
    split_ifs <;> norm_num
  · rw [if_neg hm]
    have hn : ¬ ∃ p : ℕ, p.Prime ∧ w ∈ placesOver E p ∧ (placesOver E p).ncard = Module.finrank ℚ E ∧ (n = 1 ∨ 16 * n ^ 2 < p) := by
      rintro ⟨p, hp, hw, hs, hc⟩
      apply hm
      refine ⟨p, hp, hw, hs, ?_⟩
      rcases hc with rfl | hc
      · interval_cases m
        · right
          simpa using hp.pos
        · left
          rfl
      · right
        have : m ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left h 2
        omega
    rw [if_neg hn]

end UpperTheory.GalS
