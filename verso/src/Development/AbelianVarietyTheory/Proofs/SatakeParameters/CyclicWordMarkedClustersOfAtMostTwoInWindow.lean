import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

/- English proof (translation)
Distinguish the cases in `h : ∃ q : ℕ, 1 ≤ q ∧ q ≤ j ∧ th (x + q)`. Take `⟨h1, h2, h3⟩` from `Nat.find_spec h`. Use `⟨Nat.find h, h2, fun h0 => absurd h0 (by omega), fun _ => h3, ?_⟩` and prove the remaining obligations. Introduce `q hq hqs hth`. Conclude with `Nat.find_min h hqs ⟨hq, by omega, hth⟩`.

Use `push_neg at h`. Use `⟨0, Nat.zero_le _, fun _ q hq hqj hth => absurd hth (h q hq hqj), fun h0 => absurd h0 (lt_irrefl 0), fun q hq hq0 => absurd hq0 (by omega)⟩` and prove the remaining obligations.
-/
theorem winClusters_exists_step {n : ℕ} (th : ZMod n → Prop) (j : ℕ) (x : ZMod n) :
    ∃ s : ℕ, s ≤ j ∧ (s = 0 → ∀ q : ℕ, 1 ≤ q → q ≤ j → ¬ th (x + q)) ∧ (0 < s → th (x + s)) ∧
      ∀ q : ℕ, 0 < q → q < s → ¬ th (x + q) := by
  classical
  by_cases h : ∃ q : ℕ, 1 ≤ q ∧ q ≤ j ∧ th (x + q)
  · obtain ⟨h1, h2, h3⟩ := Nat.find_spec h
    refine ⟨Nat.find h, h2, fun h0 => absurd h0 (by omega), fun _ => h3, ?_⟩
    intro q hq hqs hth
    exact Nat.find_min h hqs ⟨hq, by omega, hth⟩
  · push_neg at h
    refine ⟨0, Nat.zero_le _, fun _ q hq hqj hth => absurd hth (h q hq hqj), fun h0 => absurd h0 (lt_irrefl 0),
      fun q hq hq0 => absurd hq0 (by omega)⟩

/- English proof (translation)
Introduce `n th L j _ hL hn hW`. Use `choose sp hsp using winClusters_exists_step th j`. Use `set F : Set (ZMod n) := {x | th x ∧ ∀ q : ℕ, 1 ≤ q → q ≤ j → ¬ th (x - q)} with hFdef`. Establish `key : ∀ x1 x2 : ZMod n, x1 ∈ F → x2 ∈ F → ∀ s1 s2 : ℕ, s1 ≤ s2 → s2 ≤ j → x1 + s1 = x2 + s2 → x1 = x2`. Introduce `x1 x2 hx1 hx2 s1 s2 hs hs2 he`.

Break down `Nat.lt_or_ge s1 s2 with hlt | hge` into its components or cases. It suffices to derive a contradiction. Apply `hx1.2 (s2 - s1) (by omega) (by omega)` to reduce the goal to its premises. Establish `: x1 - ((s2 - s1 : ℕ) : ZMod n) = x2`. Rewrite using `[Nat.cast_sub hs]`.

Take the linear combination `he`. Rewrite using `[this]`. Conclude with `hx2.1`. Establish `: s1 = s2` using `le_antisymm hs hge`. Substitute `this` using the available equality.

Conclude with `add_right_cancel he`. Establish `ofCl : ∀ x y : ZMod n, (y = x ∨ y = x + (sp x : ZMod n)) → ∃ s : ℕ, s ≤ j ∧ y = x + s`. Introduce `x y h`. Break down `h with h | h` into its components or cases. Conclude with `⟨0, Nat.zero_le _, by simp [h]⟩`.

Conclude with `⟨sp x, (hsp x).1, h⟩`. Use `⟨F, sp, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `x ⟨hx, hxF⟩`. Take `⟨h1, _, h3, h4⟩` from `hsp x`. Use `⟨hx, h1, by omega, ?_, h4, hxF⟩` and prove the remaining obligations.

Break down `Nat.eq_zero_or_pos (sp x) with h | h` into its components or cases. Rewrite using `[h]`. Simplify using `using hx`. Conclude with `h3 h`. Introduce `y hy`.

Establish `ex : ∃ x, x ∈ F ∧ (y = x ∨ y = x + (sp x : ZMod n))`. Distinguish the cases in `hyF : ∀ q : ℕ, 1 ≤ q → q ≤ j → ¬ th (y - q)`. Conclude with `⟨y, ⟨hy, hyF⟩, Or.inl rfl⟩`. Use `push_neg at hyF`. Take `⟨q, hq1, hqj, hq⟩` from `hyF`.

Establish `hxF : y - (q : ZMod n) ∈ F`. Use `⟨hq, ?_⟩` and prove the remaining obligations. Introduce `q' hq'1 hq'j hth`. Apply `hW (y - q - q') 0 q' (q' + q) (by omega) (by omega) (by omega)` to reduce the goal to its premises. Use `⟨by simpa using hth, ?_, ?_⟩` and prove the remaining obligations.

Establish `: y - (q : ZMod n) - q' + (q' : ℕ) = y - q` using `by ring`. Rewrite using `[this]`. Conclude with `hq`. Establish `: y - (q : ZMod n) - q' + ((q' + q : ℕ) : ZMod n) = y` using `by push_cast; ring`. Rewrite using `[this]`.

Conclude with `hy`. Establish `hyx : y - (q : ZMod n) + (q : ZMod n) = y` using `by ring`. Take `⟨h1, h2, h3, h4⟩` from `hsp (y - q)`. Establish `hspq : sp (y - q) = q`. Break down `Nat.eq_zero_or_pos (sp (y - q)) with h0 | hpos` into its components or cases.

Conclude with `absurd (by rw [hyx]; exact hy) (h2 h0 q hq1 hqj)`. Break down `lt_trichotomy (sp (y - q)) q with hlt | heq | hgt` into its components or cases. It suffices to derive a contradiction. Apply `hW (y - q) 0 (sp (y - q)) q hpos hlt (by omega)` to reduce the goal to its premises. Use `⟨by simpa using hq, h3 hpos, ?_⟩` and prove the remaining obligations.

Rewrite using `[hyx]`. Conclude with `hy`. Conclude with `heq`. Conclude with `absurd (by rw [hyx]; exact hy) (h4 q (by omega) hgt)`. Use `⟨y - q, hxF, Or.inr ?_⟩` and prove the remaining obligations.

Rewrite using `[hspq, hyx]`. Take `⟨x, hxF, hx⟩` from `ex`. Use `⟨x, ⟨hxF, hx⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `z ⟨hzF, hz⟩`. Take `⟨s1, hs1, e1⟩` from `ofCl z y hz`.

Take `⟨s2, hs2, e2⟩` from `ofCl x y hx`. Break down `le_total s1 s2 with h | h` into its components or cases. Conclude with `key z x hzF hxF s1 s2 h hs2 (e1.symm.trans e2)`. Conclude with `(key x z hxF hzF s2 s1 h hs1 (e2.symm.trans e1)).symm`.
-/
theorem winClusters : ∀ {n : ℕ} (th : ZMod n → Prop) (L j : ℕ), 1 ≤ j → 2 * j + 1 ≤ L → 2 * j < n →
    WindowTwo th L → Clusters th j := by
  intro n th L j _ hL hn hW
  choose sp hsp using winClusters_exists_step th j
  set F : Set (ZMod n) := {x | th x ∧ ∀ q : ℕ, 1 ≤ q → q ≤ j → ¬ th (x - q)} with hFdef
  have key : ∀ x1 x2 : ZMod n, x1 ∈ F → x2 ∈ F → ∀ s1 s2 : ℕ, s1 ≤ s2 → s2 ≤ j →
      x1 + s1 = x2 + s2 → x1 = x2 := by
    intro x1 x2 hx1 hx2 s1 s2 hs hs2 he
    rcases Nat.lt_or_ge s1 s2 with hlt | hge
    · exfalso
      apply hx1.2 (s2 - s1) (by omega) (by omega)
      have : x1 - ((s2 - s1 : ℕ) : ZMod n) = x2 := by
        rw [Nat.cast_sub hs]
        linear_combination he
      rw [this]; exact hx2.1
    · have : s1 = s2 := le_antisymm hs hge
      subst this
      exact add_right_cancel he
  have ofCl : ∀ x y : ZMod n, (y = x ∨ y = x + (sp x : ZMod n)) → ∃ s : ℕ, s ≤ j ∧ y = x + s := by
    intro x y h
    rcases h with h | h
    · exact ⟨0, Nat.zero_le _, by simp [h]⟩
    · exact ⟨sp x, (hsp x).1, h⟩
  refine ⟨F, sp, ?_, ?_⟩
  · rintro x ⟨hx, hxF⟩
    obtain ⟨h1, _, h3, h4⟩ := hsp x
    refine ⟨hx, h1, by omega, ?_, h4, hxF⟩
    rcases Nat.eq_zero_or_pos (sp x) with h | h
    · rw [h]; simpa using hx
    · exact h3 h
  · intro y hy
    have ex : ∃ x, x ∈ F ∧ (y = x ∨ y = x + (sp x : ZMod n)) := by
      by_cases hyF : ∀ q : ℕ, 1 ≤ q → q ≤ j → ¬ th (y - q)
      · exact ⟨y, ⟨hy, hyF⟩, Or.inl rfl⟩
      · push_neg at hyF
        obtain ⟨q, hq1, hqj, hq⟩ := hyF
        have hxF : y - (q : ZMod n) ∈ F := by
          refine ⟨hq, ?_⟩
          intro q' hq'1 hq'j hth
          apply hW (y - q - q') 0 q' (q' + q) (by omega) (by omega) (by omega)
          refine ⟨by simpa using hth, ?_, ?_⟩
          · have : y - (q : ZMod n) - q' + (q' : ℕ) = y - q := by ring
            rw [this]; exact hq
          · have : y - (q : ZMod n) - q' + ((q' + q : ℕ) : ZMod n) = y := by push_cast; ring
            rw [this]; exact hy
        have hyx : y - (q : ZMod n) + (q : ZMod n) = y := by ring
        obtain ⟨h1, h2, h3, h4⟩ := hsp (y - q)
        have hspq : sp (y - q) = q := by
          rcases Nat.eq_zero_or_pos (sp (y - q)) with h0 | hpos
          · exact absurd (by rw [hyx]; exact hy) (h2 h0 q hq1 hqj)
          rcases lt_trichotomy (sp (y - q)) q with hlt | heq | hgt
          · exfalso
            apply hW (y - q) 0 (sp (y - q)) q hpos hlt (by omega)
            refine ⟨by simpa using hq, h3 hpos, ?_⟩
            rw [hyx]; exact hy
          · exact heq
          · exact absurd (by rw [hyx]; exact hy) (h4 q (by omega) hgt)
        refine ⟨y - q, hxF, Or.inr ?_⟩
        rw [hspq, hyx]
    obtain ⟨x, hxF, hx⟩ := ex
    refine ⟨x, ⟨hxF, hx⟩, ?_⟩
    rintro z ⟨hzF, hz⟩
    obtain ⟨s1, hs1, e1⟩ := ofCl z y hz
    obtain ⟨s2, hs2, e2⟩ := ofCl x y hx
    rcases le_total s1 s2 with h | h
    · exact key z x hzF hxF s1 s2 h hs2 (e1.symm.trans e2)
    · exact (key x z hxF hzF s2 s1 h hs1 (e2.symm.trans e1)).symm

end GlobalTheory.HTW
