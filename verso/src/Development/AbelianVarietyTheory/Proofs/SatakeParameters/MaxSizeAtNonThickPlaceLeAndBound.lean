import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FloorSizeBoundsNotThickEmbeddingStatement
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

/- English proof (translation)
Introduce `D L C hR`. Establish `hb : (0 : ℝ) ≤ L.sc.b'`. Take `⟨-, h1, -, h3, -⟩` from `hR`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hmem : ∀ s ∈ {s : ℕ | ∃ (g : D.R.GG) (j : Fin D.R.m), ¬ Thick D.host g ∧ s = ⌊(hcAt D g).e j⌋.toNat}, (s : ℝ) ≤ 8 / 5 * L.sc.b'`.

Introduce and unpack `s ⟨g, j, hg, rfl⟩`. Take `⟨h1, h2⟩` from `GlobalTheory.T.floor_size_bounds_not_thick_embedding L C g j hR hg`. Establish `h100 : (100 : ℝ) ≤ L.sc.w'' D.R.n` using `hR.2.1`. Establish `hpos : (0 : ℤ) ≤ ⌊(hcAt D g).e j⌋`. Establish `: (0 : ℝ) ≤ (⌊(hcAt D g).e j⌋ : ℝ)` using `by linarith`.

Conclude with `this` after adjusting the coercions. Establish `: ((⌊(hcAt D g).e j⌋.toNat : ℤ) : ℝ) = (⌊(hcAt D g).e j⌋ : ℝ)`. Rewrite using `[Int.toNat_of_nonneg hpos]`. Establish `h' : ((⌊(hcAt D g).e j⌋.toNat : ℕ) : ℝ) = (⌊(hcAt D g).e j⌋ : ℝ)`. Rewrite using `[← this]`.

Use `norm_cast`. Rewrite using `[h']`. Conclude with `h2`. Establish `hbdd : BddAbove {s : ℕ | ∃ (g : D.R.GG) (j : Fin D.R.m), ¬ Thick D.host g ∧ s = ⌊(hcAt D g).e j⌋.toNat}`. Use `⟨⌊8 / 5 * L.sc.b'⌋₊, fun s hs => ?_⟩` and prove the remaining obligations.

Conclude with `Nat.le_floor (hmem s hs)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `wMax`. Break down `Set.eq_empty_or_nonempty {s : ℕ | ∃ (g : D.R.GG) (j : Fin D.R.m), ¬ Thick D.host g ∧ s = ⌊(hcAt D g).e j⌋.toNat} with he | hne` into its components or cases. Rewrite using `[he, csSup_empty]`.

Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨s, hs, hseq⟩ : ∃ s ∈ {s : ℕ | ∃ (g : D.R.GG) (j : Fin D.R.m), ¬ Thick D.host g ∧ s = ⌊(hcAt D g).e j⌋.toNat}, s = sSup {s : ℕ | ∃ (g : D.R.GG) (j : Fin D.R.m), ¬ Thick D.host g ∧ s = ⌊(hcAt D g).e j⌋.toNat}` from `⟨_, Nat.sSup_mem hne hbdd, rfl⟩`. Rewrite using `[← hseq]`. Conclude with `hmem s hs`.

Introduce `g j hg`. Establish `h1 : ⌊(hcAt D g).e j⌋.toNat ≤ wMax D` using `le_csSup hbdd ⟨g, j, hg, rfl⟩`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem wMax_le_and_ge : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ), Roomy L C → (wMax D : ℝ) ≤ 8 / 5 * L.sc.b' ∧ ∀ (g : D.R.GG) (j : Fin D.R.m), ¬ Thick D.host g → ⌊(hcAt D g).e j⌋ ≤ (wMax D : ℤ) := by
  intro D L C hR
  have hb : (0 : ℝ) ≤ L.sc.b' := by
    obtain ⟨-, h1, -, h3, -⟩ := hR
    linarith
  have hmem : ∀ s ∈ {s : ℕ | ∃ (g : D.R.GG) (j : Fin D.R.m), ¬ Thick D.host g ∧ s = ⌊(hcAt D g).e j⌋.toNat},
      (s : ℝ) ≤ 8 / 5 * L.sc.b' := by
    rintro s ⟨g, j, hg, rfl⟩
    obtain ⟨h1, h2⟩ := GlobalTheory.T.floor_size_bounds_not_thick_embedding L C g j hR hg
    have h100 : (100 : ℝ) ≤ L.sc.w'' D.R.n := hR.2.1
    have hpos : (0 : ℤ) ≤ ⌊(hcAt D g).e j⌋ := by
      have : (0 : ℝ) ≤ (⌊(hcAt D g).e j⌋ : ℝ) := by linarith
      exact_mod_cast this
    have : ((⌊(hcAt D g).e j⌋.toNat : ℤ) : ℝ) = (⌊(hcAt D g).e j⌋ : ℝ) := by
      rw [Int.toNat_of_nonneg hpos]
    have h' : ((⌊(hcAt D g).e j⌋.toNat : ℕ) : ℝ) = (⌊(hcAt D g).e j⌋ : ℝ) := by
      rw [← this]; norm_cast
    rw [h']; exact h2
  have hbdd : BddAbove {s : ℕ | ∃ (g : D.R.GG) (j : Fin D.R.m), ¬ Thick D.host g ∧ s = ⌊(hcAt D g).e j⌋.toNat} := by
    refine ⟨⌊8 / 5 * L.sc.b'⌋₊, fun s hs => ?_⟩
    exact Nat.le_floor (hmem s hs)
  refine ⟨?_, ?_⟩
  · unfold wMax
    rcases Set.eq_empty_or_nonempty {s : ℕ | ∃ (g : D.R.GG) (j : Fin D.R.m), ¬ Thick D.host g ∧ s = ⌊(hcAt D g).e j⌋.toNat} with he | hne
    · rw [he, csSup_empty]; simp; linarith
    · obtain ⟨s, hs, hseq⟩ : ∃ s ∈ {s : ℕ | ∃ (g : D.R.GG) (j : Fin D.R.m), ¬ Thick D.host g ∧ s = ⌊(hcAt D g).e j⌋.toNat}, s = sSup {s : ℕ | ∃ (g : D.R.GG) (j : Fin D.R.m), ¬ Thick D.host g ∧ s = ⌊(hcAt D g).e j⌋.toNat} :=
        ⟨_, Nat.sSup_mem hne hbdd, rfl⟩
      rw [← hseq]; exact hmem s hs
  · intro g j hg
    have h1 : ⌊(hcAt D g).e j⌋.toNat ≤ wMax D := le_csSup hbdd ⟨g, j, hg, rfl⟩
    calc ⌊(hcAt D g).e j⌋ ≤ (⌊(hcAt D g).e j⌋.toNat : ℤ) := Int.self_le_toNat _
      _ ≤ (wMax D : ℤ) := by exact_mod_cast h1

end GlobalTheory.HTW
