import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.CompFixSAlt

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX

open PositivityTheory.Rg.BcB.F

/- English proof (translation)
Introduce `hIP hW hIS hR E _ _ _ hE n _ π hπ S F₀ T`. Take `⟨w₁, -, -, hw₁s, hw₁u⟩` from `hIP E hE n π hπ F₀.Sec F₀.hSec ∅`. Set `T' : Finset (Pl E)` to `insert w₁ (T.filter fun w => IsUnramU π w ∧ ¬ IsSplitAt w)`. Establish `key : ∀ w ∈ T', ¬ IsSplitAt w ∧ IsUnramU π w`. Introduce `w hw`.

Break down `Finset.mem_insert.1 hw with h | h` into its components or cases. Substitute `h` using the available equality. Conclude with `⟨hw₁s, hw₁u⟩`. Establish `h'` using `(Finset.mem_filter.1 h).2`. Conclude with `⟨h'.2, h'.1⟩`.

Use `⟨T', fun w => if h : w ∈ T' ∧ ¬ IsSplitAt w then (hW E hE n w h.2).choose else F₀.d₀.b w, ⟨w₁, Finset.mem_insert_self _ _⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `w hw`. Take `⟨hs, hu⟩` from `key w hw`. Establish `h : w ∈ T' ∧ ¬ IsSplitAt w` using `⟨hw, hs⟩`. Use `⟨hIS E F₀.Sec F₀.hSec w hs, hs, hu, ?_, fun h0 => hs (F₀.S₀ w h0).2, fun h0 => (F₀.bad w h0).2 hs hu⟩` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[dif_pos h]`. Conclude with `(hW E hE n w h.2).choose_spec`. Introduce `w hw dsimp only`. Rewrite using `[dif_neg (fun h => hw h.1)]`.

Introduce `w hw hu hs`. Conclude with `Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hw, hu, hs⟩)`.
-/
theorem exTbOf : ExTbOf := by
  intro hIP hW hIS hR E _ _ _ hE n _ π hπ S F₀ T
  obtain ⟨w₁, -, -, hw₁s, hw₁u⟩ := hIP E hE n π hπ F₀.Sec F₀.hSec ∅
  let T' : Finset (Pl E) := insert w₁ (T.filter fun w => IsUnramU π w ∧ ¬ IsSplitAt w)
  have key : ∀ w ∈ T', ¬ IsSplitAt w ∧ IsUnramU π w := by
    intro w hw
    rcases Finset.mem_insert.1 hw with h | h
    · subst h; exact ⟨hw₁s, hw₁u⟩
    · have h' := (Finset.mem_filter.1 h).2
      exact ⟨h'.2, h'.1⟩
  refine ⟨T', fun w => if h : w ∈ T' ∧ ¬ IsSplitAt w then (hW E hE n w h.2).choose else F₀.d₀.b w,
    ⟨w₁, Finset.mem_insert_self _ _⟩, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨hs, hu⟩ := key w hw
    have h : w ∈ T' ∧ ¬ IsSplitAt w := ⟨hw, hs⟩
    refine ⟨hIS E F₀.Sec F₀.hSec w hs, hs, hu, ?_, fun h0 => hs (F₀.S₀ w h0).2, fun h0 => (F₀.bad w h0).2 hs hu⟩
    dsimp only
    rw [dif_pos h]
    exact (hW E hE n w h.2).choose_spec
  · intro w hw
    dsimp only
    rw [dif_neg (fun h => hw h.1)]
  · intro w hw hu hs
    exact Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hw, hu, hs⟩)

end PositivityTheory.Rg.BcB.F.FX

end
