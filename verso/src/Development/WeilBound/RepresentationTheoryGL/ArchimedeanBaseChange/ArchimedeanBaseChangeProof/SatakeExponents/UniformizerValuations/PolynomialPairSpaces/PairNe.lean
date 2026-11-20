import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.InfParts

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation

namespace PositivityTheory.Rg.BcB.F.LemDd.PairSpaceNonzero

/- English proof (translation)
Unfold `pairSpace`. Rewrite using `[Submodule.span_eq_bot]`. Introduce and unpack `F ⟨φ₁, h₁, φ₂, -, rfl⟩`. Rewrite `h₁` using `[Submodule.mem_bot]`. Substitute `h₁` using the available equality.

Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules.
-/
theorem pairSpace_left_bot {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}
    (U₂ : Submodule ℂ (Sm E b)) : pairSpace (⊥ : Submodule ℂ (Sm E a)) U₂ = ⊥ := by
  unfold pairSpace
  rw [Submodule.span_eq_bot]
  rintro F ⟨φ₁, h₁, φ₂, -, rfl⟩
  rw [Submodule.mem_bot] at h₁
  subst h₁
  funext x
  simp

/- English proof (translation)
Unfold `pairSpace`. Rewrite using `[Submodule.span_eq_bot]`. Introduce and unpack `F ⟨φ₁, -, φ₂, h₂, rfl⟩`. Rewrite `h₂` using `[Submodule.mem_bot]`. Substitute `h₂` using the available equality.

Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules.
-/
theorem pairSpace_right_bot {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}
    (U₁ : Submodule ℂ (Sm E a)) : pairSpace U₁ (⊥ : Submodule ℂ (Sm E b)) = ⊥ := by
  unfold pairSpace
  rw [Submodule.span_eq_bot]
  rintro F ⟨φ₁, -, φ₂, h₂, rfl⟩
  rw [Submodule.mem_bot] at h₂
  subst h₂
  funext x
  simp

end PositivityTheory.Rg.BcB.F.LemDd.PairSpaceNonzero

namespace PositivityTheory.Rg.BcB.F.LemDd

/- English proof (translation)
Introduce `E _ _ _ a b U₁ U₂ G hG hne`. Use `⟨fun h => hne ?_, fun h => hne ?_⟩` and prove the remaining obligations. Substitute `h` using the available equality. Rewrite `hG` using `[PairSpaceNonzero.pairSpace_left_bot, Submodule.mem_bot]`. Conclude with `hG`.

Substitute `h` using the available equality. Rewrite `hG` using `[PairSpaceNonzero.pairSpace_right_bot, Submodule.mem_bot]`. Conclude with `hG`.
-/
theorem PairNe_holds : PairNe := by
  intro E _ _ _ a b U₁ U₂ G hG hne
  refine ⟨fun h => hne ?_, fun h => hne ?_⟩
  · subst h
    rw [PairSpaceNonzero.pairSpace_left_bot, Submodule.mem_bot] at hG
    exact hG
  · subst h
    rw [PairSpaceNonzero.pairSpace_right_bot, Submodule.mem_bot] at hG
    exact hG

end PositivityTheory.Rg.BcB.F.LemDd

end
