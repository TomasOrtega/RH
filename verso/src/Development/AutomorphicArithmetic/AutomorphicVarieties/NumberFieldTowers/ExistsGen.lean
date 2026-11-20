import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ExistsGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ContTw
import GroundTheory.GlobalFields.CyclotomicCharacters.PadicUnitsLog

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

/- English proof (translation)
Introduce `k Ω _ _ _ _ _ l _ U hU hcond`. Establish `hclosed : IsClosed ((U.map (cycZ k Ω l) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ)`. Rewrite using `[Subgroup.coe_map]`. Conclude with `(hU.isCompact.image (continuous_cycZ k Ω l)).isClosed`. Establish `hc : l ≠ 2 ∨ U.map (cycZ k Ω l) ≤ KStar.TotallyRealRoots.princ l 2`.

Distinguish the cases in `hl : l = 2`. Break down `hcond with h | h` into its components or cases. Conclude with `absurd hl h`. Use `right`. Rewrite using `[Subgroup.map_le_iff_le_comap]`.

Introduce `x hx`. Establish `hx'` using `h hx`. Simplify using `only [gamU, levU, qExp, if_pos hl, Subgroup.mem_inf] at hx'`. Conclude with `hx'.2`. Conclude with `Or.inl hl`.

Take `⟨γ', hγ', hle⟩` from `UpperTheory.V.Kum.existsGen l (U.map (cycZ k Ω l)) hclosed hc`. Take `⟨γ, hγU, rfl⟩` from `Subgroup.mem_map.mp hγ'`. Conclude with `⟨γ, hγU, hle⟩`.
-/
theorem UpperTheory.V.Tower.existsGen :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (U : Subgroup (G k Ω)), IsClosed (U : Set (G k Ω)) → (l ≠ 2 ∨ U ≤ gamU l ⊤) → ∃ γ, IsGen l U γ := by
  intro k Ω _ _ _ _ _ l _ U hU hcond
  have hclosed : IsClosed ((U.map (cycZ k Ω l) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) := by
    rw [Subgroup.coe_map]
    exact (hU.isCompact.image (continuous_cycZ k Ω l)).isClosed
  have hc : l ≠ 2 ∨ U.map (cycZ k Ω l) ≤ KStar.TotallyRealRoots.princ l 2 := by
    by_cases hl : l = 2
    · rcases hcond with h | h
      · exact absurd hl h
      · right
        rw [Subgroup.map_le_iff_le_comap]
        intro x hx
        have hx' := h hx
        simp only [gamU, levU, qExp, if_pos hl, Subgroup.mem_inf] at hx'
        exact hx'.2
    · exact Or.inl hl
  obtain ⟨γ', hγ', hle⟩ := UpperTheory.V.Kum.existsGen l (U.map (cycZ k Ω l)) hclosed hc
  obtain ⟨γ, hγU, rfl⟩ := Subgroup.mem_map.mp hγ'
  exact ⟨γ, hγU, hle⟩
