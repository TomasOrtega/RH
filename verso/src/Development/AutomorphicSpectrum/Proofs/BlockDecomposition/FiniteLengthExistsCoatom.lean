import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyExhaustion.PropsExh
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace GlobalTheory.CompanionTheory.FiniteLengthQuot

/- English proof (translation)
Introduce `G V _ _ _ ρ hfl hnt`. Establish `: WellFoundedGT (Subrepresentation ρ)` using `((hasFiniteLength_iff_wellFounded ρ).1 hfl).1`. Establish `hbt : (⊥ : Subrepresentation ρ) ≠ ⊤`. Introduce `h`. Take `⟨x, hx⟩` from `exists_ne (0 : V)`.

Establish `hmem : x ∈ (⊤ : Subrepresentation ρ).toSubmodule` using `Submodule.mem_top`. Rewrite `hmem` using `[← h]`. Conclude with `hx ((Submodule.mem_bot ℂ).1 hmem)`. Take `⟨M, hM, -⟩` from `(IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subrepresentation ρ)).resolve_left hbt`. Conclude with `⟨M, hM⟩`.
-/
theorem exists_isCoatom_subrepresentation :
    ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V),
      HasFiniteLength ρ → Nontrivial V → ∃ S : Subrepresentation ρ, IsCoatom S := by
  intro G V _ _ _ ρ hfl hnt
  have : WellFoundedGT (Subrepresentation ρ) := ((hasFiniteLength_iff_wellFounded ρ).1 hfl).1
  have hbt : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have hmem : x ∈ (⊤ : Subrepresentation ρ).toSubmodule := Submodule.mem_top
    rw [← h] at hmem
    exact hx ((Submodule.mem_bot ℂ).1 hmem)
  obtain ⟨M, hM, -⟩ :=
    (IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subrepresentation ρ)).resolve_left hbt
  exact ⟨M, hM⟩

end GlobalTheory.CompanionTheory.FiniteLengthQuot
