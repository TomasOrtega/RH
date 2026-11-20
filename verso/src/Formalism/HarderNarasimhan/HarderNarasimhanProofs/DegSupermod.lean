import Formalism.HarderNarasimhan.DegSupermodZ
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DegSupermodZ

open Module Submodule

noncomputable section

namespace Formalism.HN

section

variable {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (ρ : V →+ E)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem degSupermod_mem_zl (N : Submodule R V) (y : E) :
    y ∈ zl ρ N ↔ ∃ x ∈ N, ρ x = y := Iff.rfl

/- English proof (translation)
Introduce `y hy`. Take `⟨x, hx, rfl⟩` from `(degSupermod_mem_zl ρ A y).mp hy`. Conclude with `(degSupermod_mem_zl ρ B _).mpr ⟨x, h hx, rfl⟩`.
-/
theorem degSupermod_zl_mono {A B : Submodule R V} (h : A ≤ B) : zl ρ A ≤ zl ρ B := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (degSupermod_mem_zl ρ A y).mp hy
  exact (degSupermod_mem_zl ρ B _).mpr ⟨x, h hx, rfl⟩

/- English proof (translation)
Simplify using `only [zl, Submodule.sup_toAddSubgroup, AddSubgroup.map_sup]`. Use `first`. Consider the case `exact SupHomClass.map_sup AddSubgroup.toIntSubmodule _ _`. Consider the case `(ext y; simp [Submodule.mem_sup, AddSubgroup.mem_sup])`.
-/
theorem degSupermod_zl_sup (A B : Submodule R V) : zl ρ (A ⊔ B) = zl ρ A ⊔ zl ρ B := by
  simp only [zl, Submodule.sup_toAddSubgroup, AddSubgroup.map_sup]
  first
    | exact SupHomClass.map_sup AddSubgroup.toIntSubmodule _ _
    | (ext y; simp [Submodule.mem_sup, AddSubgroup.mem_sup])

/- English proof (translation)
Use `le_antisymm (le_inf (degSupermod_zl_mono ρ inf_le_left) (degSupermod_zl_mono ρ inf_le_right)) ?_` and prove the remaining obligations. Introduce and unpack `y ⟨hyA, hyB⟩`. Take `⟨a, ha, rfl⟩` from `(degSupermod_mem_zl ρ A y).mp hyA`. Take `⟨b, hb, hba⟩` from `(degSupermod_mem_zl ρ B _).mp hyB`. Establish `hab : b = a` using `hinj (hB hb) (hA ha) hba`.

Substitute `hab` using the available equality. Conclude with `(degSupermod_mem_zl ρ (A ⊓ B) _).mpr ⟨b, ⟨ha, hb⟩, rfl⟩`.
-/
theorem degSupermod_zl_inf {L A B : Submodule R V} (hinj : Set.InjOn ρ (L : Set V))
    (hA : A ≤ L) (hB : B ≤ L) : zl ρ (A ⊓ B) = zl ρ A ⊓ zl ρ B := by
  refine le_antisymm (le_inf (degSupermod_zl_mono ρ inf_le_left)
    (degSupermod_zl_mono ρ inf_le_right)) ?_
  rintro y ⟨hyA, hyB⟩
  obtain ⟨a, ha, rfl⟩ := (degSupermod_mem_zl ρ A y).mp hyA
  obtain ⟨b, hb, hba⟩ := (degSupermod_mem_zl ρ B _).mp hyB

  have hab : b = a := hinj (hB hb) (hA ha) hba
  subst hab
  exact (degSupermod_mem_zl ρ (A ⊓ B) _).mpr ⟨b, ⟨ha, hb⟩, rfl⟩

end

universe u v w in
/- English proof (translation)
Introduce `R V E _ _ _ _ _ _ ρ L A B hL hA hB`. Use `haveI := hL.2`. Establish `key` using `h E (zl ρ L) (zl ρ A) (zl ρ B) hL.2 (degSupermod_zl_mono ρ hA) (degSupermod_zl_mono ρ hB)`. Rewrite `key` using `[← degSupermod_zl_sup ρ A B, ← degSupermod_zl_inf ρ hL.1 hA hB]`. Conclude with `key`.
-/
theorem degSupermod_of (h : DegSupermodZ.{w}) : DegSupermod.{u, v, w} := by
  intro R V E _ _ _ _ _ _ ρ L A B hL hA hB
  haveI := hL.2
  have key := h E (zl ρ L) (zl ρ A) (zl ρ B) hL.2 (degSupermod_zl_mono ρ hA)
    (degSupermod_zl_mono ρ hB)
  rw [← degSupermod_zl_sup ρ A B, ← degSupermod_zl_inf ρ hL.1 hA hB] at key
  exact key

/- English proof (translation)
The claim follows from `degSupermod_of degree_supermodular_integral`.
-/
theorem degree_supermodular : DegSupermod := degSupermod_of degree_supermodular_integral

end Formalism.HN
