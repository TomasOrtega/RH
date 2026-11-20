import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.FiniteOrderCongruences.TwistIne
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoCoefOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu
open scoped Matrix

namespace UpperTheory.V.Cu2

/- English proof (translation)
Establish `hc : Continuous fun g => (ka g).val` using `Units.continuous_val.comp h`. Set `r : Γ →* GL (Fin 1) (PadicAlgCl l)` to `(Units.map (Matrix.scalar (Fin 1) : PadicAlgCl l →+* _).toMonoidHom).comp ka`. Establish `hr : ∀ (g : Γ) (i j : Fin 1), (r g).val i j = (ka g).val`. Introduce `g i j`. Take `rfl : i = j` from `Subsingleton.elim _ _`.

Simplify using `[r]`. Take `⟨E, hE, hm⟩` from `GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem l Γ 1 r (fun i j => by simp only [hr]; exact hc)`. Use `⟨E, hE, fun g => ⟨hr g 0 0 ▸ hm g 0 0, ?_⟩⟩` and prove the remaining obligations. Take `⟨C, hC⟩` from `(isCompact_range hc.norm).bddAbove`. Assume the negation of the conclusion as `hg`.

Take `⟨N, hN⟩` from `pow_unbounded_of_one_lt C (not_le.1 hg)`. Use `hC ⟨g ^ N, rfl⟩` as an intermediate fact. Simplify using `only [map_pow, Units.val_pow_eq_pow_val, norm_pow] at this`. Conclude with `absurd hN (not_lt.2 this)`.
-/
private theorem ce_char {l : ℕ} [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] (ka : Γ →* (PadicAlgCl l)ˣ) (h : Continuous ka) :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧
      ∀ g, (ka g).val ∈ E ∧ ‖(ka g).val‖ ≤ 1 := by
  have hc : Continuous fun g => (ka g).val := Units.continuous_val.comp h
  let r : Γ →* GL (Fin 1) (PadicAlgCl l) :=
    (Units.map (Matrix.scalar (Fin 1) : PadicAlgCl l →+* _).toMonoidHom).comp ka
  have hr : ∀ (g : Γ) (i j : Fin 1), (r g).val i j = (ka g).val := by
    intro g i j
    obtain rfl : i = j := Subsingleton.elim _ _
    simp [r]
  obtain ⟨E, hE, hm⟩ := GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem l Γ 1 r
    (fun i j => by simp only [hr]; exact hc)
  refine ⟨E, hE, fun g => ⟨hr g 0 0 ▸ hm g 0 0, ?_⟩⟩
  obtain ⟨C, hC⟩ := (isCompact_range hc.norm).bddAbove
  by_contra hg
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt C (not_le.1 hg)
  have := hC ⟨g ^ N, rfl⟩
  simp only [map_pow, Units.val_pow_eq_pow_val, norm_pow] at this
  exact absurd hN (not_lt.2 this)

end UpperTheory.V.Cu2

end
