import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.RealStructures.Imports
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.ImportsBis
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.HeckeCharacterEqOfCofinite

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ l _ ι art _ χ χ' n n' μ hχ hχ'`. Apply `GlobalTheory.T.hecke_character_eq_of_cofinite E χ χ'` to reduce the goal to its premises. Establish `hl : Ideal.span {(l : 𝓞 E)} ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `(Fact.out : Nat.Prime l).ne_zero` after adjusting the coercions.

Establish `hfin` using `Ideal.finite_factors hl`. Establish `h1` using `(GlobalTheory.Mem.UnrAe.unr_ae_and_level E χ).1`. Establish `h2` using `(GlobalTheory.Mem.UnrAe.unr_ae_and_level E χ').1`. Establish `hev` using `((h1.union h2).union hfin).compl_mem_cofinite`. Use `filter_upwards [hev] with v hv`.

Simplify using `only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hv`. Take `⟨⟨hu, hu'⟩, hd⟩` from `hv`. Establish `hl' : (l : 𝓞 E) ∉ v.asIdeal` using `fun h => hd (Ideal.dvd_span_singleton.mpr h)`. Use `⟨hu, hu', ?_⟩` and prove the remaining obligations. Take `⟨σ, hσ⟩` from `toAb_surjective (E := E) (Ω := Ω) (art (localIdele E v (atFin v (unif v))))`.

Establish `a` using `hχ.loc_away (Or.inl hl') (atFin v (unif v)) σ hσ.symm`. Establish `b` using `hχ'.loc_away (Or.inl hl') (atFin v (unif v)) σ hσ.symm`. Rewrite using `[← HChar.val_eq χ hu _ (unif_spec v), ← HChar.val_eq χ' hu' _ (unif_spec v)]`. Conclude with `Units.ext (ι.symm.injective (a.symm.trans b))`.
-/
theorem UpperTheory.Gal.TP.Sub.charInj_holds :
    CharInj := by
  intro E Ω _ _ _ _ _ l _ ι art _ χ χ' n n' μ hχ hχ'
  apply GlobalTheory.T.hecke_character_eq_of_cofinite E χ χ'
  have hl : Ideal.span {(l : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : Nat.Prime l).ne_zero
  have hfin := Ideal.finite_factors hl
  have h1 := (GlobalTheory.Mem.UnrAe.unr_ae_and_level E χ).1
  have h2 := (GlobalTheory.Mem.UnrAe.unr_ae_and_level E χ').1
  have hev := ((h1.union h2).union hfin).compl_mem_cofinite
  filter_upwards [hev] with v hv
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hv
  obtain ⟨⟨hu, hu'⟩, hd⟩ := hv
  have hl' : (l : 𝓞 E) ∉ v.asIdeal := fun h => hd (Ideal.dvd_span_singleton.mpr h)
  refine ⟨hu, hu', ?_⟩
  obtain ⟨σ, hσ⟩ := toAb_surjective (E := E) (Ω := Ω) (art (localIdele E v (atFin v (unif v))))
  have a := hχ.loc_away (Or.inl hl') (atFin v (unif v)) σ hσ.symm
  have b := hχ'.loc_away (Or.inl hl') (atFin v (unif v)) σ hσ.symm
  rw [← HChar.val_eq χ hu _ (unif_spec v), ← HChar.val_eq χ' hu' _ (unif_spec v)]
  exact Units.ext (ι.symm.injective (a.symm.trans b))
