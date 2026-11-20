import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LevelDefs
import GroundTheory.GlobalFields.SecondInequality.Cyclic
import GroundTheory.TateCohomology.HerbrandTate
import GroundTheory.TateCohomology.Herbrand
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory CategoryTheory.Limits GroundTheory.Global NumberField Module

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

/- English proof (translation)
Rewrite using `[GroundTheory.GroupCoh.natCard_tateCohomology_zero _ hσ]`. Conclude with `(classFieldAxiom_ideleClassGroup σ hσ).1`.
-/
theorem natCard_tateCohomology_zero_ideleClassRep (σ : Gal(L/K))
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Nat.card (tateCohomology (ideleClassRep K L) 0) = finrank K L := by
  rw [GroundTheory.GroupCoh.natCard_tateCohomology_zero _ hσ]
  exact (classFieldAxiom_ideleClassGroup σ hσ).1

/- English proof (translation)
Rewrite using `[GroundTheory.GroupCoh.natCard_tateCohomology_neg_one _ hσ]`. Conclude with `(classFieldAxiom_ideleClassGroup σ hσ).2`.
-/
theorem natCard_tateCohomology_neg_one_ideleClassRep (σ : Gal(L/K))
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Nat.card (tateCohomology (ideleClassRep K L) (-1)) = 1 := by
  rw [GroundTheory.GroupCoh.natCard_tateCohomology_neg_one _ hσ]
  exact (classFieldAxiom_ideleClassGroup σ hσ).2

variable [IsCyclic Gal(L/K)]

/- English proof (translation)
Take `⟨σ, hσ⟩` from `IsCyclic.exists_generator (α := Gal(L/K))`. Establish `e2 : (-1 + 2 : ℤ) = ((1 : ℕ) : ℤ)` using `by norm_num`. Establish `h0 : Nat.card (groupCohomology (ideleClassRep K L) 1) = Nat.card (tateCohomology (ideleClassRep K L) ((1 : ℕ) : ℤ))` using `(Nat.card_congr ((TateCohomology.isoGroupCohomology 1).app (ideleClassRep K L)).toLinearEquiv.toEquiv).symm`. Establish `h1 : Nat.card (tateCohomology (ideleClassRep K L) (-1 + 2)) = Nat.card (tateCohomology (ideleClassRep K L) (-1))` using `Nat.card_congr (GroundTheory.GroupCoh.tateCohomologyPeriodicIso (ideleClassRep K L) hσ (-1)).toLinearEquiv.toEquiv`. Establish `h : Nat.card (groupCohomology (ideleClassRep K L) 1) = 1`.

Rewrite using `[h0, ← e2, h1]`. Conclude with `natCard_tateCohomology_neg_one_ideleClassRep σ hσ`. Establish `: Subsingleton (groupCohomology (ideleClassRep K L) 1)` using `(Nat.card_eq_one_iff_unique.1 h).1`. Conclude with `ModuleCat.isZero_of_subsingleton _`.
-/
theorem isZero_groupCohomology_one_ideleClassRep_of_isCyclic :
    IsZero (groupCohomology (ideleClassRep K L) 1) := by
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  have e2 : (-1 + 2 : ℤ) = ((1 : ℕ) : ℤ) := by norm_num
  have h0 : Nat.card (groupCohomology (ideleClassRep K L) 1) =
      Nat.card (tateCohomology (ideleClassRep K L) ((1 : ℕ) : ℤ)) :=
    (Nat.card_congr
      ((TateCohomology.isoGroupCohomology 1).app (ideleClassRep K L)).toLinearEquiv.toEquiv).symm
  have h1 : Nat.card (tateCohomology (ideleClassRep K L) (-1 + 2)) =
      Nat.card (tateCohomology (ideleClassRep K L) (-1)) :=
    Nat.card_congr
      (GroundTheory.GroupCoh.tateCohomologyPeriodicIso (ideleClassRep K L) hσ (-1)).toLinearEquiv.toEquiv
  have h : Nat.card (groupCohomology (ideleClassRep K L) 1) = 1 := by
    rw [h0, ← e2, h1]
    exact natCard_tateCohomology_neg_one_ideleClassRep σ hσ
  have : Subsingleton (groupCohomology (ideleClassRep K L) 1) :=
    (Nat.card_eq_one_iff_unique.1 h).1
  exact ModuleCat.isZero_of_subsingleton _

/- English proof (translation)
Take `⟨σ, hσ⟩` from `IsCyclic.exists_generator (α := Gal(L/K))`. Set `e : groupCohomology (ideleClassRep K L) 2 ≅ tateCohomology (ideleClassRep K L) 0` to `((TateCohomology.isoGroupCohomology 2).app (ideleClassRep K L)).symm ≪≫ GroundTheory.GroupCoh.tateCohomologyPeriodicIso (ideleClassRep K L) hσ 0`. Rewrite using `[Nat.card_congr e.toLinearEquiv.toEquiv]`. Conclude with `natCard_tateCohomology_zero_ideleClassRep σ hσ`.
-/
theorem natCard_groupCohomology_two_ideleClassRep_of_isCyclic :
    Nat.card (groupCohomology (ideleClassRep K L) 2) = finrank K L := by
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  let e : groupCohomology (ideleClassRep K L) 2 ≅ tateCohomology (ideleClassRep K L) 0 :=
    ((TateCohomology.isoGroupCohomology 2).app (ideleClassRep K L)).symm ≪≫
      GroundTheory.GroupCoh.tateCohomologyPeriodicIso (ideleClassRep K L) hσ 0
  rw [Nat.card_congr e.toLinearEquiv.toEquiv]
  exact natCard_tateCohomology_zero_ideleClassRep σ hσ

end GroundTheory.ProfCoh
