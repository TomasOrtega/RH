import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory

/- English proof (translation)
Establish `hO : Function.Injective (algebraMap O (FractionRing O))` using `IsFractionRing.injective _ _`. Establish `hA : Function.Injective (algebraMap A (FractionRing A))` using `IsFractionRing.injective _ _`. Use `set g : A →+* FractionRing O := (algebraMap O (FractionRing O)).comp (algebraMap A O) with hg`. Establish `hgi : Function.Injective g` using `hO.comp hinj`. Express the relevant statement in the definitionally equal form `P.map g = _ at hP`.

Express the relevant statement in the definitionally equal form `((P.map (algebraMap A (FractionRing A))).rootSet _).ncard = t at hcard`. Establish `hmon' : (P.map g).Monic`. Rewrite using `[hP]`. Conclude with `Polynomial.monic_prod_of_monic _ _ (fun c _ => Polynomial.monic_X_sub_C _)`. Establish `hmon : P.Monic` using `Polynomial.monic_of_injective hgi hmon'`.

Establish `hdeg : P.natDegree = t`. Rewrite using `[← hmon.natDegree_map g, hP, Polynomial.natDegree_prod_of_monic _ _ (fun c _ => Polynomial.monic_X_sub_C _)]`. Simplify using the standard rewrite rules. Establish `hsep : (P.map (algebraMap A (FractionRing A))).Separable`. Establish `hne : P.map (algebraMap A (FractionRing A)) ≠ 0` using `(hmon.map _).ne_zero`.

Rewrite using `[← Polynomial.card_rootSet_eq_natDegree_iff_of_splits (K := AlgebraicClosure (FractionRing A)) hne (IsAlgClosed.splits _), hmon.natDegree_map, hdeg, ← hcard, Set.ncard_eq_toFinset_card', Set.toFinset_card]`. Take `⟨φ, hφ⟩ : ∃ φ : FractionRing A →+* FractionRing O, φ.comp (algebraMap A (FractionRing A)) = g` from `⟨IsFractionRing.lift hgi, RingHom.ext fun a => IsFractionRing.lift_algebraMap (K := FractionRing A) hgi a⟩`. Establish `hsep2 : (P.map g).Separable`. Rewrite using `[← hφ, ← Polynomial.map_map]`. Conclude with `hsep.map`.

Establish `hα : Function.Injective α`. Rewrite `hsep2` using `[hP]`. Conclude with `Polynomial.separable_prod_X_sub_C_iff.mp hsep2`. Establish `hint : ∀ c, ∃ b : O, algebraMap O (FractionRing O) b = α c`. Introduce `c`.

Apply `IsIntegrallyClosed.algebraMap_eq_of_integral` to reduce the goal to its premises. Use `⟨P.map (algebraMap A O), hmon.map _, ?_⟩` and prove the remaining obligations. Rewrite using `[← Polynomial.eval_map, Polynomial.map_map, ← hg, hP, Polynomial.eval_prod]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ c) (by simp)`. Use `choose β hβ using hint`.

Use `⟨β, fun c d h => hα (by rw [← hβ, ← hβ, h]), ?_⟩` and prove the remaining obligations. Apply `Polynomial.map_injective _ hO` to reduce the goal to its premises. Rewrite using `[Polynomial.map_map, ← hg, hP, Polynomial.map_prod]`. Simplify using `[hβ]`.
-/
theorem exists_injective_roots_of_ncard_rootSet {A O : Type} [CommRing A] [IsDomain A] [CommRing O] [IsDomain O] [IsIntegrallyClosed O] [Algebra A O] (t : ℕ) (P : Polynomial A) (α : Fin t → FractionRing O)
    (hinj : Function.Injective (algebraMap A O))
    (hcard : ((P.map (toFr A)).rootSet (AlgebraicClosure (FractionRing A))).ncard = t)
    (hP : P.map ((toFr O).comp (algebraMap A O)) = ∏ c, (Polynomial.X - Polynomial.C (α c))) :
    ∃ β : Fin t → O, Function.Injective β ∧ P.map (algebraMap A O) = ∏ c, (Polynomial.X - Polynomial.C (β c)) := by
  classical
  have hO : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective _ _
  have hA : Function.Injective (algebraMap A (FractionRing A)) := IsFractionRing.injective _ _
  set g : A →+* FractionRing O := (algebraMap O (FractionRing O)).comp (algebraMap A O) with hg
  have hgi : Function.Injective g := hO.comp hinj
  change P.map g = _ at hP
  change ((P.map (algebraMap A (FractionRing A))).rootSet _).ncard = t at hcard
  have hmon' : (P.map g).Monic := by
    rw [hP]; exact Polynomial.monic_prod_of_monic _ _ (fun c _ => Polynomial.monic_X_sub_C _)
  have hmon : P.Monic := Polynomial.monic_of_injective hgi hmon'
  have hdeg : P.natDegree = t := by
    rw [← hmon.natDegree_map g, hP, Polynomial.natDegree_prod_of_monic _ _ (fun c _ => Polynomial.monic_X_sub_C _)]
    simp
  have hsep : (P.map (algebraMap A (FractionRing A))).Separable := by
    have hne : P.map (algebraMap A (FractionRing A)) ≠ 0 := (hmon.map _).ne_zero
    rw [← Polynomial.card_rootSet_eq_natDegree_iff_of_splits (K := AlgebraicClosure (FractionRing A)) hne (IsAlgClosed.splits _), hmon.natDegree_map, hdeg, ← hcard, Set.ncard_eq_toFinset_card', Set.toFinset_card]
  obtain ⟨φ, hφ⟩ : ∃ φ : FractionRing A →+* FractionRing O, φ.comp (algebraMap A (FractionRing A)) = g :=
    ⟨IsFractionRing.lift hgi, RingHom.ext fun a => IsFractionRing.lift_algebraMap (K := FractionRing A) hgi a⟩
  have hsep2 : (P.map g).Separable := by
    rw [← hφ, ← Polynomial.map_map]; exact hsep.map
  have hα : Function.Injective α := by
    rw [hP] at hsep2
    exact Polynomial.separable_prod_X_sub_C_iff.mp hsep2
  have hint : ∀ c, ∃ b : O, algebraMap O (FractionRing O) b = α c := by
    intro c
    apply IsIntegrallyClosed.algebraMap_eq_of_integral
    refine ⟨P.map (algebraMap A O), hmon.map _, ?_⟩
    rw [← Polynomial.eval_map, Polynomial.map_map, ← hg, hP, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ c) (by simp)
  choose β hβ using hint
  refine ⟨β, fun c d h => hα (by rw [← hβ, ← hβ, h]), ?_⟩
  apply Polynomial.map_injective _ hO
  rw [Polynomial.map_map, ← hg, hP, Polynomial.map_prod]
  simp [hβ]

end GlobalTheory
