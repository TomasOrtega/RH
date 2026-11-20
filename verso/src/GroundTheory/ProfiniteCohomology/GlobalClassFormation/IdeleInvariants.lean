import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.ABHNPrep
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleInvariants.LocalInf
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.RealPlaces
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield IsDedekindDomain IdeleLimit
  GroundTheory.Global.SemiLocal

open scoped NumberField.LiesOver DirectSum

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K E : FiniteSubfield} [Fact (K ≤ E)] (ι : LocalEmbeddings K) (ιE : LocalEmbeddings E)

section Places

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Rewrite using `[idelesLimitCohomologyEquiv_apply_inr, idelesLimitCohomologyEquiv_apply_inr]`. Take `⟨ι', hι'⟩` from `exists_placeOfEmbedding_eq w`. Establish `key : ∀ u : PlacesOver E.1 v, placeOfEmbedding ι' E = u → placeInv (K` using `E) (.inr u.1) ((idelesLocalRes (ιE.fin u.1) 2).hom ((idelesResField K E 2).hom y)) = Module.finrank (v.adicCompletion K.1) (u.1.adicCompletion E.1) • placeInv (K := K) (.inr v) ((idelesLocalRes (ι.fin v) 2).hom y) := by`. Introduce and unpack `u rfl`. Rewrite using `[idelesLocalRes_eq_of_algHom ι' (ι.fin v)]`.

Conclude with `brauerInvZOfIsSepClosure_idelesLocalRes_idelesResField v ι' (ιE.fin _) y`. Conclude with `key w hι'`.
-/
theorem placeInv_idelesResField_inr (y : cohomology (limitRep K) 2) (v : HeightOneSpectrum (𝓞 K.1))
    (w : PlacesOver E.1 v) :
    placeInv (.inr w.1) (idelesLimitCohomologyEquiv ιE (by norm_num : 1 ≤ 2) ((idelesResField K E 2).hom y) (.inr w.1)) =
      Module.finrank (v.adicCompletion K.1) (w.1.adicCompletion E.1) •
        placeInv (.inr v) (idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2) y (.inr v)) := by
  rw [idelesLimitCohomologyEquiv_apply_inr, idelesLimitCohomologyEquiv_apply_inr]
  obtain ⟨ι', hι'⟩ := exists_placeOfEmbedding_eq w
  have key : ∀ u : PlacesOver E.1 v, placeOfEmbedding ι' E = u →
      placeInv (K := E) (.inr u.1) ((idelesLocalRes (ιE.fin u.1) 2).hom ((idelesResField K E 2).hom y)) =
        Module.finrank (v.adicCompletion K.1) (u.1.adicCompletion E.1) •
          placeInv (K := K) (.inr v) ((idelesLocalRes (ι.fin v) 2).hom y) := by
    rintro u rfl
    rw [idelesLocalRes_eq_of_algHom ι' (ι.fin v)]
    exact brauerInvZOfIsSepClosure_idelesLocalRes_idelesResField v ι' (ιE.fin _) y
  exact key w hι'

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Rewrite using `[idelesLimitCohomologyEquiv_apply_inl, idelesLimitCohomologyEquiv_apply_inl]`. Distinguish the cases in `hw : (w : InfinitePlace E.1).IsComplex`. Establish `h0 : placeInv (K` using `E) (.inl (w : InfinitePlace E.1)) ((infIdelesLocalRes (ιE.inf (w : InfinitePlace E.1)) 2).hom ((idelesResField K E 2).hom y)) = 0 := by`. Establish `: Subsingleton (cohomology (galUnitsZ (w : InfinitePlace E.1).Completion (AlgebraicClosure (w : InfinitePlace E.1).Completion)) 2)` using `subsingleton_cohomology_two_of_isComplex _ hw`. Conclude with `(congrArg _ (Subsingleton.elim _ 0)).trans (map_zero _)`.

Rewrite using `[h0]`. Distinguish the cases in `hv : v.IsReal`. Rewrite using `[(InfinitePlace.finrank_completion_eq_two_iff (w : InfinitePlace E.1)).2 ⟨hv, hw⟩]`. Break down `placeInv_inl_eq_zero_or_eq_half v ((infIdelesLocalRes (ι.inf v) 2).hom y) with h | h` into its components or cases. Rewrite using `[h, smul_zero]`.

Rewrite using `[h, two_nsmul, QZ.mk_half_add_mk_half]`. Establish `h0 : placeInv (K` using `K) (.inl v) ((infIdelesLocalRes (ι.inf v) 2).hom y) = 0 := by`. Establish `: Subsingleton (cohomology (galUnitsZ v.Completion (AlgebraicClosure v.Completion)) 2)` using `subsingleton_cohomology_two_of_isComplex v (InfinitePlace.not_isReal_iff_isComplex.1 hv)`. Conclude with `(congrArg _ (Subsingleton.elim _ 0)).trans (map_zero _)`. Rewrite using `[h0, smul_zero]`.

Establish `h1 : Module.finrank v.Completion (w : InfinitePlace E.1).Completion = 1` using `(InfinitePlace.finrank_completion_eq_one_iff (w : InfinitePlace E.1)).2 fun h => hw h.2`. Rewrite using `[h1, one_smul]`. Take `⟨ι', hι'⟩` from `exists_infPlaceOfEmbedding_eq w`. Establish `key : ∀ u : v.placesOver E.1, infPlaceOfEmbedding ι' E = u → Module.finrank v.Completion (u : InfinitePlace E.1).Completion = 1 → placeInv (K` using `E) (.inl (u : InfinitePlace E.1)) ((infIdelesLocalRes (ιE.inf (u : InfinitePlace E.1)) 2).hom ((idelesResField K E 2).hom y)) = placeInv (K := K) (.inl v) ((infIdelesLocalRes (ι.inf v) 2).hom y) := by`. Introduce and unpack `u rfl hu`.

Rewrite using `[infIdelesLocalRes_eq_of_algHom ι' (ι.inf v)]`. Conclude with `quadraticInv_infIdelesLocalRes_idelesResField_of_finrank_eq_one ι' (ιE.inf _) y hu`. Conclude with `key w hι' h1`.
-/
theorem placeInv_idelesResField_inl (y : cohomology (limitRep K) 2) (v : InfinitePlace K.1) (w : v.placesOver E.1) :
    placeInv (.inl (w : InfinitePlace E.1))
        (idelesLimitCohomologyEquiv ιE (by norm_num : 1 ≤ 2) ((idelesResField K E 2).hom y) (.inl w)) =
      Module.finrank v.Completion (w : InfinitePlace E.1).Completion •
        placeInv (.inl v) (idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2) y (.inl v)) := by
  rw [idelesLimitCohomologyEquiv_apply_inl, idelesLimitCohomologyEquiv_apply_inl]
  by_cases hw : (w : InfinitePlace E.1).IsComplex
  · have h0 : placeInv (K := E) (.inl (w : InfinitePlace E.1))
        ((infIdelesLocalRes (ιE.inf (w : InfinitePlace E.1)) 2).hom ((idelesResField K E 2).hom y)) = 0 := by
      have : Subsingleton (cohomology (galUnitsZ (w : InfinitePlace E.1).Completion
          (AlgebraicClosure (w : InfinitePlace E.1).Completion)) 2) :=
        subsingleton_cohomology_two_of_isComplex _ hw
      exact (congrArg _ (Subsingleton.elim _ 0)).trans (map_zero _)
    rw [h0]
    by_cases hv : v.IsReal
    · rw [(InfinitePlace.finrank_completion_eq_two_iff (w : InfinitePlace E.1)).2 ⟨hv, hw⟩]
      rcases placeInv_inl_eq_zero_or_eq_half v ((infIdelesLocalRes (ι.inf v) 2).hom y) with h | h
      · rw [h, smul_zero]
      · rw [h, two_nsmul, QZ.mk_half_add_mk_half]
    · have h0 : placeInv (K := K) (.inl v) ((infIdelesLocalRes (ι.inf v) 2).hom y) = 0 := by
        have : Subsingleton (cohomology (galUnitsZ v.Completion (AlgebraicClosure v.Completion)) 2) :=
          subsingleton_cohomology_two_of_isComplex v (InfinitePlace.not_isReal_iff_isComplex.1 hv)
        exact (congrArg _ (Subsingleton.elim _ 0)).trans (map_zero _)
      rw [h0, smul_zero]
  · have h1 : Module.finrank v.Completion (w : InfinitePlace E.1).Completion = 1 :=
      (InfinitePlace.finrank_completion_eq_one_iff (w : InfinitePlace E.1)).2 fun h => hw h.2
    rw [h1, one_smul]
    obtain ⟨ι', hι'⟩ := exists_infPlaceOfEmbedding_eq w
    have key : ∀ u : v.placesOver E.1, infPlaceOfEmbedding ι' E = u →
        Module.finrank v.Completion (u : InfinitePlace E.1).Completion = 1 →
        placeInv (K := E) (.inl (u : InfinitePlace E.1))
            ((infIdelesLocalRes (ιE.inf (u : InfinitePlace E.1)) 2).hom ((idelesResField K E 2).hom y)) =
          placeInv (K := K) (.inl v) ((infIdelesLocalRes (ι.inf v) 2).hom y) := by
      rintro u rfl hu
      rw [infIdelesLocalRes_eq_of_algHom ι' (ι.inf v)]
      exact quadraticInv_infIdelesLocalRes_idelesResField_of_finrank_eq_one ι' (ιE.inf _) y hu
    exact key w hι' h1

end Places

section Sum

/- English proof (translation)
Establish `hD : D = ∑ w ∈ S, DirectSum.of _ w (D w)`. Use `DFinsupp.ext fun w => ?_` and prove the remaining obligations. Rewrite using `[DFinsupp.finsetSum_apply]`. Distinguish the cases in `hw : w ∈ S`. Rewrite using `[Finset.sum_eq_single w (fun b _ hb => DirectSum.of_eq_of_ne _ _ _ (Ne.symm hb)) (fun h => absurd hw h), DirectSum.of_eq_same]`.

Rewrite using `[hS w hw, Finset.sum_eq_zero fun b hb => DirectSum.of_eq_of_ne _ _ _ (by rintro rfl; exact hw hb)]`. Use `conv_lhs => rw [hD]`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun w _ => sumPlaceInv_of w (D w)`.
-/
theorem sumPlaceInv_eq_sum (D : ⨁ w : Place E.1, localGaloisCohomology E 2 w) (S : Finset (Place E.1))
    (hS : ∀ w ∉ S, D w = 0) : sumPlaceInv E D = ∑ w ∈ S, placeInv w (D w) := by
  classical
  have hD : D = ∑ w ∈ S, DirectSum.of _ w (D w) := by
    refine DFinsupp.ext fun w => ?_
    rw [DFinsupp.finsetSum_apply]
    by_cases hw : w ∈ S
    · rw [Finset.sum_eq_single w (fun b _ hb => DirectSum.of_eq_of_ne _ _ _ (Ne.symm hb))
        (fun h => absurd hw h), DirectSum.of_eq_same]
    · rw [hS w hw, Finset.sum_eq_zero fun b hb => DirectSum.of_eq_of_ne _ _ _ (by rintro rfl; exact hw hb)]
  conv_lhs => rw [hD]
  rw [map_sum]
  exact Finset.sum_congr rfl fun w _ => sumPlaceInv_of w (D w)

set_option maxHeartbeats 4000000 in
open Classical in

/- English proof (translation)
Use `set y := (idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2)).symm (DirectSum.of _ u t) with hy_def`. Establish `hy : idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2) y = DirectSum.of _ u t` using `AddEquiv.apply_symm_apply _ _`. Use `set D := idelesLimitCohomologyEquiv ιE (by norm_num : 1 ≤ 2) ((idelesResField K E 2).hom y) with hD_def`. Rewrite using `[idelesSumInv_apply, idelesSumInv_apply, hy, sumPlaceInv_of]`. Establish `hinl : ∀ w : InfinitePlace E.1, placeInv (.inl w) (D (.inl w)) = Module.finrank (w.comap (algebraMap K.1 E.1)).Completion w.Completion • placeInv (.inl (w.comap (algebraMap K.1 E.1))) (DirectSum.of (localGaloisCohomology K 2) u t (.inl (w.comap (algebraMap K.1 E.1))))` using `fun w => by`.

Rewrite using `[← hy]`. Conclude with `placeInv_idelesResField_inl ι ιE y (w.comap (algebraMap K.1 E.1)) ⟨w, ⟨rfl⟩⟩`. Establish `hinr : ∀ w : HeightOneSpectrum (𝓞 E.1), placeInv (.inr w) (D (.inr w)) = Module.finrank ((AdeleBaseChange.below K.1 w).adicCompletion K.1) (w.adicCompletion E.1) • placeInv (.inr (AdeleBaseChange.below K.1 w)) (DirectSum.of (localGaloisCohomology K 2) u t (.inr (AdeleBaseChange.b …` using `fun w => by`. Rewrite using `[← hy]`. Conclude with `placeInv_idelesResField_inr ι ιE y (AdeleBaseChange.below K.1 w) ⟨w, AdeleBaseChange.liesOver_below w⟩`.

Break down `u with v | v` into its components or cases. Set `S : Finset (Place E.1)` to `Finset.univ.map ⟨fun w : v.placesOver E.1 => (.inl (w : InfinitePlace E.1) : Place E.1), fun a b h => Subtype.ext (Sum.inl_injective h)⟩`. Establish `hS : ∀ w ∉ S, D w = 0`. Introduce `w hw`. Apply `placeInv_injective w` to reduce the goal to its premises.

Rewrite using `[map_zero]`. Break down `w with w | w` into its components or cases. Rewrite using `[hinl]`. Distinguish the cases in `hv : w.comap (algebraMap K.1 E.1) = v`. Conclude with `absurd (Finset.mem_map.2 ⟨(⟨w, by subst hv; exact ⟨rfl⟩⟩ : v.placesOver E.1), Finset.mem_univ _, rfl⟩) hw`.

Rewrite using `[DirectSum.of_eq_of_ne _ _ _ (fun h => hv (Sum.inl_injective h)), map_zero, smul_zero]`. Rewrite using `[hinr, DirectSum.of_eq_of_ne _ _ _ Sum.inr_ne_inl, map_zero, smul_zero]`. Rewrite using `[sumPlaceInv_eq_sum D S hS, Finset.sum_map]`. Express the relevant statement in the definitionally equal form `∑ w : v.placesOver E.1, placeInv (.inl (w : InfinitePlace E.1)) (D (.inl (w : InfinitePlace E.1))) = _`. Establish `hw : ∀ w : v.placesOver E.1, placeInv (.inl (w : InfinitePlace E.1)) (D (.inl (w : InfinitePlace E.1))) = Module.finrank v.Completion (w : InfinitePlace E.1).Completion • placeInv (.inl v) t` using `fun w => by`.

Rewrite using `[hD_def, placeInv_idelesResField_inl ι ιE y v w, hy, DirectSum.of_eq_same]`. Rewrite using `[Finset.sum_congr rfl fun w _ => hw w, ← Finset.sum_smul, GroundTheory.Global.InfinitePlace.sum_finrank_completion (L := E.1) v]`. Set `S : Finset (Place E.1)` to `Finset.univ.map ⟨fun w : PlacesOver E.1 v => (.inr w.1 : Place E.1), fun a b h => Subtype.ext (Sum.inr_injective h)⟩`. Establish `hS : ∀ w ∉ S, D w = 0`. Introduce `w hw`.

Apply `placeInv_injective w` to reduce the goal to its premises. Rewrite using `[map_zero]`. Break down `w with w | w` into its components or cases. Rewrite using `[hinl, DirectSum.of_eq_of_ne _ _ _ Sum.inl_ne_inr, map_zero, smul_zero]`. Rewrite using `[hinr]`.

Distinguish the cases in `hv : AdeleBaseChange.below K.1 w = v`. Use `absurd (Finset.mem_map.2 ⟨(⟨w, ?_⟩ : PlacesOver E.1 v), Finset.mem_univ _, rfl⟩) hw` and prove the remaining obligations. Rewrite using `[← hv]`. Conclude with `AdeleBaseChange.liesOver_below w`. Rewrite using `[DirectSum.of_eq_of_ne _ _ _ (fun h => hv (Sum.inr_injective h)), map_zero, smul_zero]`.

Rewrite using `[sumPlaceInv_eq_sum D S hS, Finset.sum_map]`. Express the relevant statement in the definitionally equal form `∑ w : PlacesOver E.1 v, placeInv (.inr w.1) (D (.inr w.1)) = _`. Establish `hw : ∀ w : PlacesOver E.1 v, placeInv (.inr w.1) (D (.inr w.1)) = Module.finrank (v.adicCompletion K.1) (w.1.adicCompletion E.1) • placeInv (.inr v) t` using `fun w => by`. Rewrite using `[hD_def, placeInv_idelesResField_inr ι ιE y v w, hy, DirectSum.of_eq_same]`. Rewrite using `[Finset.sum_congr rfl fun w _ => hw w, ← Finset.sum_smul, sum_finrank_eq E.1 v]`.
-/
theorem idelesSumInv_idelesResField_of (u : Place K.1) (t : localGaloisCohomology K 2 u) :
    idelesSumInv ιE ((idelesResField K E 2).hom
        ((idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2)).symm (DirectSum.of _ u t))) =
      Module.finrank K.1 E.1 •
        idelesSumInv ι ((idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2)).symm (DirectSum.of _ u t)) := by
  classical
  set y := (idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2)).symm (DirectSum.of _ u t) with hy_def
  have hy : idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2) y = DirectSum.of _ u t :=
    AddEquiv.apply_symm_apply _ _
  set D := idelesLimitCohomologyEquiv ιE (by norm_num : 1 ≤ 2) ((idelesResField K E 2).hom y) with hD_def
  rw [idelesSumInv_apply, idelesSumInv_apply, hy, sumPlaceInv_of]

  have hinl : ∀ w : InfinitePlace E.1, placeInv (.inl w) (D (.inl w)) =
      Module.finrank (w.comap (algebraMap K.1 E.1)).Completion w.Completion •
        placeInv (.inl (w.comap (algebraMap K.1 E.1)))
          (DirectSum.of (localGaloisCohomology K 2) u t (.inl (w.comap (algebraMap K.1 E.1)))) := fun w => by
    rw [← hy]
    exact placeInv_idelesResField_inl ι ιE y (w.comap (algebraMap K.1 E.1)) ⟨w, ⟨rfl⟩⟩
  have hinr : ∀ w : HeightOneSpectrum (𝓞 E.1), placeInv (.inr w) (D (.inr w)) =
      Module.finrank ((AdeleBaseChange.below K.1 w).adicCompletion K.1) (w.adicCompletion E.1) •
        placeInv (.inr (AdeleBaseChange.below K.1 w))
          (DirectSum.of (localGaloisCohomology K 2) u t (.inr (AdeleBaseChange.below K.1 w))) := fun w => by
    rw [← hy]
    exact placeInv_idelesResField_inr ι ιE y (AdeleBaseChange.below K.1 w) ⟨w, AdeleBaseChange.liesOver_below w⟩
  rcases u with v | v
  ·
    let S : Finset (Place E.1) := Finset.univ.map ⟨fun w : v.placesOver E.1 => (.inl (w : InfinitePlace E.1) :
      Place E.1), fun a b h => Subtype.ext (Sum.inl_injective h)⟩
    have hS : ∀ w ∉ S, D w = 0 := by
      intro w hw
      apply placeInv_injective w
      rw [map_zero]
      rcases w with w | w
      · rw [hinl]
        by_cases hv : w.comap (algebraMap K.1 E.1) = v
        · exact absurd (Finset.mem_map.2 ⟨(⟨w, by subst hv; exact ⟨rfl⟩⟩ : v.placesOver E.1), Finset.mem_univ _, rfl⟩) hw
        · rw [DirectSum.of_eq_of_ne _ _ _ (fun h => hv (Sum.inl_injective h)), map_zero, smul_zero]
      · rw [hinr, DirectSum.of_eq_of_ne _ _ _ Sum.inr_ne_inl, map_zero, smul_zero]
    rw [sumPlaceInv_eq_sum D S hS, Finset.sum_map]
    change ∑ w : v.placesOver E.1, placeInv (.inl (w : InfinitePlace E.1)) (D (.inl (w : InfinitePlace E.1))) = _
    have hw : ∀ w : v.placesOver E.1, placeInv (.inl (w : InfinitePlace E.1)) (D (.inl (w : InfinitePlace E.1))) =
        Module.finrank v.Completion (w : InfinitePlace E.1).Completion • placeInv (.inl v) t := fun w => by
      rw [hD_def, placeInv_idelesResField_inl ι ιE y v w, hy, DirectSum.of_eq_same]
    rw [Finset.sum_congr rfl fun w _ => hw w, ← Finset.sum_smul,
      GroundTheory.Global.InfinitePlace.sum_finrank_completion (L := E.1) v]
  ·
    let S : Finset (Place E.1) := Finset.univ.map ⟨fun w : PlacesOver E.1 v => (.inr w.1 : Place E.1),
      fun a b h => Subtype.ext (Sum.inr_injective h)⟩
    have hS : ∀ w ∉ S, D w = 0 := by
      intro w hw
      apply placeInv_injective w
      rw [map_zero]
      rcases w with w | w
      · rw [hinl, DirectSum.of_eq_of_ne _ _ _ Sum.inl_ne_inr, map_zero, smul_zero]
      · rw [hinr]
        by_cases hv : AdeleBaseChange.below K.1 w = v
        · refine absurd (Finset.mem_map.2 ⟨(⟨w, ?_⟩ : PlacesOver E.1 v), Finset.mem_univ _, rfl⟩) hw
          rw [← hv]
          exact AdeleBaseChange.liesOver_below w
        · rw [DirectSum.of_eq_of_ne _ _ _ (fun h => hv (Sum.inr_injective h)), map_zero, smul_zero]
    rw [sumPlaceInv_eq_sum D S hS, Finset.sum_map]
    change ∑ w : PlacesOver E.1 v, placeInv (.inr w.1) (D (.inr w.1)) = _
    have hw : ∀ w : PlacesOver E.1 v, placeInv (.inr w.1) (D (.inr w.1)) =
        Module.finrank (v.adicCompletion K.1) (w.1.adicCompletion E.1) • placeInv (.inr v) t := fun w => by
      rw [hD_def, placeInv_idelesResField_inr ι ιE y v w, hy, DirectSum.of_eq_same]
    rw [Finset.sum_congr rfl fun w _ => hw w, ← Finset.sum_smul, sum_finrank_eq E.1 v]

/- English proof (translation)
Use `set Φ := idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2)`. Take `⟨D, rfl⟩` from `Φ.symm.surjective y`. Rewrite using `[← DirectSum.sum_support_of D, map_sum, map_sum, map_sum, map_sum, Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun u _ => idelesSumInv_idelesResField_of ι ιE u (D u)`.
-/
theorem idelesSumInv_idelesResField (y : cohomology (limitRep K) 2) :
    idelesSumInv ιE ((idelesResField K E 2).hom y) = Module.finrank K.1 E.1 • idelesSumInv ι y := by
  classical
  set Φ := idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2)
  obtain ⟨D, rfl⟩ := Φ.symm.surjective y
  rw [← DirectSum.sum_support_of D, map_sum, map_sum, map_sum, map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun u _ => idelesSumInv_idelesResField_of ι ιE u (D u)

end Sum

end

end GroundTheory.ProfCoh
