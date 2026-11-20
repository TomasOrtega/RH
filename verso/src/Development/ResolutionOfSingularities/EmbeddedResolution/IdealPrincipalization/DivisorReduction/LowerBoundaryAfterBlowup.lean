import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Saturation
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateDivisorBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformSubscheme
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictNormalCrossingsBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictNormalCrossingsEraseMember
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtGenericPoint
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ContainedComponentsIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SingleBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReductionBoundary

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
private theorem mem_closeds_compl {α : Type u} [TopologicalSpace α]
    (S : TopologicalSpace.Closeds α) (x : α) : x ∈ S.compl ↔ x ∉ S := Iff.rfl

/- English proof (translation)
Establish `h` using `comap_le_strictTransform (𝟙 Y) F (⊤ : Y.IdealSheafData)`. Rewrite `h` using `[strictTransform_eq_saturation, Scheme.IdealSheafData.comap_id, Scheme.IdealSheafData.comap_id]`. Conclude with `top_le_iff.mp h`.
-/
private theorem saturation_top_eq_top {Y : Scheme.{u}} (F : Y.IdealSheafData) :
    saturation F (⊤ : Y.IdealSheafData) = ⊤ := by
  have h := comap_le_strictTransform (𝟙 Y) F (⊤ : Y.IdealSheafData)
  rw [strictTransform_eq_saturation, Scheme.IdealSheafData.comap_id,
    Scheme.IdealSheafData.comap_id] at h
  exact top_le_iff.mp h

/- English proof (translation)
The claim follows from `Scheme.IdealSheafData.comap_mul A B U.ι`.
-/
private theorem restrictIdeal_mul {X : Scheme.{u}} (A B : X.IdealSheafData) (U : X.Opens) :
    restrictIdeal (A * B) U = restrictIdeal A U * restrictIdeal B U :=
  Scheme.IdealSheafData.comap_mul A B U.ι

/- English proof (translation)
Establish `h1` using `restrictIdeal_strictTransform (𝟙 X) Z D U`. Establish `h2` using `strictTransform_comp_ι U (𝟙 U.toScheme) Z D`. Rewrite `h2` using `[Category.id_comp]`. Rewrite using `[h1, Category.comp_id, h2, strictTransform_eq_saturation, Scheme.IdealSheafData.comap_id, Scheme.IdealSheafData.comap_id]`.
-/
private theorem restrictIdeal_strictTransform_id {X : Scheme.{u}} [IsLocallyNoetherian X]
    (Z D : X.IdealSheafData) (U : X.Opens) :
    restrictIdeal (Blowup.strictTransform (𝟙 X) Z D) U =
      saturation (restrictIdeal Z U) (restrictIdeal D U) := by
  have h1 := restrictIdeal_strictTransform (𝟙 X) Z D U
  have h2 := strictTransform_comp_ι U (𝟙 U.toScheme) Z D
  rw [Category.id_comp] at h2
  rw [h1, Category.comp_id, h2, strictTransform_eq_saturation, Scheme.IdealSheafData.comap_id,
    Scheme.IdealSheafData.comap_id]

/- English proof (translation)
The claim follows from `| [], _ => rfl | a :: t, h => by have h0 : g a = a := h 0 (Nat.succ_pos _) have ht : t.map g = t := map_eq_self_of_getElem g t (fun i hi => h (i + 1) (Nat.succ_lt_succ hi)) rw [List.map_cons, h0, ht]`.
-/
private theorem map_eq_self_of_getElem {α : Type u} (g : α → α) : ∀ l : List α,
    (∀ (i : ℕ) (h : i < l.length), g (l[i]'h) = l[i]'h) → l.map g = l
  | [], _ => rfl
  | a :: t, h => by
      have h0 : g a = a := h 0 (Nat.succ_pos _)
      have ht : t.map g = t :=
        map_eq_self_of_getElem g t (fun i hi => h (i + 1) (Nat.succ_lt_succ hi))
      rw [List.map_cons, h0, ht]

/- English proof (translation)
The claim follows from `| [], _, _ => rfl | _ :: t, 0, h => by have ht : t.map g = t := map_eq_self_of_getElem g t (fun i hi => h (i + 1) (Nat.succ_lt_succ hi) (Nat.succ_ne_zero i)) show t.map g = t exact ht | a :: t, (m + 1), h => by have h0 : g a = a := h 0 (Nat.succ_pos _) (Nat.succ_ne_zero m).symm h …`.
-/
private theorem eraseIdx_map_eq {α : Type u} (g : α → α) : ∀ (l : List α) (j : ℕ),
    (∀ (i : ℕ) (h : i < l.length), i ≠ j → g (l[i]'h) = l[i]'h) →
    (l.map g).eraseIdx j = l.eraseIdx j
  | [], _, _ => rfl
  | _ :: t, 0, h => by
      have ht : t.map g = t :=
        map_eq_self_of_getElem g t
          (fun i hi => h (i + 1) (Nat.succ_lt_succ hi) (Nat.succ_ne_zero i))
      show t.map g = t
      exact ht
  | a :: t, (m + 1), h => by
      have h0 : g a = a := h 0 (Nat.succ_pos _) (Nat.succ_ne_zero m).symm
      have ht := eraseIdx_map_eq g t m
        (fun i hi hij => h (i + 1) (Nat.succ_lt_succ hi) (fun e => hij (by omega)))
      show g a :: (t.map g).eraseIdx m = a :: t.eraseIdx m
      rw [h0, ht]

/- English proof (translation)
Use `hV.isNoetherian` as an intermediate fact. Rewrite using `[Scheme.IdealSheafData.comap_id]`. Use `eq_of_locally_restrictIdeal_eq _ _ fun x => ?_` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ (DivisorReduction.containedComponentsIdeal T j hj).support`. Take `⟨U, hxU, n, c, a, b, hab, hnone, hsome, hinj, hZU⟩` from `exists_etaleChart_containedComponentsIdeal T hV j hj x hx`.

Use `⟨U, hxU, ?_⟩` and prove the remaining obligations. Rewrite using `[restrictIdeal_strictTransform_id, hZU]`. Consider the cases of `hai : a i with`. Consider the case `none`. Rewrite using `[hnone i hi hai]`.

Conclude with `saturation_top_eq_top _`. Consider the case `some t`. Establish `htb : t ≠ b`. Introduce `e`. Apply `hij` to reduce the goal to its premises.

Use `hinj i j hi hj b ?_ hab` and prove the remaining obligations. Rewrite using `[hai, e]`. Establish `ht` using `hsome i hi t hai`. Establish `hq1 : QuasiCompact (saturationι (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨i, hi⟩))` using `quasiCompact_saturationι_of_isLocallyNoetherian _ _`. Establish `hq2` using `quasiCompact_saturationι_restrictIdeal (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨i, hi⟩) U`.

Rewrite `hq2` using `[hZU, ht]`. Use `hq2` as an intermediate fact. Rewrite using `[ht]`. Conclude with `c.saturation_coordIdeal_of_ne t b htb`. Use `⟨(DivisorReduction.containedComponentsIdeal T j hj).support.compl, (mem_closeds_compl _ _).mpr hx, ?_⟩` and prove the remaining obligations.

Establish `hst` using `restrictIdeal_strictTransform_eq_comap_of_notMem_support (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨i, hi⟩) (DivisorReduction.containedComponentsIdeal T j hj).support.compl (fun y hy => by`. Establish `h' : y ∉ (DivisorReduction.containedComponentsIdeal T j hj).support` using `(mem_closeds_compl _ y).mp hy`. Simplify using `using h')`. Rewrite using `[hst, Scheme.IdealSheafData.comap_id]`.
-/
theorem strictTransform_comap_boundary_of_ne (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) (i : ℕ) (hi : i < T.boundary.length) (hij : i ≠ j) :
    Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)
        ((T.boundary.get ⟨i, hi⟩).comap (𝟙 T.scheme)) = T.boundary.get ⟨i, hi⟩ := by
  have := hV.isNoetherian
  rw [Scheme.IdealSheafData.comap_id]
  refine eq_of_locally_restrictIdeal_eq _ _ fun x => ?_
  by_cases hx : x ∈ (DivisorReduction.containedComponentsIdeal T j hj).support
  · obtain ⟨U, hxU, n, c, a, b, hab, hnone, hsome, hinj, hZU⟩ :=
      exists_etaleChart_containedComponentsIdeal T hV j hj x hx
    refine ⟨U, hxU, ?_⟩
    rw [restrictIdeal_strictTransform_id, hZU]
    cases hai : a i with
    | none =>
        rw [hnone i hi hai]
        exact saturation_top_eq_top _
    | some t =>
        have htb : t ≠ b := by
          intro e
          apply hij
          refine hinj i j hi hj b ?_ hab
          rw [hai, e]
        have ht := hsome i hi t hai
        have hq1 : QuasiCompact
            (saturationι (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨i, hi⟩)) :=
          quasiCompact_saturationι_of_isLocallyNoetherian _ _
        have hq2 := quasiCompact_saturationι_restrictIdeal
          (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨i, hi⟩) U
        rw [hZU, ht] at hq2
        have := hq2
        rw [ht]
        exact c.saturation_coordIdeal_of_ne t b htb
  · refine ⟨(DivisorReduction.containedComponentsIdeal T j hj).support.compl,
      (mem_closeds_compl _ _).mpr hx, ?_⟩
    have hst := restrictIdeal_strictTransform_eq_comap_of_notMem_support (𝟙 T.scheme)
      (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨i, hi⟩)
      (DivisorReduction.containedComponentsIdeal T j hj).support.compl
      (fun y hy => by
        have h' : y ∉ (DivisorReduction.containedComponentsIdeal T j hj).support :=
          (mem_closeds_compl _ y).mp hy
        simpa using h')
    rw [hst, Scheme.IdealSheafData.comap_id]

/- English proof (translation)
Assemble the required witnesses or components as `⟨isLocallyGeneratedByNonZeroDivisor_containedComponentsIdeal T hV j hj, smooth_subschemeι_containedComponentsIdeal_comp T hV j hj⟩`.
-/
theorem isSmoothDivisor_containedComponentsIdeal (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    IsSmoothDivisor T.structMap (DivisorReduction.containedComponentsIdeal T j hj) :=
  ⟨isLocallyGeneratedByNonZeroDivisor_containedComponentsIdeal T hV j hj, smooth_subschemeι_containedComponentsIdeal_comp T hV j hj⟩

/- English proof (translation)
Use `hV.isNoetherian` as an intermediate fact. Rewrite using `[Scheme.IdealSheafData.comap_id]`. Use `eq_of_locally_restrictIdeal_eq _ _ fun x => ?_` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ (DivisorReduction.containedComponentsIdeal T j hj).support`. Take `⟨U, hxU, n, c, a, b, hab, hnone, hsome, hinj, hZU⟩` from `exists_etaleChart_containedComponentsIdeal T hV j hj x hx`.

Use `⟨U, hxU, ?_⟩` and prove the remaining obligations. Establish `hDj` using `hsome j hj b hab`. Establish `hq1 : QuasiCompact (saturationι (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨j, hj⟩))` using `quasiCompact_saturationι_of_isLocallyNoetherian _ _`. Establish `hq2` using `quasiCompact_saturationι_restrictIdeal (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨j, hj⟩) U`. Rewrite `hq2` using `[hZU, hDj]`.

Use `hq2` as an intermediate fact. Rewrite using `[restrictIdeal_mul, restrictIdeal_strictTransform_id, hZU, hDj, c.saturation_coordIdeal_self b, Scheme.IdealSheafData.top_mul]`. Use `⟨(DivisorReduction.containedComponentsIdeal T j hj).support.compl, (mem_closeds_compl _ _).mpr hx, ?_⟩` and prove the remaining obligations. Establish `hZtop : restrictIdeal (DivisorReduction.containedComponentsIdeal T j hj) (DivisorReduction.containedComponentsIdeal T j hj).support.compl = ⊤`. Establish `h` using `restrictIdeal_exceptionalIdeal_eq_top_of_notMem_support (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj) (DivisorReduction.containedComponentsIdeal T j hj).support.compl (fun y hy => by`.

Establish `h' : y ∉ (DivisorReduction.containedComponentsIdeal T j hj).support` using `(mem_closeds_compl _ y).mp hy`. Simplify using `using h')`. Rewrite `h` using `[exceptionalIdeal_id]`. Then use the resulting hypothesis. Establish `hst` using `restrictIdeal_strictTransform_eq_comap_of_notMem_support (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨j, hj⟩) (DivisorReduction.containedComponentsIdeal T j hj).support.compl (fun y hy => by`. Establish `h' : y ∉ (DivisorReduction.containedComponentsIdeal T j hj).support` using `(mem_closeds_compl _ y).mp hy`.

Simplify using `using h')`. Rewrite using `[restrictIdeal_mul, hst, Scheme.IdealSheafData.comap_id, hZtop, Scheme.IdealSheafData.mul_top]`.
-/
theorem strictTransform_mul_containedComponentsIdeal (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)
          ((T.boundary.get ⟨j, hj⟩).comap (𝟙 T.scheme)) *
        DivisorReduction.containedComponentsIdeal T j hj =
      T.boundary.get ⟨j, hj⟩ := by
  have := hV.isNoetherian
  rw [Scheme.IdealSheafData.comap_id]
  refine eq_of_locally_restrictIdeal_eq _ _ fun x => ?_
  by_cases hx : x ∈ (DivisorReduction.containedComponentsIdeal T j hj).support
  · obtain ⟨U, hxU, n, c, a, b, hab, hnone, hsome, hinj, hZU⟩ :=
      exists_etaleChart_containedComponentsIdeal T hV j hj x hx
    refine ⟨U, hxU, ?_⟩
    have hDj := hsome j hj b hab
    have hq1 : QuasiCompact
        (saturationι (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨j, hj⟩)) :=
      quasiCompact_saturationι_of_isLocallyNoetherian _ _
    have hq2 := quasiCompact_saturationι_restrictIdeal
      (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨j, hj⟩) U
    rw [hZU, hDj] at hq2
    have := hq2
    rw [restrictIdeal_mul, restrictIdeal_strictTransform_id, hZU, hDj,
      c.saturation_coordIdeal_self b, Scheme.IdealSheafData.top_mul]
  · refine ⟨(DivisorReduction.containedComponentsIdeal T j hj).support.compl,
      (mem_closeds_compl _ _).mpr hx, ?_⟩
    have hZtop : restrictIdeal (DivisorReduction.containedComponentsIdeal T j hj)
        (DivisorReduction.containedComponentsIdeal T j hj).support.compl = ⊤ := by
      have h := restrictIdeal_exceptionalIdeal_eq_top_of_notMem_support (𝟙 T.scheme)
        (DivisorReduction.containedComponentsIdeal T j hj) (DivisorReduction.containedComponentsIdeal T j hj).support.compl
        (fun y hy => by
          have h' : y ∉ (DivisorReduction.containedComponentsIdeal T j hj).support :=
            (mem_closeds_compl _ y).mp hy
          simpa using h')
      rwa [exceptionalIdeal_id] at h
    have hst := restrictIdeal_strictTransform_eq_comap_of_notMem_support (𝟙 T.scheme)
      (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨j, hj⟩)
      (DivisorReduction.containedComponentsIdeal T j hj).support.compl
      (fun y hy => by
        have h' : y ∉ (DivisorReduction.containedComponentsIdeal T j hj).support :=
          (mem_closeds_compl _ y).mp hy
        simpa using h')
    rw [restrictIdeal_mul, hst, Scheme.IdealSheafData.comap_id, hZtop,
      Scheme.IdealSheafData.mul_top]

/- English proof (translation)
Use `hV.isNoetherian` as an intermediate fact. Rewrite using `[Scheme.IdealSheafData.comap_id, Set.disjoint_right]`. Introduce `x hx`. Take `⟨U, hxU, n, c, a, b, hab, hnone, hsome, hinj, hZU⟩` from `exists_etaleChart_containedComponentsIdeal T hV j hj x hx`. Establish `hDj` using `hsome j hj b hab`.

Establish `hq1 : QuasiCompact (saturationι (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨j, hj⟩))` using `quasiCompact_saturationι_of_isLocallyNoetherian _ _`. Establish `hq2` using `quasiCompact_saturationι_restrictIdeal (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨j, hj⟩) U`. Rewrite `hq2` using `[hZU, hDj]`. Use `hq2` as an intermediate fact. Establish `hres : restrictIdeal (Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨j, hj⟩)) U = ⊤`.

Rewrite using `[restrictIdeal_strictTransform_id, hZU, hDj]`. Conclude with `c.saturation_coordIdeal_self b`. Conclude with `notMem_support_of_mem_opens_of_restrictIdeal_eq_top _ U hres x hxU`.
-/
theorem disjoint_support_strictTransform_containedComponentsIdeal (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    Disjoint
      ((Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)
          ((T.boundary.get ⟨j, hj⟩).comap (𝟙 T.scheme))).support : Set ↥T.scheme)
      (((DivisorReduction.containedComponentsIdeal T j hj).support : Set ↥T.scheme)) := by
  have := hV.isNoetherian
  rw [Scheme.IdealSheafData.comap_id, Set.disjoint_right]
  intro x hx
  obtain ⟨U, hxU, n, c, a, b, hab, hnone, hsome, hinj, hZU⟩ :=
    exists_etaleChart_containedComponentsIdeal T hV j hj x hx
  have hDj := hsome j hj b hab
  have hq1 : QuasiCompact
      (saturationι (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨j, hj⟩)) :=
    quasiCompact_saturationι_of_isLocallyNoetherian _ _
  have hq2 := quasiCompact_saturationι_restrictIdeal
    (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨j, hj⟩) U
  rw [hZU, hDj] at hq2
  have := hq2
  have hres : restrictIdeal (Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)
      (T.boundary.get ⟨j, hj⟩)) U = ⊤ := by
    rw [restrictIdeal_strictTransform_id, hZU, hDj]
    exact c.saturation_coordIdeal_self b
  exact notMem_support_of_mem_opens_of_restrictIdeal_eq_top _ U hres x hxU

/- English proof (translation)
Establish `hlist : (T.boundary.map (fun D => D.comap (𝟙 T.scheme))).map (Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)) = T.boundary.map (fun D => Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj) (D.comap (𝟙 T.sc …`. Simplify using `only [List.map_map, Function.comp_def]`. Establish `key` using `eraseIdx_map_eq (fun D : T.scheme.IdealSheafData => Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj) (D.comap (𝟙 T.scheme))) T.boundary j (fun i h hij => strictTransform_comap_boundary_of_ne T hV j hj i h hij)`. Establish `hlen : j < (T.boundary.map (fun D => Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj) (D.comap (𝟙 T.scheme)))).length`. Simplify using `using hj`.

Use `show ((((T.boundary.map (fun D => D.comap (𝟙 T.scheme))).map (Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj))) ++ [Blowup.exceptionalIdeal (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)]).eraseIdx j).take (T.boundary.length …`. Rewrite using `[hlist, List.eraseIdx_append_of_lt_length hlen, key]`. Conclude with `List.take_left' (List.length_eraseIdx_of_lt hj)`.
-/
theorem take_eraseIdx_lowerBoundaryAfterBlowup (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    ((DivisorReduction.lowerBoundaryAfterBlowup T j hj).eraseIdx j).take (T.boundary.length - 1) =
      T.boundary.eraseIdx j := by
  have hlist : (T.boundary.map (fun D => D.comap (𝟙 T.scheme))).map
        (Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)) =
      T.boundary.map (fun D =>
        Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj) (D.comap (𝟙 T.scheme))) := by
    simp only [List.map_map, Function.comp_def]
  have key := eraseIdx_map_eq
    (fun D : T.scheme.IdealSheafData =>
      Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj) (D.comap (𝟙 T.scheme)))
    T.boundary j
    (fun i h hij => strictTransform_comap_boundary_of_ne T hV j hj i h hij)
  have hlen : j < (T.boundary.map (fun D =>
      Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)
        (D.comap (𝟙 T.scheme)))).length := by
    simpa using hj
  show ((((T.boundary.map (fun D => D.comap (𝟙 T.scheme))).map
        (Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj))) ++
      [Blowup.exceptionalIdeal (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)]).eraseIdx j).take
      (T.boundary.length - 1) = T.boundary.eraseIdx j
  rw [hlist, List.eraseIdx_append_of_lt_length hlen, key]
  exact List.take_left' (List.length_eraseIdx_of_lt hj)

/- English proof (translation)
Rewrite using `[take_eraseIdx_lowerBoundaryAfterBlowup T hV j hj]`. Conclude with `inStrictNormalCrossingPosition_comap_subschemeι_eraseIdx_of_eq T.structMap T.boundary hV.snc j hj (T.boundary.get ⟨j, hj⟩) rfl`.
-/
theorem inStrictNormalCrossingPosition_comap_lowerBoundaryAfterBlowup (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (j : ℕ) (hj : j < T.boundary.length) :
    InStrictNormalCrossingPosition ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap)
      ((((DivisorReduction.lowerBoundaryAfterBlowup T j hj).eraseIdx j).take (T.boundary.length - 1)).map
        fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι) := by
  rw [take_eraseIdx_lowerBoundaryAfterBlowup T hV j hj]
  exact inStrictNormalCrossingPosition_comap_subschemeι_eraseIdx_of_eq T.structMap T.boundary hV.snc j hj
    (T.boundary.get ⟨j, hj⟩) rfl

end DivisorReductionBoundary

end FunctorialResolution.EmbeddedResolution

end
