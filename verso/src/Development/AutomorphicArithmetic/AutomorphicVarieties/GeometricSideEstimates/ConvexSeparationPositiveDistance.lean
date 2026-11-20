import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.PositivityAtAllPlaces
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.RationalPointRetractionExistsCmDatum
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.FinField
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.V.Lit.Geo

/- English proof (translation)
Rewrite using `[← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mulVec]`.
-/
private theorem dot_cancel {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (f : R →+* S) (g : GL (Fin a) R)
    (x y : Fin a → S) :
    (x ᵥ* (GeneralLinearGroup.map f g).val) ⬝ᵥ ((GeneralLinearGroup.map f g⁻¹).val *ᵥ y) = x ⬝ᵥ y := by
  rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
    Units.val_one, Matrix.one_mulVec]

/- English proof (translation)
Establish `h2` using `congrArg (fun z => (GeneralLinearGroup.map f g).val *ᵥ z) h`. Simplify using `only [Matrix.mulVec_zero] at h2`. Rewrite `h2` using `[Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mulVec]`. Then use the resulting hypothesis.
-/
private theorem back {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (f : R →+* S) (g : GL (Fin a) R)
    (y : Fin a → S) (h : (GeneralLinearGroup.map f g⁻¹).val *ᵥ y = 0) : y = 0 := by
  have h2 := congrArg (fun z => (GeneralLinearGroup.map f g).val *ᵥ z) h
  simp only [Matrix.mulVec_zero] at h2
  rwa [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
    Units.val_one, Matrix.one_mulVec] at h2

/- English proof (translation)
Rewrite using `[pInf_algebraMap, InfinitePlace.norm_embedding_eq]`.
-/
private theorem abs_inf {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (x : E) (w : InfinitePlace E) :
    ‖pInf E (algebraMap E (Ad E) x) w‖ = w x := by
  rw [pInf_algebraMap, InfinitePlace.norm_embedding_eq]

/- English proof (translation)
Introduce `h`. Take `⟨w⟩ : Nonempty (InfinitePlace E)` from `inferInstance`. Establish `h1` using `abs_inf x w`. Rewrite `h1` using `[h]`. Establish `h2` using `InfinitePlace.pos_iff (w := w).2 hx`.

Simplify using `at h1`. Conclude with `h2.ne h1`.
-/
private theorem inf_ne {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (x : E) (hx : x ≠ 0) :
    pInf E (algebraMap E (Ad E) x) ≠ 0 := by
  intro h
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have h1 := abs_inf x w
  rw [h] at h1
  have h2 := InfinitePlace.pos_iff (w := w).2 hx
  simp at h1
  exact h2.ne h1

/- English proof (translation)
Establish `hf` using `UpperTheory.V.Lit.Dr.finField E 1 T hT`. Establish `hf2` using `(hf.subset (Set.diff_subset (t := {0}))).image fun x => ‖pInf E (algebraMap E (Ad E) x)‖⁻¹`. Take `⟨M, hM⟩` from `hf2.bddAbove`. Use `⟨(max M 1)⁻¹, by positivity, fun x hx => ?_⟩` and prove the remaining obligations. Distinguish the cases in `h0 : x = 0`.

Conclude with `Or.inl h0`. Use `right`. Establish `hp : 0 < ‖pInf E (algebraMap E (Ad E) x)‖` using `norm_pos_iff.2 (inf_ne x h0)`. Rewrite using `[inv_le_comm₀ (by positivity) hp]`. Distinguish the cases in `h1 : ∀ w : InfinitePlace E, w x ≤ 1`.

Conclude with `(hM ⟨x, ⟨⟨h1, hx⟩, h0⟩, rfl⟩).trans (le_max_left _ _)`. Use `push Not at h1`. Take `⟨w, hw⟩` from `h1`. Use `le_trans (inv_le_one_of_one_le₀ ?_) (le_max_right _ _)` and prove the remaining obligations. Rewrite `hw` using `[← abs_inf]`.

Conclude with `hw.le.trans (norm_le_pi_norm _ w)`.
-/
private theorem sep {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (T : Set (Af E)) (hT : IsCompact T) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : E, algebraMap E (Af E) x ∈ T → x = 0 ∨ c ≤ ‖pInf E (algebraMap E (Ad E) x)‖ := by
  have hf := UpperTheory.V.Lit.Dr.finField E 1 T hT
  have hf2 := (hf.subset (Set.diff_subset (t := {0}))).image fun x => ‖pInf E (algebraMap E (Ad E) x)‖⁻¹
  obtain ⟨M, hM⟩ := hf2.bddAbove
  refine ⟨(max M 1)⁻¹, by positivity, fun x hx => ?_⟩
  by_cases h0 : x = 0
  · exact Or.inl h0
  right
  have hp : 0 < ‖pInf E (algebraMap E (Ad E) x)‖ := norm_pos_iff.2 (inf_ne x h0)
  rw [inv_le_comm₀ (by positivity) hp]
  by_cases h1 : ∀ w : InfinitePlace E, w x ≤ 1
  · exact (hM ⟨x, ⟨⟨h1, hx⟩, h0⟩, rfl⟩).trans (le_max_left _ _)
  · push Not at h1
    obtain ⟨w, hw⟩ := h1
    refine le_trans (inv_le_one_of_one_le₀ ?_) (le_max_right _ _)
    rw [← abs_inf] at hw
    exact hw.le.trans (norm_le_pi_norm _ w)

/- English proof (translation)
Introduce `E _ _ _ a ha L hL`. Take `⟨T, C, N, hT, H⟩` from `UpperTheory.positivity_at_all_places E a ha`. Take `⟨-, hR, -⟩` from `UpperTheory.rationalPoint_retraction_exists_cmDatum E a ha`. Establish `hc : IsCompact ((fun p : (Fin a → Af E) × (Fin a → Af E) => p.1 ⬝ᵥ p.2) '' ((L : Set (Fin a → Af E)) ×ˢ T))` using `(hL.isCompact.prod hT).image (continuous_fst.dotProduct continuous_snd)`. Take `⟨c, hc0, hsep⟩` from `sep _ hc`.

Use `⟨c, C, N, hc0, fun g => ?_⟩` and prove the remaining obligations. Take `⟨ξ, hξ, h1, h2⟩` from `H (retractOne g)`. Express the relevant statement in the definitionally equal form `(GeneralLinearGroup.map (pFin E) (rt g)⁻¹).val *ᵥ vFin ξ ∈ T at h1`. Express the relevant statement in the definitionally equal form `qht (rt g) * qf ((GeneralLinearGroup.map (pInf E) (rt g)⁻¹).val *ᵥ vInf ξ) ^ N ≤ C at h2`. Use `⟨(GeneralLinearGroup.map (pInf E) (rt g)⁻¹).val *ᵥ vInf ξ, fun h => hξ ?_, (hR g).2.1 ▸ h2, fun v hv => ?_⟩` and prove the remaining obligations.

Establish `h3` using `back _ _ _ h`. Use function extensionality and compare the values at `i`. Assume the negation of the conclusion as `hi`. Conclude with `inf_ne (ξ i) hi (congrFun h3 i)`. Establish `e1 : pt (rt g) v ⬝ᵥ ((GeneralLinearGroup.map (pInf E) (rt g)⁻¹).val *ᵥ vInf ξ) = pInf E (algebraMap E (Ad E) (v ⬝ᵥ ξ))`.

Use `(dot_cancel (pInf E) (rt g) (vInf v) (vInf ξ)).trans ?_` and prove the remaining obligations. Simplify using `only [dotProduct, vInf, map_sum, map_mul]`. Establish `e2 : ptF (rt g) v ⬝ᵥ ((GeneralLinearGroup.map (pFin E) (rt g)⁻¹).val *ᵥ vFin ξ) = algebraMap E (Af E) (v ⬝ᵥ ξ)`. Use `(dot_cancel (pFin E) (rt g) (vFin v) (vFin ξ)).trans ?_` and prove the remaining obligations. Simplify using `only [dotProduct, vFin, map_sum, map_mul]`.

Establish `hv' : ptF (rt g) v ∈ L` using `by rw [(hR g).2.2]; exact hv`. Rewrite using `[e1]`. Break down `hsep (v ⬝ᵥ ξ) ⟨(_, _), ⟨hv', h1⟩, e2⟩ with h | h` into its components or cases. Use `left`. Rewrite using `[h, map_zero, map_zero]`.

Conclude with `Or.inr h`.
-/
theorem UpperTheory.convex_separation_positive_distance :
    ShortCol := by
  intro E _ _ _ a ha L hL
  obtain ⟨T, C, N, hT, H⟩ := UpperTheory.positivity_at_all_places E a ha
  obtain ⟨-, hR, -⟩ := UpperTheory.rationalPoint_retraction_exists_cmDatum E a ha
  have hc : IsCompact ((fun p : (Fin a → Af E) × (Fin a → Af E) => p.1 ⬝ᵥ p.2) '' ((L : Set (Fin a → Af E)) ×ˢ T)) :=
    (hL.isCompact.prod hT).image (continuous_fst.dotProduct continuous_snd)
  obtain ⟨c, hc0, hsep⟩ := sep _ hc
  refine ⟨c, C, N, hc0, fun g => ?_⟩
  obtain ⟨ξ, hξ, h1, h2⟩ := H (retractOne g)
  change (GeneralLinearGroup.map (pFin E) (rt g)⁻¹).val *ᵥ vFin ξ ∈ T at h1
  change qht (rt g) * qf ((GeneralLinearGroup.map (pInf E) (rt g)⁻¹).val *ᵥ vInf ξ) ^ N ≤ C at h2
  refine ⟨(GeneralLinearGroup.map (pInf E) (rt g)⁻¹).val *ᵥ vInf ξ, fun h => hξ ?_, (hR g).2.1 ▸ h2, fun v hv => ?_⟩
  · have h3 := back _ _ _ h
    funext i
    by_contra hi
    exact inf_ne (ξ i) hi (congrFun h3 i)
  · have e1 : pt (rt g) v ⬝ᵥ ((GeneralLinearGroup.map (pInf E) (rt g)⁻¹).val *ᵥ vInf ξ)
        = pInf E (algebraMap E (Ad E) (v ⬝ᵥ ξ)) := by
      refine (dot_cancel (pInf E) (rt g) (vInf v) (vInf ξ)).trans ?_
      simp only [dotProduct, vInf, map_sum, map_mul]
    have e2 : ptF (rt g) v ⬝ᵥ ((GeneralLinearGroup.map (pFin E) (rt g)⁻¹).val *ᵥ vFin ξ)
        = algebraMap E (Af E) (v ⬝ᵥ ξ) := by
      refine (dot_cancel (pFin E) (rt g) (vFin v) (vFin ξ)).trans ?_
      simp only [dotProduct, vFin, map_sum, map_mul]
    have hv' : ptF (rt g) v ∈ L := by rw [(hR g).2.2]; exact hv
    rw [e1]
    rcases hsep (v ⬝ᵥ ξ) ⟨(_, _), ⟨hv', h1⟩, e2⟩ with h | h
    · left; rw [h, map_zero, map_zero]
    · exact Or.inr h
