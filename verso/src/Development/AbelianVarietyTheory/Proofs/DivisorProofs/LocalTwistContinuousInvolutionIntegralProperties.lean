import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.BCT.ThBasic

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Establish `h` using `(GlobalTheory.T.placeConjugation_properties_cmField E hU w).2.2.1 x`. Express the relevant statement in the definitionally equal form `Valued.v (cj w x) ≤ 1`. Rewrite using `[h]`. Conclude with `hx`.
-/
theorem cj_mem_integers (hU : Unr E) (w : Pl E) (x : w.adicCompletion E) (hx : x ∈ Ov E w) : cj w x ∈ Ov E w := by
  have h := (GlobalTheory.T.placeConjugation_properties_cmField E hU w).2.2.1 x
  change Valued.v (cj w x) ≤ 1
  rw [h]; exact hx

/- English proof (translation)
Unfold `thL`. Use `split_ifs`. Both sides reduce to the same expression. Conclude with `GlobalTheory.ThetaPull.thetaGL_thetaGL _ (GlobalTheory.T.placeConjugation_properties_cmField E hU w).2.1 g`.
-/
theorem thL_thL (hU : Unr E) (n : ℕ) (w : Pl E) (g : GLw n w) : thL n w (thL n w g) = g := by
  unfold thL
  split_ifs
  · rfl
  · exact GlobalTheory.ThetaPull.thetaGL_thetaGL _ (GlobalTheory.T.placeConjugation_properties_cmField E hU w).2.1 g

/- English proof (translation)
Unfold `thL`. Use `split_ifs`. Conclude with `continuous_id`. Conclude with `GlobalTheory.ThetaPull.continuous_thetaGL _ (GlobalTheory.T.placeConjugation_properties_cmField E hU w).1`.
-/
theorem continuous_thL (hU : Unr E) (n : ℕ) (w : Pl E) : Continuous (thL n w) := by
  unfold thL
  split_ifs
  · exact continuous_id
  · exact GlobalTheory.ThetaPull.continuous_thetaGL _ (GlobalTheory.T.placeConjugation_properties_cmField E hU w).1

/- English proof (translation)
Unfold `thL`. Use `split_ifs`. Conclude with `hk`. Take `⟨k', rfl⟩` from `hk`. Set `c' : Ov E w →+* Ov E w` to `(cj w).restrict (Ov E w) (Ov E w) (cj_mem_integers hU w)`.

Use `⟨thetaGL n c' k', ?_⟩` and prove the remaining obligations. Conclude with `GlobalTheory.ThetaPull.map_thetaGL (Ov E w).subtype c' (cj w) (fun x => rfl) k'`.
-/
theorem thL_mem_KGL (hU : Unr E) (n : ℕ) (w : Pl E) (k : GLw n w) (hk : k ∈ GlobalTheory.LFun.KGL w n) :
    thL n w k ∈ GlobalTheory.LFun.KGL w n := by
  unfold thL
  split_ifs
  · exact hk
  · obtain ⟨k', rfl⟩ := hk
    let c' : Ov E w →+* Ov E w := (cj w).restrict (Ov E w) (Ov E w) (cj_mem_integers hU w)
    refine ⟨thetaGL n c' k', ?_⟩
    exact GlobalTheory.ThetaPull.map_thetaGL (Ov E w).subtype c' (cj w) (fun x => rfl) k'

/- English proof (translation)
Unfold `nrmL`. Establish `h2` using `thL_thL hU n w g`. Unfold `thL at h2 ⊢`. Use `split_ifs with hs`. Simplify using `[hs] at *`.

Simplify using `only [hs, if_false] at h2 ⊢`. Rewrite using `[map_mul, map_mul, map_inv, h2]`. Use `group`.
-/
theorem nrmL_twist (hU : Unr E) (n : ℕ) (w : Pl E) (g y : GLw n w) :
    nrmL n w (g⁻¹ * y * thL n w g) = g⁻¹ * nrmL n w y * g := by
  unfold nrmL
  have h2 := thL_thL hU n w g
  unfold thL at h2 ⊢
  split_ifs with hs
  · simp [hs] at *
  · simp only [hs, if_false] at h2 ⊢
    rw [map_mul, map_mul, map_inv, h2]
    group

/- English proof (translation)
Unfold `UL`. Use `split_ifs`. Conclude with `isClosed_univ`. Establish `hc` using `(GlobalTheory.T.placeConjugation_properties_cmField E hU w).1`. Establish `: Continuous fun g : GLw n w => cT (cj w) (g : Matrix (Fin n) (Fin n) _) * 1 * (g : Matrix (Fin n) (Fin n) _)`.

Use `Continuous.mul (Continuous.mul ?_ continuous_const) Units.continuous_val` and prove the remaining obligations. Conclude with `continuous_matrix fun i j => hc.comp (Units.continuous_val.matrix_elem _ _)`. Conclude with `isClosed_singleton.preimage this`.
-/
theorem isClosed_UL (hU : Unr E) (n : ℕ) (w : Pl E) : IsClosed (UL n w : Set (GLw n w)) := by
  unfold UL
  split_ifs
  · exact isClosed_univ
  · have hc := (GlobalTheory.T.placeConjugation_properties_cmField E hU w).1
    have : Continuous fun g : GLw n w => cT (cj w) (g : Matrix (Fin n) (Fin n) _) * 1 * (g : Matrix (Fin n) (Fin n) _) := by
      refine Continuous.mul (Continuous.mul ?_ continuous_const) Units.continuous_val
      exact continuous_matrix fun i j => hc.comp (Units.continuous_val.matrix_elem _ _)
    exact isClosed_singleton.preimage this

/- English proof (translation)
Unfold `nrmL locEl`. Use `split_ifs with hs`. Conclude with `(Matrix.charpoly_map _ _)`. Establish `hm : thetaGL n (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ) = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (thE E n δ)` using `(GlobalTheory.ThetaPull.map_thetaGL _ _ _ (fun x => ((GlobalTheory.T.placeConjugation_properties_cmField E hU w).2.2.2.1 hs).1 x |>.symm) δ).symm`. Rewrite using `[hm, ← map_mul]`.

Conclude with `(Matrix.charpoly_map _ _)`.
-/
theorem charpoly_nrmL (hU : Unr E) (n : ℕ) (w : Pl E) (δ : GL (Fin n) E) :
    (nrmL n w (locEl n w δ)).val.charpoly = atPl w (δ * thE E n δ).val.charpoly := by
  unfold nrmL locEl
  split_ifs with hs
  · exact (Matrix.charpoly_map _ _)
  · have hm : thetaGL n (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ) =
        GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (thE E n δ) :=
      (GlobalTheory.ThetaPull.map_thetaGL _ _ _ (fun x => ((GlobalTheory.T.placeConjugation_properties_cmField E hU w).2.2.2.1 hs).1 x |>.symm) δ).symm
    rw [hm, ← map_mul]
    exact (Matrix.charpoly_map _ _)

/- English proof (translation)
Unfold `UL`. Use `split_ifs with hs`. Conclude with `Subgroup.mem_top _`. Establish `hp` using `((GlobalTheory.T.placeConjugation_properties_cmField E hU w).2.2.2.1 hs).2.2.1`. Establish `hx` using `x.2`.

Express the relevant statement in the definitionally equal form `cT (conjAd E) (x.1 : Matrix (Fin n) (Fin n) (Ad E)) * 1 * (x.1 : Matrix (Fin n) (Fin n) (Ad E)) = 1 at hx`. Express the relevant statement in the definitionally equal form `cT (cj w) ((cLoc w x : GLw n w) : Matrix (Fin n) (Fin n) _) * 1 * ((cLoc w x : GLw n w) : Matrix (Fin n) (Fin n) _) = 1`. Use `congrArg (((pLoc E w).comp (pFin E)).mapMatrix) hx` as an intermediate fact. Rewrite `this` using `[map_one, map_mul, map_mul, map_one]`. Use `this using 3` and compare the differences between its conclusion and the goal.

Use `Matrix.ext fun i j => ?_ show cj w (pLoc E w (pFin E ((x.1 : Matrix (Fin n) (Fin n) (Ad E)) j i))) = pLoc E w (pFin E (conjAd E ((x.1 : Matrix (Fin n) (Fin n) (Ad E)) j i)))` and prove the remaining obligations. Rewrite using `[← hp]`. Both sides reduce to the same expression. Both sides reduce to the same expression.
-/
theorem cLoc_mem_UL (hU : Unr E) (n : ℕ) (w : Pl E) (x : UA E n) : cLoc w x ∈ UL n w := by
  unfold UL
  split_ifs with hs
  · exact Subgroup.mem_top _
  · have hp := ((GlobalTheory.T.placeConjugation_properties_cmField E hU w).2.2.2.1 hs).2.2.1
    have hx := x.2
    change cT (conjAd E) (x.1 : Matrix (Fin n) (Fin n) (Ad E)) * 1 * (x.1 : Matrix (Fin n) (Fin n) (Ad E)) = 1 at hx
    change cT (cj w) ((cLoc w x : GLw n w) : Matrix (Fin n) (Fin n) _) * 1 * ((cLoc w x : GLw n w) : Matrix (Fin n) (Fin n) _) = 1
    have := congrArg (((pLoc E w).comp (pFin E)).mapMatrix) hx
    rw [map_one, map_mul, map_mul, map_one] at this
    convert this using 3
    · refine Matrix.ext fun i j => ?_
      show cj w (pLoc E w (pFin E ((x.1 : Matrix (Fin n) (Fin n) (Ad E)) j i))) =
        pLoc E w (pFin E (conjAd E ((x.1 : Matrix (Fin n) (Fin n) (Ad E)) j i)))
      rw [← hp]
      rfl
    · rfl

/- English proof (translation)
Introduce `E _ _ _ hU n w`. Establish `hK` using `GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n`. Use `⟨continuous_thL hU n w, thL_thL hU n w, thL_mem_KGL hU n w, nrmL_twist hU n w, hK.1, hK.2, ?_, ?_, charpoly_nrmL hU n w, fun x _ => cLoc_mem_UL hU n w x⟩` and prove the remaining obligations. Rewrite using `[KL, Subgroup.coe_subgroupOf]`. Conclude with `hK.1.preimage continuous_subtype_val`.

Rewrite using `[KL, Subgroup.coe_subgroupOf]`. Conclude with `(isClosed_UL hU n w).isClosedEmbedding_subtypeVal.isCompact_preimage hK.2`.
-/
theorem twist_basic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E), Continuous (thL n w) ∧ (∀ g, thL n w (thL n w g) = g) ∧ (∀ k ∈ GlobalTheory.LFun.KGL w n, thL n w k ∈ GlobalTheory.LFun.KGL w n) ∧ (∀ g y, nrmL n w (g⁻¹ * y * thL n w g) = g⁻¹ * nrmL n w y * g) ∧ IsOpen (GlobalTheory.LFun.KGL w n : Set (GLw n w)) ∧ IsCompact (GlobalTheory.LFun.KGL w n : Set (GLw n w)) ∧ IsOpen (KL n w : Set (UL n w)) ∧ IsCompact (KL n w : Set (UL n w)) ∧ (∀ δ : GL (Fin n) E, (nrmL n w (locEl n w δ)).val.charpoly = atPl w (δ * thE E n δ).val.charpoly) ∧ ∀ x ∈ locU n w, cLoc w x ∈ UL n w := by
  intro E _ _ _ hU n w
  have hK := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n
  refine ⟨continuous_thL hU n w, thL_thL hU n w, thL_mem_KGL hU n w, nrmL_twist hU n w, hK.1, hK.2, ?_, ?_,
    charpoly_nrmL hU n w, fun x _ => cLoc_mem_UL hU n w x⟩
  · rw [KL, Subgroup.coe_subgroupOf]
    exact hK.1.preimage continuous_subtype_val
  · rw [KL, Subgroup.coe_subgroupOf]
    exact (isClosed_UL hU n w).isClosedEmbedding_subtypeVal.isCompact_preimage hK.2

end GlobalTheory.BCT.ThBasic
