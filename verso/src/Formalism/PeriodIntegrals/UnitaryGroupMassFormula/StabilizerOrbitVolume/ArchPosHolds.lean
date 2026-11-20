import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensPos
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LBSubm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensInfAll
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensInfSS

noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Filter Topology Set LocPosW
open scoped TensorProduct ENNReal

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet μinf νinf hμ hν W hWo hXW`. Establish `: FiniteDimensional F E` using `Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)`. Take `⟨n, m, eV, eH, f', hV, hH, hf', hG, hsurj⟩` from `hC F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet`. Take `⟨t1, t2, t3, t4, t5, t6, t7⟩` from `(tensAll_holds F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet).1`. Establish `: BorelSpace (Ainf F ⊗[F] E)` using `⟨rfl⟩`.

Establish `: BorelSpace (HermR (Ainf F) σ a)` using `⟨rfl⟩`. Establish `: ContinuousAdd (Fin a → Fin M → Ainf F ⊗[F] E)` using `⟨by`. Establish `e : (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) × (Fin a → Fin M → Ainf F ⊗[F] E) => p.1 + p.2) = fun p => eV.symm (eV p.1 + eV p.2)`. Use function extensionality and compare the values at `p`. Rewrite using `[← hV, Homeomorph.symm_apply_apply]`.

Rewrite using `[e]`. Use the proof step `fun_prop⟩`. Establish `: ContinuousAdd (HermR (Ainf F) σ a)` using `⟨by`. Establish `e : (fun p : HermR (Ainf F) σ a × HermR (Ainf F) σ a => p.1 + p.2) = fun p => eH.symm (eH p.1 + eH p.2)`. Use function extensionality and compare the values at `p`.

Rewrite using `[← hH, Homeomorph.symm_apply_apply]`. Rewrite using `[e]`. Use the proof step `fun_prop⟩`. Establish `hμ' : (μinf.map eV).IsAddHaarMeasure` using `Measure.isAddHaarMeasure_map μinf (AddMonoidHom.mk' eV hV) eV.continuous eV.surjective (eV.map_cocompact).le`. Establish `hν' : (νinf.map eH).IsAddHaarMeasure` using `Measure.isAddHaarMeasure_map νinf (AddMonoidHom.mk' eH hH) eH.continuous eH.surjective (eH.map_cocompact).le`.

Use `set X1 := ratTup (F := F) (Ainf F) X0 with hX1`. Use `set T := hermOf (Ainf F) σ (gramE σ J X0) hT with hTdef`. Establish `hX1U : LinearIndependent (Ainf F ⊗[F] E) X1` using `linIndep_of_isUnit_det (Ainf F) σ J X1 (by rw [gramR_ratTup]; exact isUnit_det_hermOf (Ainf F) σ _ hT hdet)`. Establish `hW' : IsOpen (eV.symm ⁻¹' W)` using `hWo.preimage eV.symm.continuous`. Establish `hx0W : eV X1 ∈ eV.symm ⁻¹' W` using `by show eV.symm (eV X1) ∈ W`.

Rewrite using `[Homeomorph.symm_apply_apply]`. Conclude with `hXW`. Take `⟨c, hc0, hct, N', hN', hlb'⟩` from `hS n m _ _ hμ' hν' f' hf' (eV X1) (hsurj X1 hX1U) _ hW' hx0W`. Establish `hfx0 : f' (eV X1) = eH T`. Establish `h1 : eH.symm (f' (eV X1)) = T` using `Subtype.ext ((hG X1).trans (gramR_ratTup (Ainf F) σ J X0))`.

Rewrite using `[← h1, Homeomorph.apply_symm_apply]`. Establish `hN : eH ⁻¹' N' ∈ 𝓝 T` using `eH.continuous.continuousAt.preimage_mem_nhds (hfx0 ▸ hN')`. Use `⟨c, hc0, hct, _, hN, fun S hSN hSm => ?_⟩` and prove the remaining obligations. Establish `hS'm : MeasurableSet (eH.symm ⁻¹' S)` using `eH.symm.continuous.measurable hSm`. Establish `hS'N : eH.symm ⁻¹' S ⊆ N'` using `fun z hz => by`.

Use `hSN hz` as an intermediate fact. Rewrite `this` using `[mem_preimage, Homeomorph.apply_symm_apply]`. Then use the resulting hypothesis. Establish `h` using `hlb' _ hS'N hS'm`. Rewrite `h` using `[show (νinf.map eH) = νinf.map eH.toMeasurableEquiv from rfl, show (μinf.map eV) = μinf.map eV.toMeasurableEquiv from rfl, MeasurableEquiv.map_apply, MeasurableEquiv.map_apply]`. Establish `e1 : eH.toMeasurableEquiv ⁻¹' (eH.symm ⁻¹' S) = S`.

Use extensionality with `z`. Simplify using the standard rewrite rules. Establish `e2 : eV.toMeasurableEquiv ⁻¹' (f' ⁻¹' (eH.symm ⁻¹' S) ∩ eV.symm ⁻¹' W) = (gramR (Ainf F) σ J) ⁻¹' (Subtype.val '' S) ∩ W`. Use extensionality with `X`. Simplify using `only [mem_preimage, mem_inter_iff, Homeomorph.toMeasurableEquiv_coe, Homeomorph.symm_apply_apply, mem_image]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨⟨_, h1, hG X⟩, h2⟩`. Introduce and unpack `⟨⟨s, hs, hsX⟩, h2⟩`. Use `⟨?_, h2⟩` and prove the remaining obligations.

Establish `: s = eH.symm (f' (eV X))` using `Subtype.ext (hsX.trans (hG X).symm)`. Rewrite using `[← this]`. Conclude with `hs`. Rewrite `h` using `[e1, e2]`. Conclude with `h`.
-/
theorem lbInf_of (hC : CoordInf) (hS : SubmLB) : LBInf := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet μinf νinf hμ hν W hWo hXW
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨n, m, eV, eH, f', hV, hH, hf', hG, hsurj⟩ :=
    hC F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ :=
    (tensAll_holds F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet).1
  have : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (HermR (Ainf F) σ a) := ⟨rfl⟩
  have : ContinuousAdd (Fin a → Fin M → Ainf F ⊗[F] E) := ⟨by
    have e : (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) × (Fin a → Fin M → Ainf F ⊗[F] E) =>
        p.1 + p.2) = fun p => eV.symm (eV p.1 + eV p.2) := by
      funext p; rw [← hV, Homeomorph.symm_apply_apply]
    rw [e]; fun_prop⟩
  have : ContinuousAdd (HermR (Ainf F) σ a) := ⟨by
    have e : (fun p : HermR (Ainf F) σ a × HermR (Ainf F) σ a => p.1 + p.2) =
        fun p => eH.symm (eH p.1 + eH p.2) := by
      funext p; rw [← hH, Homeomorph.symm_apply_apply]
    rw [e]; fun_prop⟩
  have hμ' : (μinf.map eV).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map μinf (AddMonoidHom.mk' eV hV) eV.continuous eV.surjective
      (eV.map_cocompact).le
  have hν' : (νinf.map eH).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map νinf (AddMonoidHom.mk' eH hH) eH.continuous eH.surjective
      (eH.map_cocompact).le
  set X1 := ratTup (F := F) (Ainf F) X0 with hX1
  set T := hermOf (Ainf F) σ (gramE σ J X0) hT with hTdef
  have hX1U : LinearIndependent (Ainf F ⊗[F] E) X1 :=
    linIndep_of_isUnit_det (Ainf F) σ J X1
      (by rw [gramR_ratTup]; exact isUnit_det_hermOf (Ainf F) σ _ hT hdet)
  have hW' : IsOpen (eV.symm ⁻¹' W) := hWo.preimage eV.symm.continuous
  have hx0W : eV X1 ∈ eV.symm ⁻¹' W := by
    show eV.symm (eV X1) ∈ W
    rw [Homeomorph.symm_apply_apply]
    exact hXW
  obtain ⟨c, hc0, hct, N', hN', hlb'⟩ :=
    hS n m _ _ hμ' hν' f' hf' (eV X1) (hsurj X1 hX1U) _ hW' hx0W
  have hfx0 : f' (eV X1) = eH T := by
    have h1 : eH.symm (f' (eV X1)) = T := Subtype.ext ((hG X1).trans (gramR_ratTup (Ainf F) σ J X0))
    rw [← h1, Homeomorph.apply_symm_apply]
  have hN : eH ⁻¹' N' ∈ 𝓝 T := eH.continuous.continuousAt.preimage_mem_nhds (hfx0 ▸ hN')
  refine ⟨c, hc0, hct, _, hN, fun S hSN hSm => ?_⟩
  have hS'm : MeasurableSet (eH.symm ⁻¹' S) := eH.symm.continuous.measurable hSm
  have hS'N : eH.symm ⁻¹' S ⊆ N' := fun z hz => by
    have := hSN hz
    rwa [mem_preimage, Homeomorph.apply_symm_apply] at this
  have h := hlb' _ hS'N hS'm
  rw [show (νinf.map eH) = νinf.map eH.toMeasurableEquiv from rfl,
    show (μinf.map eV) = μinf.map eV.toMeasurableEquiv from rfl,
    MeasurableEquiv.map_apply, MeasurableEquiv.map_apply] at h
  have e1 : eH.toMeasurableEquiv ⁻¹' (eH.symm ⁻¹' S) = S := by
    ext z
    simp
  have e2 : eV.toMeasurableEquiv ⁻¹' (f' ⁻¹' (eH.symm ⁻¹' S) ∩ eV.symm ⁻¹' W) =
      (gramR (Ainf F) σ J) ⁻¹' (Subtype.val '' S) ∩ W := by
    ext X
    simp only [mem_preimage, mem_inter_iff, Homeomorph.toMeasurableEquiv_coe,
      Homeomorph.symm_apply_apply, mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨_, h1, hG X⟩, h2⟩
    · rintro ⟨⟨s, hs, hsX⟩, h2⟩
      refine ⟨?_, h2⟩
      have : s = eH.symm (f' (eV X)) := Subtype.ext (hsX.trans (hG X).symm)
      rw [← this]
      exact hs
  rw [e1, e2] at h
  exact h

/- English proof (translation)
The claim follows from `lbInf_of (coordInf_of quadCoord_holds tensR_holds (freeSurj_of semisimpleTens_holds)) submLB_holds`.
-/
theorem lbInf_holds : LBInf :=
  lbInf_of (coordInf_of quadCoord_holds tensR_holds (freeSurj_of semisimpleTens_holds))
    submLB_holds

/- English proof (translation)
The claim follows from `archPos_of_lb lbInf_holds`.
-/
theorem archPos_holds : ArchPos := archPos_of_lb lbInf_holds

end PI.VolStabSW
