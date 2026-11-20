import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailFurther
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideRest
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailExtra
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSegreFibresNef
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SegreInclWeightedHomogeneousComponent
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SegreLiftMapMap
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PModelGenericPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiProjPrime intNum)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

noncomputable section

namespace SegreNef

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Establish `h : (MvPolynomial.map (RingHom.id F) : MvPolynomial σ F →+* MvPolynomial σ F) = RingHom.id _` using `RingHom.ext MvPolynomial.map_id`. Rewrite using `[h, Ideal.map_id]`.
-/
theorem map_id_ideal {σ : Type*} (I : Ideal (MvPolynomial σ F)) :
    I.map (MvPolynomial.map (RingHom.id F)) = I := by
  have h : (MvPolynomial.map (RingHom.id F) : MvPolynomial σ F →+* MvPolynomial σ F) = RingHom.id _ :=
    RingHom.ext MvPolynomial.map_id
  rw [h, Ideal.map_id]

/- English proof (translation)
Establish `h : (segreLiftMap ι F W).comp (segreIncl ι F) = (Polynomial.CAlgHom : (MRing ι F ⧸ W) →ₐ[F] Polynomial (MRing ι F ⧸ W)).comp (Ideal.Quotient.mkₐ F W)`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `p`. Simplify using `[segreIncl, segreLiftMap, segreLiftVal]`. Use extensionality with `g`.

Rewrite using `[Ideal.mem_comap, segreLift, RingHom.mem_ker]`. Establish `hg` using `congrArg (fun φ => φ g) h`. Simplify using `only [AlgHom.comp_apply] at hg`. Rewrite using `[hg, Polynomial.CAlgHom_apply, Polynomial.C_eq_zero, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]`.
-/
theorem comap_segreLift (W : Ideal (MRing ι F)) : (segreLift ι F W).comap (segreIncl ι F) = W := by
  have h : (segreLiftMap ι F W).comp (segreIncl ι F) =
      (Polynomial.CAlgHom : (MRing ι F ⧸ W) →ₐ[F] Polynomial (MRing ι F ⧸ W)).comp
        (Ideal.Quotient.mkₐ F W) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [segreIncl, segreLiftMap, segreLiftVal]
  ext g
  rw [Ideal.mem_comap, segreLift, RingHom.mem_ker]
  have hg := congrArg (fun φ => φ g) h
  simp only [AlgHom.comp_apply] at hg
  rw [hg, Polynomial.CAlgHom_apply, Polynomial.C_eq_zero, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem]

/- English proof (translation)
Introduce `k` and use `by obtain ⟨i, hi⟩ := hW.relevant k exact ⟨i, (ModelGenericPoint.genPt_ne_zero W _).mpr hi⟩`.
-/
theorem genPt_block_ne_zero (W : Ideal (MRing ι F)) [W.IsPrime] (hW : IsMultiProjPrime W) :
    ∀ k, ∃ i, ModelGenericPoint.genPt W ⟨k, i⟩ ≠ 0 := fun k => by
  obtain ⟨i, hi⟩ := hW.relevant k
  exact ⟨i, (ModelGenericPoint.genPt_ne_zero W _).mpr hi⟩

/- English proof (translation)
The claim follows from `| Sum.inl () => ⟨fun k => (hy k).choose, show ∏ k, y ⟨k, (hy k).choose⟩ ≠ 0 from Finset.prod_ne_zero_iff.mpr fun k _ => (hy k).choose_spec⟩ | Sum.inr k => hy k`.
-/
theorem segreJoin_block_ne_zero {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) :
    ∀ k, ∃ i, segreJoin y ⟨k, i⟩ ≠ 0
  | Sum.inl () => ⟨fun k => (hy k).choose,
      show ∏ k, y ⟨k, (hy k).choose⟩ ≠ 0 from Finset.prod_ne_zero_iff.mpr fun k _ => (hy k).choose_spec⟩
  | Sum.inr k => hy k

/- English proof (translation)
Establish `hy : mIdealOver F (ModelGenericPoint.genPt W) = W` using `ModelGenericPoint.mIdealOver_genPt W hW.multiHomog`. Establish `hP' : IsMultiProjPrime (mIdealOver F (segreJoin (ModelGenericPoint.genPt W)))` using `isMultiProjPrime_mIdealOver _ (segreJoin_block_ne_zero _ (genPt_block_ne_zero W hW))`. Take `⟨hrel, hle, hlift⟩` from `SegreFibreIdeal.proof F _ F (RingHom.id F) K ι (ModelGenericPoint.genPt W)`. Simplify using `only [map_id_ideal] at hrel hle hlift`. Establish `hc : (mIdealOver F (segreJoin (ModelGenericPoint.genPt W))).comap (segreIncl ι F) = W`.

Use `le_antisymm ?_ (hy.ge.trans hle)` and prove the remaining obligations. Establish `h` using `hlift W hy.le`. Conclude with `(Ideal.comap_mono h).trans (comap_segreLift W).le`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hc]`.

Use `_ = _ := ((SegreLiftComap.proof F K ι _ hP' hrel).2).symm`.
-/
theorem segreLift_eq_mIdealOver (W : Ideal (MRing ι F)) [W.IsPrime] (hW : IsMultiProjPrime W) :
    segreLift ι F W = mIdealOver F (segreJoin (ModelGenericPoint.genPt W)) := by
  have hy : mIdealOver F (ModelGenericPoint.genPt W) = W :=
    ModelGenericPoint.mIdealOver_genPt W hW.multiHomog
  have hP' : IsMultiProjPrime (mIdealOver F (segreJoin (ModelGenericPoint.genPt W))) :=
    isMultiProjPrime_mIdealOver _ (segreJoin_block_ne_zero _ (genPt_block_ne_zero W hW))
  obtain ⟨hrel, hle, hlift⟩ := SegreFibreIdeal.proof F _ F (RingHom.id F) K ι (ModelGenericPoint.genPt W)
  simp only [map_id_ideal] at hrel hle hlift
  have hc : (mIdealOver F (segreJoin (ModelGenericPoint.genPt W))).comap (segreIncl ι F) = W := by
    refine le_antisymm ?_ (hy.ge.trans hle)
    have h := hlift W hy.le
    exact (Ideal.comap_mono h).trans (comap_segreLift W).le
  calc segreLift ι F W
      = segreLift ι F ((mIdealOver F (segreJoin (ModelGenericPoint.genPt W))).comap (segreIncl ι F)) := by
        rw [hc]
    _ = _ := ((SegreLiftComap.proof F K ι _ hP' hrel).2).symm

/- English proof (translation)
Use `hW.isPrime` as an intermediate fact. Rewrite using `[segreLift_eq_mIdealOver W hW]`. Conclude with `isMultiProjPrime_mIdealOver _ (segreJoin_block_ne_zero _ (genPt_block_ne_zero W hW))`.
-/
theorem isMultiProjPrime_segreLift (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) :
    IsMultiProjPrime (segreLift ι F W) := by
  have := hW.isPrime
  rw [segreLift_eq_mIdealOver W hW]
  exact isMultiProjPrime_mIdealOver _ (segreJoin_block_ne_zero _ (genPt_block_ne_zero W hW))

end SegreNef

open SegreNef

/- English proof (translation)
Introduce `F _ K _ _ ι _ W hW`. Use `hW.isPrime` as an intermediate fact. Rewrite using `[segreLift_eq_mIdealOver W hW, hD F K ι _ (ModelGenericPoint.genPt W) (genPt_block_ne_zero W hW), ModelGenericPoint.mIdealOver_genPt W hW.multiHomog]`.
-/
theorem SegreLiftRelDim.proof_of_segreDim (hD : SegreDim.Statement) : SegreLiftRelDim.Statement := by
  intro F _ K _ _ ι _ W hW
  have := hW.isPrime
  rw [segreLift_eq_mIdealOver W hW,
    hD F K ι _ (ModelGenericPoint.genPt W) (genPt_block_ne_zero W hW),
    ModelGenericPoint.mIdealOver_genPt W hW.multiHomog]

/- English proof (translation)
Introduce `F _ K _ _ ι _ W hW β`. Use `hW.isPrime` as an intermediate fact. Establish `h` using `hN F K ι _ (ModelGenericPoint.genPt W) (genPt_block_ne_zero W hW) 1 ![β]`. Establish `hfun : (fun j : Fin 1 => IndefiniteRowSideFullHecke.Kleiman2.pullDeg (K₁` using `Unit) (![β] j)) = ![IndefiniteRowSideFullHecke.Kleiman2.pullDeg β] := by`. Use function extensionality and compare the values at `j`.

Use `fin_cases j`. Both sides reduce to the same expression. Rewrite `h` using `[hfun, ModelGenericPoint.mIdealOver_genPt W hW.multiHomog]`. Rewrite using `[segreLift_eq_mIdealOver W hW]`. Conclude with `h`.
-/
theorem SegreLiftIntNum.proof_of_segreNum (hN : SegreNum.Statement) : SegreLiftIntNum.Statement := by
  intro F _ K _ _ ι _ W hW β
  have := hW.isPrime
  have h := hN F K ι _ (ModelGenericPoint.genPt W) (genPt_block_ne_zero W hW) 1 ![β]
  have hfun : (fun j : Fin 1 => IndefiniteRowSideFullHecke.Kleiman2.pullDeg (K₁ := Unit) (![β] j)) = ![IndefiniteRowSideFullHecke.Kleiman2.pullDeg β] := by
    funext j
    fin_cases j
    rfl
  rw [hfun, ModelGenericPoint.mIdealOver_genPt W hW.multiHomog] at h
  rw [segreLift_eq_mIdealOver W hW]
  exact h

/- English proof (translation)
Introduce `F _ K _ _ ι _ Ω _ _ y _ β`. Establish `h` using `segreFibresNef_of_map SegreLiftComap.proof (fun F _ K _ _ ι _ W hW => isMultiProjPrime_segreLift W hW) hC hN SegreFibreIdeal.proof F Ω F (RingHom.id F) K ι y β`. Rewrite `h` using `[map_id_ideal, map_id_ideal]`. Conclude with `h`.
-/
theorem SegreNef.proof_of_lift (hC : SegreLiftRelDim.Statement) (hN : SegreLiftIntNum.Statement) :
    SegreNef.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y _ β
  have h := segreFibresNef_of_map SegreLiftComap.proof (fun F _ K _ _ ι _ W hW => isMultiProjPrime_segreLift W hW)
    hC hN SegreFibreIdeal.proof F Ω F (RingHom.id F) K ι y β
  rw [map_id_ideal, map_id_ideal] at h
  exact h

/- English proof (translation)
The claim follows from `SegreNef.proof_of_lift (SegreLiftRelDim.proof_of_segreDim hD) (SegreLiftIntNum.proof_of_segreNum hN)`.
-/
theorem SegreNef.proof (hD : SegreDim.Statement) (hN : SegreNum.Statement) : SegreNef.Statement :=
  SegreNef.proof_of_lift (SegreLiftRelDim.proof_of_segreDim hD) (SegreLiftIntNum.proof_of_segreNum hN)

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
