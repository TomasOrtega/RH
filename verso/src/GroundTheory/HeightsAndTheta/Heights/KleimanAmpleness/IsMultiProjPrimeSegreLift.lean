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
Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem map_id_ideal {σ : Type*} (I : Ideal (MvPolynomial σ F)) :
    I.map (MvPolynomial.map (RingHom.id F)) = I := by
  have h : (MvPolynomial.map (RingHom.id F) : MvPolynomial σ F →+* MvPolynomial σ F) = RingHom.id _ :=
    RingHom.ext MvPolynomial.map_id
  rw [h, Ideal.map_id]

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. By extensionality, compare the relevant components.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
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
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem genPt_block_ne_zero (W : Ideal (MRing ι F)) [W.IsPrime] (hW : IsMultiProjPrime W) :
    ∀ k, ∃ i, ModelGenericPoint.genPt W ⟨k, i⟩ ≠ 0 := fun k => by
  obtain ⟨i, hi⟩ := hW.relevant k
  exact ⟨i, (ModelGenericPoint.genPt_ne_zero W _).mpr hi⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem segreJoin_block_ne_zero {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) :
    ∀ k, ∃ i, segreJoin y ⟨k, i⟩ ≠ 0
  | Sum.inl () => ⟨fun k => (hy k).choose,
      show ∏ k, y ⟨k, (hy k).choose⟩ ≠ 0 from Finset.prod_ne_zero_iff.mpr fun k _ => (hy k).choose_spec⟩
  | Sum.inr k => hy k

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isMultiProjPrime_segreLift (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) :
    IsMultiProjPrime (segreLift ι F W) := by
  have := hW.isPrime
  rw [segreLift_eq_mIdealOver W hW]
  exact isMultiProjPrime_mIdealOver _ (segreJoin_block_ne_zero _ (genPt_block_ne_zero W hW))

end SegreNef

open SegreNef

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem SegreLiftRelDim.proof_of_segreDim (hD : SegreDim.Statement) : SegreLiftRelDim.Statement := by
  intro F _ K _ _ ι _ W hW
  have := hW.isPrime
  rw [segreLift_eq_mIdealOver W hW,
    hD F K ι _ (ModelGenericPoint.genPt W) (genPt_block_ne_zero W hW),
    ModelGenericPoint.mIdealOver_genPt W hW.multiHomog]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Both sides reduce to the same expression. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem SegreNef.proof_of_lift (hC : SegreLiftRelDim.Statement) (hN : SegreLiftIntNum.Statement) :
    SegreNef.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y _ β
  have h := segreFibresNef_of_map SegreLiftComap.proof (fun F _ K _ _ ι _ W hW => isMultiProjPrime_segreLift W hW)
    hC hN SegreFibreIdeal.proof F Ω F (RingHom.id F) K ι y β
  rw [map_id_ideal, map_id_ideal] at h
  exact h

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SegreNef.proof (hD : SegreDim.Statement) (hN : SegreNum.Statement) : SegreNef.Statement :=
  SegreNef.proof_of_lift (SegreLiftRelDim.proof_of_segreDim hD) (SegreLiftIntNum.proof_of_segreNum hN)

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
