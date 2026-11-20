import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.BaseComap
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherFurther
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.OneBlockPnPt
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.ContractRelevant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem isMultiProjPrime_baseComap (F : Type) [Field F] {K : Type} [DecidableEq K] {ι : K → Type} (k₀ : K)
    {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) {W : Ideal (NumbersDVR.MRing ι F)} (hW : NumbersDVR.IsMultiProjPrime W) :
    NumbersDVR.IsMultiProjPrime (baseComap F k₀ e W) := by
  refine FieldNumbers.ContractRelevant.isMultiProjPrime_comap_rename (j := fun _ : Unit => k₀)
    (g := fun p : (Σ _ : Unit, Fin (N + 1)) => (⟨k₀, e.symm p.2⟩ : Σ k, ι k)) (fun _ => rfl)
    (fun _ _ _ => Subsingleton.elim _ _) ?_ ?_ hW
  · rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, b⟩ h
    simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and, EmbeddingLike.apply_eq_iff_eq] at h
    rw [h]
  · rintro ⟨k, i⟩ ⟨⟨⟩, hk⟩
    obtain rfl : k₀ = k := hk
    exact ⟨⟨(), e i⟩, by simp⟩

/- English proof (translation)
Substitute using the available equality. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem mIdealOver_le_baseComap (F : Type) [Field F] {K : Type} {ι : K → Type} {Ω : Type} [Field Ω]
    [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) {x : Fin (N + 1) → Ω}
    (hx : x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) {W : Ideal (NumbersDVR.MRing ι F)}
    (hW : mIdealOver F y ≤ W) : mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) ≤ baseComap F k₀ e W := by
  subst hx
  intro f hf
  rw [baseComap, Ideal.mem_comap]
  apply hW
  have hcomp : (mConeMapOver F y).comp
      (rename fun p : (Σ _ : Unit, Fin (N + 1)) => (⟨k₀, e.symm p.2⟩ : Σ k, ι k)) =
      ((rename (R := Ω) fun _ : Unit => k₀).restrictScalars F).comp
        (mConeMapOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm))) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMapOver, IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec]
  have hf' : mConeMapOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) f = 0 := hf
  have h1 := AlgHom.congr_fun hcomp f
  rw [AlgHom.comp_apply, AlgHom.comp_apply, hf', map_zero] at h1
  exact h1

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem ModelCurves.proof (hdim : ModelCurvesDim.Statement) (hlift : ModelCurvesLift.Statement) :
    ModelCurves.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hy d
  refine ⟨fun W hW hyW hd => ⟨isMultiProjPrime_baseComap F k₀ e hW,
    mIdealOver_le_baseComap F y k₀ e hx hyW, ?_⟩, fun P hP hxP hd => ?_⟩
  · rw [hdim F K ι Ω y k₀ N e hy W hW hyW, hd]
  · obtain ⟨W, hW, hyW, rfl⟩ := hlift F K ι Ω y k₀ N e x hx hy P hP hxP
    exact ⟨W, hW, hyW, by rw [← hdim F K ι Ω y k₀ N e hy W hW hyW, hd], rfl⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
