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
Use `FieldNumbers.ContractRelevant.isMultiProjPrime_comap_rename (j := fun _ : Unit => k₀) (g := fun p : (Σ _ : Unit, Fin (N + 1)) => (⟨k₀, e.symm p.2⟩ : Σ k, ι k)) (fun _ => rfl) (fun _ _ _ => Subsingleton.elim _ _) ?_ ?_ hW` and prove the remaining obligations. Introduce and unpack `⟨⟨⟩, a⟩ ⟨⟨⟩, b⟩ h`. Simplify using `only [Sigma.mk.inj_iff, heq_eq_eq, true_and, EmbeddingLike.apply_eq_iff_eq] at h`. Rewrite using `[h]`. Introduce and unpack `⟨k, i⟩ ⟨⟨⟩, hk⟩`.

Take `rfl : k₀ = k` from `hk`. Conclude with `⟨⟨(), e i⟩, by simp⟩`.
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
Substitute `hx` using the available equality. Introduce `f hf`. Rewrite using `[baseComap, Ideal.mem_comap]`. Apply `hW` to reduce the goal to its premises. Establish `hcomp : (mConeMapOver F y).comp (rename fun p : (Σ _ : Unit, Fin (N + 1)) => (⟨k₀, e.symm p.2⟩ : Σ k, ι k)) = ((rename (R` using `Ω) fun _ : Unit => k₀).restrictScalars F).comp (mConeMapOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm))) := by`.

Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `p`. Simplify using `[mConeMapOver, IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec]`. Establish `hf' : mConeMapOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) f = 0` using `hf`. Establish `h1` using `AlgHom.congr_fun hcomp f`.

Rewrite `h1` using `[AlgHom.comp_apply, AlgHom.comp_apply, hf', map_zero]`. Conclude with `h1`.
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
Introduce `F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hy d`. Use `⟨fun W hW hyW hd => ⟨isMultiProjPrime_baseComap F k₀ e hW, mIdealOver_le_baseComap F y k₀ e hx hyW, ?_⟩, fun P hP hxP hd => ?_⟩` and prove the remaining obligations. Rewrite using `[hdim F K ι Ω y k₀ N e hy W hW hyW, hd]`. Take `⟨W, hW, hyW, rfl⟩` from `hlift F K ι Ω y k₀ N e x hx hy P hP hxP`. Conclude with `⟨W, hW, hyW, by rw [← hdim F K ι Ω y k₀ N e hy W hW hyW, hd], rfl⟩`.
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
