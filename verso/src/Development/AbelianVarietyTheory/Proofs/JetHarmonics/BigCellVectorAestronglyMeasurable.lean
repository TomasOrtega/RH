import Mathlib
import Formalism.HermitianCurvature.StatementTBB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsContinuousFrameSectionStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselBigCellPointVectorEqBesselStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AestronglyMeasurableBesselFunctionContinuousFamiStatement

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P p H hH`. Take `⟨γ, hγc, hγ⟩` from `GlobalTheory.T.exists_continuous_frame_section' P.k P.r Wp Wq p.T.base p.ν' p.m₀ p.hF`. Use `set U : Set (Fin (P.r + 1) → ℂ) := {c | (∀ a, c a ≠ 0) ∧ Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (c (Fin.last P.r))} with hU`. Establish `hUo : IsOpen U`. Establish `h1 : IsOpen {c : Fin (P.r + 1) → ℂ | ∀ a, c a ≠ 0}`.

Rewrite using `[Set.ofPred_forall]`. Conclude with `isOpen_iInter_of_finite fun a => isOpen_ne_fun (continuous_apply a) continuous_const`. Establish `h2 : IsOpen {c : Fin (P.r + 1) → ℂ | Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (c (Fin.last P.r))}` using `isOpen_lt continuous_const (Complex.continuous_normSq.comp (continuous_apply _))`. Conclude with `h1.inter h2`. Establish `key : ∀ c ∈ U, γ c ∈ B.GPos p.T.base ∧ p.V H (TBB.bigPt P.r c) = B.JF p.T.base H (γ c)`.

Introduce `c hc`. Take `⟨g1, g2, g3⟩` from `hγ c hc.1 hc.2`. Conclude with `((GlobalTheory.T.besselBigCellPoint_vector_eq_bessel Wp Wq P p H c).2 hc).2 (γ c) g1 g2 g3`. Establish `hm : AEStronglyMeasurable (fun c => B.JF p.T.base H (γ c)) (volume.restrict U)`. Use `GlobalTheory.T.aestronglyMeasurable_besselFunction_continuousFamily P.k P.r Wp Wq p.T.base _ volume U γ (B.GPos p.T.base) H hUo hγc ?_ hH` and prove the remaining obligations.

Introduce `c hc q hq`. Establish `h` using `(key c hc).1`. Conclude with `⟨Formalism.FourierDecayAlt.P.B7.sgs_mem _ hq h.1, by`. Rewrite using `[Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs _ hq]`. Conclude with `h.2⟩`.

Establish `he : (fun c : Fin (P.r + 1) → ℂ => p.V H (TBB.bigPt P.r c)) = U.indicator (fun c => B.JF p.T.base H (γ c))`. Use function extensionality and compare the values at `c`. Distinguish the cases in `hc : c ∈ U`. Rewrite using `[Set.indicator_of_mem hc]`. Conclude with `(key c hc).2`.

Rewrite using `[Set.indicator_of_notMem hc]`. Conclude with `(GlobalTheory.T.besselBigCellPoint_vector_eq_bessel Wp Wq P p H c).1 hc`. Rewrite using `[he]`. Conclude with `(aestronglyMeasurable_indicator_iff hUo.measurableSet).2 hm`.
-/
theorem bigCell_vector_aestronglyMeasurable :
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), ContinuousOn H (B.GPos p.T.base) →
      AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ => p.V H (TBB.bigPt P.r c)) volume := by
  intro Wp Wq _ _ _ _ _ _ P p H hH
  classical
  obtain ⟨γ, hγc, hγ⟩ := GlobalTheory.T.exists_continuous_frame_section' P.k P.r Wp Wq p.T.base p.ν' p.m₀ p.hF
  set U : Set (Fin (P.r + 1) → ℂ) := {c | (∀ a, c a ≠ 0) ∧
    Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (c (Fin.last P.r))} with hU
  have hUo : IsOpen U := by
    have h1 : IsOpen {c : Fin (P.r + 1) → ℂ | ∀ a, c a ≠ 0} := by
      rw [Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun a => isOpen_ne_fun (continuous_apply a) continuous_const
    have h2 : IsOpen {c : Fin (P.r + 1) → ℂ |
        Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (c (Fin.last P.r))} :=
      isOpen_lt continuous_const (Complex.continuous_normSq.comp (continuous_apply _))
    exact h1.inter h2
  have key : ∀ c ∈ U, γ c ∈ B.GPos p.T.base ∧ p.V H (TBB.bigPt P.r c) = B.JF p.T.base H (γ c) := by
    intro c hc
    obtain ⟨g1, g2, g3⟩ := hγ c hc.1 hc.2
    exact ((GlobalTheory.T.besselBigCellPoint_vector_eq_bessel Wp Wq P p H c).2 hc).2 (γ c) g1 g2 g3
  have hm : AEStronglyMeasurable (fun c => B.JF p.T.base H (γ c)) (volume.restrict U) := by
    refine GlobalTheory.T.aestronglyMeasurable_besselFunction_continuousFamily P.k P.r Wp Wq p.T.base _ volume U γ (B.GPos p.T.base) H hUo hγc ?_ hH
    intro c hc q hq
    have h := (key c hc).1
    exact ⟨Formalism.FourierDecayAlt.P.B7.sgs_mem _ hq h.1, by
      rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs _ hq]; exact h.2⟩
  have he : (fun c : Fin (P.r + 1) → ℂ => p.V H (TBB.bigPt P.r c)) =
      U.indicator (fun c => B.JF p.T.base H (γ c)) := by
    funext c
    by_cases hc : c ∈ U
    · rw [Set.indicator_of_mem hc]; exact (key c hc).2
    · rw [Set.indicator_of_notMem hc]; exact (GlobalTheory.T.besselBigCellPoint_vector_eq_bessel Wp Wq P p H c).1 hc
  rw [he]
  exact (aestronglyMeasurable_indicator_iff hUo.measurableSet).2 hm

end GlobalTheory
