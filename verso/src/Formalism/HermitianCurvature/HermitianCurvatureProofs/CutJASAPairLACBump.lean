import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLACCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellOpenDomain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveOrbitOpen
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian

open MeasureTheory Topology
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `k r Wp Wq _ _ _ _ D K hK hKQ`. Establish `: LocallyCompactSpace (B.Mat k r)` using `(inferInstance : LocallyCompactSpace (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ))`. Establish `hcont : ContinuousOn (fun q => B.gq D q) (JF.QDom k r D.z D.z')` using `(Formalism.FourierDecayAlt.P.BigCellOpenDomain.gq_contDiffOn D 0).continuousOn`. Establish `hgK : IsCompact ((fun q => B.gq D q) '' K)` using `hK.image_of_continuousOn (hcont.mono hKQ)`. Establish `hsub : (fun q => B.gq D q) '' K ⊆ Q.OmPlus k r D.z D.z'`.

Introduce and unpack `_ ⟨q, hq, rfl⟩`. Conclude with `(Formalism.FourierDecayAlt.P.big_cell_domain k r Wp Wq D q (hKQ hq)).2`. Take `⟨L, hLc, hKL, hLO⟩` from `exists_compact_between hgK (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open D.z D.z') hsub`. Take `⟨φ₀, hsupp, hsmooth, hrange⟩` from `(isOpen_interior : IsOpen (interior L)).exists_contDiff_support_eq (n := ⊤)`. Establish `hts : tsupport φ₀ ⊆ L`.

Unfold `tsupport`. Rewrite using `[hsupp]`. Conclude with `closure_minimal interior_subset hLc.isClosed`. Use `⟨φ₀, hsmooth, fun g => (hrange ⟨g, rfl⟩).1, hLc.of_isClosed_subset (isClosed_tsupport _) hts, hts.trans hLO, fun q hq => ?_⟩` and prove the remaining obligations. Establish `hin : B.gq D q ∈ Function.support φ₀`.

Rewrite using `[hsupp]`. Conclude with `hKL ⟨q, hq, rfl⟩`. Conclude with `lt_of_le_of_ne (hrange ⟨_, rfl⟩).1 (Ne.symm hin)`.
-/
theorem averaging_bump_holds : ACBump := by
  intro k r Wp Wq _ _ _ _ D K hK hKQ
  have : LocallyCompactSpace (B.Mat k r) :=
    (inferInstance : LocallyCompactSpace (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ))
  have hcont : ContinuousOn (fun q => B.gq D q) (JF.QDom k r D.z D.z') :=
    (Formalism.FourierDecayAlt.P.BigCellOpenDomain.gq_contDiffOn D 0).continuousOn
  have hgK : IsCompact ((fun q => B.gq D q) '' K) := hK.image_of_continuousOn (hcont.mono hKQ)
  have hsub : (fun q => B.gq D q) '' K ⊆ Q.OmPlus k r D.z D.z' := by
    rintro _ ⟨q, hq, rfl⟩
    exact (Formalism.FourierDecayAlt.P.big_cell_domain k r Wp Wq D q (hKQ hq)).2
  obtain ⟨L, hLc, hKL, hLO⟩ := exists_compact_between hgK (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open D.z D.z') hsub
  obtain ⟨φ₀, hsupp, hsmooth, hrange⟩ :=
    (isOpen_interior : IsOpen (interior L)).exists_contDiff_support_eq (n := ⊤)
  have hts : tsupport φ₀ ⊆ L := by
    unfold tsupport
    rw [hsupp]
    exact closure_minimal interior_subset hLc.isClosed
  refine ⟨φ₀, hsmooth, fun g => (hrange ⟨g, rfl⟩).1, hLc.of_isClosed_subset (isClosed_tsupport _) hts,
    hts.trans hLO, fun q hq => ?_⟩
  have hin : B.gq D q ∈ Function.support φ₀ := by
    rw [hsupp]; exact hKL ⟨q, hq, rfl⟩
  exact lt_of_le_of_ne (hrange ⟨_, rfl⟩).1 (Ne.symm hin)

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
