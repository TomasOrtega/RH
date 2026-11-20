import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

namespace GlobalTheory.SchurExt

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem blockGL_mem_supS : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S, GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h ∈ GlobalTheory.JSW.supS E (m + r + 1 + 1) S := by
  intro E _ _ m r S h hh w hw
  have hmap : Matrix.GeneralLinearGroup.map ((pLoc E w).comp (pFin E))
      (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) =
      GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1)
        (Matrix.GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) h) :=
    Units.ext (GroundTheory.Automorphic.FourierWhittaker.map_blockMat _ _ (h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)))
  rw [hmap, hh w hw, map_one]

end GlobalTheory.SchurExt
