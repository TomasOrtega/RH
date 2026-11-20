import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopBlockEqOneIffMemColHK
import Mathlib
import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
import Formalism.LocalToGlobal.Divisibility.DefGroup
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FTopBlockEqOneIffMemColHK.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.upperLeftBlock_eq_one_iff_mem_HK : ∀ {κ : Type} [CommRing κ] {n r t : ℕ}, n = r + t → ∀ (hr : r ≤ n) (g : GL (Fin n) κ),
    g ∈ Formalism.L2.Col.blockUT n κ r [t] → (Formalism.L2.DIV.upperLeftBlock hr g = 1 ↔ g ∈ Formalism.L2.Col.HK n κ r [t]) := by
  first | exact @GlobalTheory.topBlock_eq_one_iff_mem_colHK | exact GlobalTheory.topBlock_eq_one_iff_mem_colHK | (intros; apply GlobalTheory.topBlock_eq_one_iff_mem_colHK <;> assumption)
