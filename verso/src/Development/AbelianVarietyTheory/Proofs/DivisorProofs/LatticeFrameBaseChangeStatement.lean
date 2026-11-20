import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeFrameBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LieHt.isFrame_latBC` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLatticeFrameBaseChange.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.lattice_frame_base_change : ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K'] (m : ℕ) (L : Submodule (𝓞 K) (Fin m → K)) (r : ℕ) (v : Fin r → Fin m → K), IsFrame K L v → IsFrame K' (latBC K' L) (fun j i => algebraMap K K' (v j i)) := by
  first | exact @GlobalTheory.LieHt.isFrame_latBC | exact GlobalTheory.LieHt.isFrame_latBC | (intros; apply GlobalTheory.LieHt.isFrame_latBC <;> assumption)
