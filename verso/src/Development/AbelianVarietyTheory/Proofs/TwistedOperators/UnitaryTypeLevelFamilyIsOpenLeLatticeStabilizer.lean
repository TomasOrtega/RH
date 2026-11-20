import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralMulRightOfCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelFamOfNotMem
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem

namespace GlobalTheory.TrIdem

/- English proof (translation)
Introduce `D V T U hu v`. Distinguish the cases in `hvu : v = U.u`. Substitute `hvu` using the available equality. Rewrite using `[levelFam_u]`. Conclude with `⟨U.frame.isOpen_iwahori, U.frame.iwahori_le⟩`.

Distinguish the cases in `hv : v ∈ T.S`. Establish `h` using `levelFam_of_mem T U hu ⟨v, hv⟩`. Simplify using `only at h`. Rewrite using `[h, kerSub]`. Use `⟨?_, Subgroup.map_subtype_le _⟩` and prove the remaining obligations.

Rewrite using `[Subgroup.coe_map]`. Conclude with `(isOpen_stabLoc _ _ _ v).isOpenMap_subtype_val _ (T.frame ⟨v, hv⟩).isOpen_ker_red`. Rewrite using `[levelFam_of_notMem T U hv hvu]`. Conclude with `⟨isOpen_stabLoc _ _ _ v, le_refl _⟩`.
-/
theorem levelFam_open_le : ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V), U.u ∉ T.S → ∀ v, IsOpen (levelFam T U v : Set (GLoc D.sp.cm.sig V.gram v)) ∧ levelFam T U v ≤ Kv V v := by
  intro D V T U hu v
  by_cases hvu : v = U.u
  · subst hvu
    rw [levelFam_u]
    exact ⟨U.frame.isOpen_iwahori, U.frame.iwahori_le⟩
  by_cases hv : v ∈ T.S
  · have h := levelFam_of_mem T U hu ⟨v, hv⟩
    simp only at h
    rw [h, kerSub]
    refine ⟨?_, Subgroup.map_subtype_le _⟩
    rw [Subgroup.coe_map]
    exact (isOpen_stabLoc _ _ _ v).isOpenMap_subtype_val _ (T.frame ⟨v, hv⟩).isOpen_ker_red
  · rw [levelFam_of_notMem T U hv hvu]
    exact ⟨isOpen_stabLoc _ _ _ v, le_refl _⟩

end GlobalTheory.TrIdem
