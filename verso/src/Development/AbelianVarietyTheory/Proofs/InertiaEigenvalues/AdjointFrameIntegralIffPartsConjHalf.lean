import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceModelCompTensorHalf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapMulInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairCharactersAtLevel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePlacesDisjointTwistPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatrixReductionEqOfHalfIdempotentSubset
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.ConjHalfSplitInt

/- English proof (translation)
Introduce `D S T βS βT Pg Q eg eQ hg hQ _ _ x hx`. Establish `hx' : cA D (eg + eQ) • x = x` using `(GlobalTheory.ExportSeries.RestrictHalfModel.isHalf_iff' _ _).1 hx`. Establish `hsplit : x = cA D eg • x + cA D eQ • x` using `by rw [← add_smul, ← map_add, hx']`. Establish `hA : ∀ e : AE D, frMapAdj S T βS βT (cA D e • x) = toEAf D e • frMapAdj S T βS βT x` using `fun e => by`. Rewrite using `[GlobalTheory.RedHalfDrop.frMapAdj_smul_eq, Formalism.L2.Theta.cA_cA]`.

Establish `hint : ∀ (e : AE D) (P : Finset (Pl D.host.E)), IsIdemSum e P → toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E` using `fun e P h => by`. Rewrite using `[← GlobalTheory.ExportSeries.idem_eq h]`. Unfold `GlobalTheory.ExportSeries.idem`. Rewrite using `[map_sum]`. Conclude with `sum_mem fun PP hPP => GlobalTheory.RedHalfDrop.int_idemAt ⟨e, h⟩ hPP`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[hA, hA]`. Conclude with `⟨fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem (hint _ _ hg) (h i j), fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem (hint _ _ hQ) (h i j)⟩`. Introduce and unpack `⟨h1, h2⟩`.

Rewrite using `[hsplit, GlobalTheory.PlaceVec.frMapAdj_add]`. Introduce `i j`. Rewrite using `[Matrix.add_apply]`. Conclude with `add_mem (h1 i j) (h2 i j)`.
-/
theorem frMapAdj_int_iff : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (Pg Q : Finset (Pl D.host.E)) (eg eQ : AE D), IsIdemSum eg Pg → IsIdemSum eQ Q → Disjoint Pg Q → IsIdemSum (eg + eQ) (Pg ∪ Q) → ∀ x : WO S T, IsHalf (cA D (eg + eQ)) x → (IsIntM (frMapAdj S T βS βT x) ↔ IsIntM (frMapAdj S T βS βT (cA D eg • x)) ∧ IsIntM (frMapAdj S T βS βT (cA D eQ • x))) := by
  intro D S T βS βT Pg Q eg eQ hg hQ _ _ x hx
  have hx' : cA D (eg + eQ) • x = x := (GlobalTheory.ExportSeries.RestrictHalfModel.isHalf_iff' _ _).1 hx
  have hsplit : x = cA D eg • x + cA D eQ • x := by rw [← add_smul, ← map_add, hx']
  have hA : ∀ e : AE D, frMapAdj S T βS βT (cA D e • x) = toEAf D e • frMapAdj S T βS βT x := fun e => by
    rw [GlobalTheory.RedHalfDrop.frMapAdj_smul_eq, Formalism.L2.Theta.cA_cA]
  have hint : ∀ (e : AE D) (P : Finset (Pl D.host.E)), IsIdemSum e P →
      toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun e P h => by
    rw [← GlobalTheory.ExportSeries.idem_eq h]
    unfold GlobalTheory.ExportSeries.idem
    rw [map_sum]
    exact sum_mem fun PP hPP => GlobalTheory.RedHalfDrop.int_idemAt ⟨e, h⟩ hPP
  constructor
  · intro h
    rw [hA, hA]
    exact ⟨fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem (hint _ _ hg) (h i j),
      fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem (hint _ _ hQ) (h i j)⟩
  · rintro ⟨h1, h2⟩
    rw [hsplit, GlobalTheory.PlaceVec.frMapAdj_add]
    intro i j
    rw [Matrix.add_apply]
    exact add_mem (h1 i j) (h2 i j)

end GlobalTheory.ConjHalfSplitInt
