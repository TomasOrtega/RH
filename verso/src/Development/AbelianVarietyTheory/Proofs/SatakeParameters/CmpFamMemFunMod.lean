import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnimodularLatticeLocalMatch
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGlobalLatticeLocalGiven
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeHasBasisAtEveryFinitePlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PosOkId
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnimodularLatticeLocalConjSymm

namespace GlobalTheory.GO

open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV

namespace CmpMem

/- English proof (translation)
Take `⟨g, hg, rfl⟩` from `hL`. Use `⟨(A : Matrix (Fin k) (Fin k) K) * g, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_mul]`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).1 A.isUnit).mul hg`. Unfold `colSpan`.

Rewrite using `[Submodule.map_span, ← Set.range_comp]`. Use `congr 1`.
-/
theorem isLattice_map {R K : Type} [CommRing R] [Field K] [Algebra R K] {k : ℕ} (A : GL (Fin k) K)
    {L : Submodule R (Fin k → K)} (hL : IsLattice R L) :
    IsLattice R (L.map ((Matrix.mulVecLin (A : Matrix (Fin k) (Fin k) K)).restrictScalars R)) := by
  obtain ⟨g, hg, rfl⟩ := hL
  refine ⟨(A : Matrix (Fin k) (Fin k) K) * g, ?_, ?_⟩
  · rw [Matrix.det_mul]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 A.isUnit).mul hg
  · unfold colSpan
    rw [Submodule.map_span, ← Set.range_comp]
    congr 1

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {P : Places p O Kf}

/- English proof (translation)
Introduce `v` and use `isLattice_map (C.act v γ) (hL v)`.
-/
theorem isLatTup_smul (C : Level P) (γ : C.Γ) {L : P.Tup} (hL : P.IsLatTup L) : P.IsLatTup (C.smul γ L) :=
  fun v => isLattice_map (C.act v γ) (hL v)

variable {X : Fields} (T : PlTie X P) {n : ℕ} (hn : n = P.m + 1) {lam : X.Tau → DomWeight n} {c : ℤ}

variable {S : GSD X.K} (Y : PSys X n p lam S)

end CmpMem

end GlobalTheory.GO
