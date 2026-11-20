import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsThreePrimesOneModLeRpow

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top

open NumberField IsDedekindDomain in

/- English proof (translation)
Introduce `D c hc hG w hw`. Unfold `_root_.Formalism.BasicNotions.NTw.NonzeroIndexPlace`. Use `⟨if c.sd w = true then w else D.what₂.places.conj w, ?_, ?_⟩` and prove the remaining obligations. Use `split_ifs`. Conclude with `hw`.

Rewrite using `[_root_.Formalism.BasicNotions.Rows.Data.muAt_conj]`. Conclude with `hw`. Establish `h` using `_root_.GlobalTheory.TwistGoodCompare.liesUnder_of_tie hG hc w`. Unfold `_root_.GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.LiesUnder at h`. Conclude with `h`.
-/
theorem _root_.GlobalTheory.Mem.Top.twistedPlaceIndex_mem_firstPair_of_compatibleChoice : ∀ (D : _root_.Formalism.BasicNotions.D7) (c : _root_.Formalism.BasicNotions.NChoice D),
    _root_.Formalism.BasicNotions.NChTie D c → IsGalois ℚ ↥D.LL0 →
    ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → D.ntw.NonzeroIndexPlace (c.twI w) := by
  intro D c hc hG w hw
  unfold _root_.Formalism.BasicNotions.NTw.NonzeroIndexPlace
  refine ⟨if c.sd w = true then w else D.what₂.places.conj w, ?_, ?_⟩
  · split_ifs
    · exact hw
    · rw [_root_.Formalism.BasicNotions.Rows.Data.muAt_conj]
      exact hw
  · have h := _root_.GlobalTheory.TwistGoodCompare.liesUnder_of_tie hG hc w
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.LiesUnder at h
    exact h

end GlobalTheory.Mem.Top
