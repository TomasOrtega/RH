import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ThresholdProductsBounded
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsPlaceWithVectors
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InvariantOperatorUnderJacquet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QNFAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ModuleFormEqRadialFormOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.KB GlobalTheory.ThA Finset NumberField MeasureTheory Formalism.QuantumDeterminants Matrix

namespace GlobalTheory.ThA

/- English proof (translation)
Take `⟨Cb, -, hTL⟩` from `Formalism.FourierDecayAlt.P.top_lift_exists`. Use `⟨Cb, ?_⟩` and prove the remaining obligations. Introduce `Wp Wq _ _ _ _ _ _ P Bs ν' m₀ l0 hl1 hl2 hk hW hW' hN hF hP`. Take `⟨T, hz, hz', hπ, hπ', hTn⟩` from `Formalism.FourierDecayAlt.P.exists_normalized_tower P.k P.r Wp Wq Bs`. Establish `ez : (T.bs 0).z = Bs.z` using `hz`.

Establish `ez' : (T.bs 0).z' = Bs.z'` using `hz'`. Establish `eπ : (T.bs 0).π = Bs.π` using `hπ`. Establish `eπ' : (T.bs 0).π' = Bs.π'` using `hπ'`. Set `T' : D.LevTower P.k P.r Wp Wq` to `{ bs := fun j => Nat.rec (motive := fun j => B.RealPlaceData P.k (P.r - j) Wp Wq) Bs (fun n _ => T.bs (n + 1)) j z_lev := by`. Introduce `j hj`.

Consider the cases of `j with`. Consider the case `zero`. Establish `h0` using `T.z_lev 0 hj`. Rewrite `h0` using `[ez]`. Conclude with `h0`.

Consider the case `succ n => exact (T.z_lev (n + 1) hj).trans ez`. Use the proof step `z'_lev := by`. Introduce `j hj`. Consider the cases of `j with`. Consider the case `zero`.

Establish `h0` using `T.z'_lev 0 hj`. Rewrite `h0` using `[ez']`. Conclude with `h0`. Consider the case `succ n => exact (T.z'_lev (n + 1) hj).trans ez'`. Use `π_lev := by`.

Introduce `j hj y`. Consider the cases of `j with`. Consider the case `zero`. Establish `h0` using `T.π_lev 0 hj y`. Rewrite `h0` using `[eπ]`.

Conclude with `h0`. Consider the case `succ n => exact (T.π_lev (n + 1) hj y).trans (congrFun eπ _)`. Use the proof step `π'_lev := by`. Introduce `j hj y`. Consider the cases of `j with`.

Consider the case `zero`. Establish `h0` using `T.π'_lev 0 hj y`. Rewrite `h0` using `[eπ']`. Conclude with `h0`. Consider the case `succ n => exact (T.π'_lev (n + 1) hj y).trans (congrFun eπ' _) }`.

Establish `hT'n : D.TowerNormalised T'`. Introduce `j hj`. Consider the cases of `j with`. Consider the case `zero => exact ⟨hW, hW', hN⟩`. Consider the case `succ n => exact hTn (n + 1) hj`.

Take `⟨X⟩` from `Formalism.FourierDecayAlt.P.actual_operators_exist Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hP`. Take `⟨L, st, hXL, hQQ, hq, hinv, hstar, hstart⟩` from `Formalism.FourierDecayAlt.P.level_start_actual Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hP X l0`. Take `⟨μ, hμ⟩` from `Formalism.FourierDecayAlt.P.exists_zeta_normalized_haar P.k P.r Wp Wq Bs`. Establish `hD : P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0` using `⟨hP, hμ.1, hXL, hQQ, hq, hinv, hstar, hstart⟩`. Take `⟨Θ, hΘ1, hΘ2⟩` from `hTL Wp Wq P Bs X μ L st l0 hl1 hl2 hD`.

Take `⟨he1, he2, he3⟩` from `Formalism.FourierDecayAlt.P.HaarMassHermitianCurvature.frameVec_facts Bs ν' m₀ hF`. Take `⟨TP⟩` from `Formalism.FourierDecayAlt.P.type_projectors_exist Wp Wq P Bs.z Bs.z' Bs.π Bs.π' (m₀ *ᵥ ν') hP he1 he2 he3`. Conclude with `⟨⟨l0, T', ν', m₀, Θ, TP, ⟨hl1, hl2, hk⟩, hT'n, hF, hP, ⟨X, μ, L, st, hD, hΘ1⟩⟩, rfl, rfl, rfl, rfl, hΘ2⟩`.
-/
theorem plExists : PlExists := by
  obtain ⟨Cb, -, hTL⟩ := Formalism.FourierDecayAlt.P.top_lift_exists
  refine ⟨Cb, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P Bs ν' m₀ l0 hl1 hl2 hk hW hW' hN hF hP

  obtain ⟨T, hz, hz', hπ, hπ', hTn⟩ := Formalism.FourierDecayAlt.P.exists_normalized_tower P.k P.r Wp Wq Bs
  have ez : (T.bs 0).z = Bs.z := hz
  have ez' : (T.bs 0).z' = Bs.z' := hz'
  have eπ : (T.bs 0).π = Bs.π := hπ
  have eπ' : (T.bs 0).π' = Bs.π' := hπ'

  let T' : D.LevTower P.k P.r Wp Wq :=
    { bs := fun j => Nat.rec (motive := fun j => B.RealPlaceData P.k (P.r - j) Wp Wq) Bs (fun n _ => T.bs (n + 1)) j
      z_lev := by
        intro j hj
        cases j with
        | zero =>
          have h0 := T.z_lev 0 hj
          rw [ez] at h0
          exact h0
        | succ n => exact (T.z_lev (n + 1) hj).trans ez
      z'_lev := by
        intro j hj
        cases j with
        | zero =>
          have h0 := T.z'_lev 0 hj
          rw [ez'] at h0
          exact h0
        | succ n => exact (T.z'_lev (n + 1) hj).trans ez'
      π_lev := by
        intro j hj y
        cases j with
        | zero =>
          have h0 := T.π_lev 0 hj y
          rw [eπ] at h0
          exact h0
        | succ n => exact (T.π_lev (n + 1) hj y).trans (congrFun eπ _)
      π'_lev := by
        intro j hj y
        cases j with
        | zero =>
          have h0 := T.π'_lev 0 hj y
          rw [eπ'] at h0
          exact h0
        | succ n => exact (T.π'_lev (n + 1) hj y).trans (congrFun eπ' _) }
  have hT'n : D.TowerNormalised T' := by
    intro j hj
    cases j with
    | zero => exact ⟨hW, hW', hN⟩
    | succ n => exact hTn (n + 1) hj

  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hP
  obtain ⟨L, st, hXL, hQQ, hq, hinv, hstar, hstart⟩ :=
    Formalism.FourierDecayAlt.P.level_start_actual Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hP X l0
  obtain ⟨μ, hμ⟩ := Formalism.FourierDecayAlt.P.exists_zeta_normalized_haar P.k P.r Wp Wq Bs
  have hD : P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 :=
    ⟨hP, hμ.1, hXL, hQQ, hq, hinv, hstar, hstart⟩
  obtain ⟨Θ, hΘ1, hΘ2⟩ := hTL Wp Wq P Bs X μ L st l0 hl1 hl2 hD

  obtain ⟨he1, he2, he3⟩ := Formalism.FourierDecayAlt.P.HaarMassHermitianCurvature.frameVec_facts Bs ν' m₀ hF
  obtain ⟨TP⟩ := Formalism.FourierDecayAlt.P.type_projectors_exist Wp Wq P Bs.z Bs.z' Bs.π Bs.π' (m₀ *ᵥ ν') hP he1 he2 he3
  exact ⟨⟨l0, T', ν', m₀, Θ, TP, ⟨hl1, hl2, hk⟩, hT'n, hF, hP, ⟨X, μ, L, st, hD, hΘ1⟩⟩, rfl, rfl, rfl, rfl, hΘ2⟩

end GlobalTheory.ThA
