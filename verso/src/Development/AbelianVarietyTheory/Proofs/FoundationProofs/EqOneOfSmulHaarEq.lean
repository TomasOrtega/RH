import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InstSecondCountable
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BlockOrdFinSumFinEquiv
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.HolDS Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace GlobalTheory.HolDS

/- English proof (translation)
Take `⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts H)` from `inferInstance`. Establish `h0 : ν K ≠ 0` using `(Measure.measure_pos_of_nonempty_interior ν K.interior_nonempty).ne'`. Establish `h1 : ν K ≠ ⊤` using `K.isCompact.measure_lt_top.ne`. Establish `h2 : (c : ENNReal) * ν K = 1 * ν K` using `by conv_rhs => rw [← h]`. Rewrite using `[one_mul, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]`.

Rewrite `h2` using `[ENNReal.mul_left_inj h0 h1]`. Conclude with `h2` after adjusting the coercions.
-/
theorem eq_one_of_smul_haar_eq {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
    [BorelSpace H] [LocallyCompactSpace H] (ν : Measure H) [ν.IsHaarMeasure] {c : NNReal} (h : c • ν = ν) :
    c = 1 := by
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts H) := inferInstance
  have h0 : ν K ≠ 0 := (Measure.measure_pos_of_nonempty_interior ν K.interior_nonempty).ne'
  have h1 : ν K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have h2 : (c : ENNReal) * ν K = 1 * ν K := by
    conv_rhs => rw [← h]
    rw [one_mul, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rw [ENNReal.mul_left_inj h0 h1] at h2
  exact_mod_cast h2

/- English proof (translation)
Introduce `p q T`. Establish `h` using `blockOrd_finSumFinEquiv p q`. Use `haveI := GlobalTheory.RealPar.SqInt.isHaarMeasure_map_covU h T`. Use `set ε : Fin (p + q) → Bool := fun i => (finSumFinEquiv.symm i).isLeft`. Use `set f := GlobalTheory.RealPar.SqInt.covU h T`.

Establish `hf : Measurable f` using `(GlobalTheory.RealPar.SqInt.continuous_covU h T).measurable`. Take `⟨c, hc⟩ : ∃ c : NNReal, T.haar.map f = c • Formalism.REAL.muG ε` from `⟨_, Measure.isMulLeftInvariant_eq_smul _ _⟩`. Establish `hR : T.haar.IsMulRightInvariant`. Use `⟨fun g => ?_⟩` and prove the remaining obligations. Establish `hg` using `Measure.map_right_mul_eq_modularCharacterFun_smul T.haar g`.

Establish `h1 : (T.haar.map (· * g)).map f = T.haar.map f`. Establish `h2 : (T.haar.map (· * g)).map f = (T.haar.map f).map (· * f g)`. Rewrite using `[Measure.map_map hf (measurable_mul_const g), Measure.map_map (measurable_mul_const _) hf]`. Use `congr 1`. Use function extensionality and compare the values at `x`.

Simplify using the standard rewrite rules. Rewrite using `[h2, hc, Measure.map_smul, Formalism.REAL.indefinite_unitary_unimodular _ ε (f g)]`. Rewrite `h1` using `[hg, Measure.map_smul]`. Rewrite using `[hg, eq_one_of_smul_haar_eq _ h1, one_smul]`. Use `⟨hR, ⟨?_⟩⟩` and prove the remaining obligations.

Use `haveI : T.haar.inv.IsHaarMeasure := { toIsFiniteMeasureOnCompacts := inferInstance toIsMulLeftInvariant := inferInstance toIsOpenPosMeasure := inferInstance }`. Take `⟨d, hd⟩ : ∃ d : NNReal, T.haar.inv = d • T.haar` from `⟨_, Measure.isMulLeftInvariant_eq_smul _ _⟩`. Establish `h1 : T.haar.inv.map f = T.haar.map f`. Establish `h2 : T.haar.inv.map f = (T.haar.map f).map (fun x => x⁻¹)`. Rewrite using `[Measure.inv_def, Measure.map_map hf measurable_inv, Measure.map_map measurable_inv hf]`.

Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules. Rewrite using `[h2, hc, Measure.map_smul, Formalism.REAL.invInvariant_of Formalism.REAL.indefinite_unitary_unimodular _ ε]`. Rewrite `h1` using `[hd, Measure.map_smul]`.

Rewrite using `[hd, eq_one_of_smul_haar_eq _ h1, one_smul]`.
-/
theorem haar_unimodular : ∀ (p q : ℕ) (T : GrpData p q), T.haar.IsMulRightInvariant ∧ T.haar.IsInvInvariant := by
  intro p q T
  have h := blockOrd_finSumFinEquiv p q
  haveI := GlobalTheory.RealPar.SqInt.isHaarMeasure_map_covU h T
  set ε : Fin (p + q) → Bool := fun i => (finSumFinEquiv.symm i).isLeft
  set f := GlobalTheory.RealPar.SqInt.covU h T
  have hf : Measurable f := (GlobalTheory.RealPar.SqInt.continuous_covU h T).measurable
  obtain ⟨c, hc⟩ : ∃ c : NNReal, T.haar.map f = c • Formalism.REAL.muG ε :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul _ _⟩
  have hR : T.haar.IsMulRightInvariant := by
    refine ⟨fun g => ?_⟩
    have hg := Measure.map_right_mul_eq_modularCharacterFun_smul T.haar g
    have h1 : (T.haar.map (· * g)).map f = T.haar.map f := by
      have h2 : (T.haar.map (· * g)).map f = (T.haar.map f).map (· * f g) := by
        rw [Measure.map_map hf (measurable_mul_const g), Measure.map_map (measurable_mul_const _) hf]
        congr 1
        funext x
        simp
      rw [h2, hc, Measure.map_smul, Formalism.REAL.indefinite_unitary_unimodular _ ε (f g)]
    rw [hg, Measure.map_smul] at h1
    rw [hg, eq_one_of_smul_haar_eq _ h1, one_smul]
  refine ⟨hR, ⟨?_⟩⟩
  haveI : T.haar.inv.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsMulLeftInvariant := inferInstance
      toIsOpenPosMeasure := inferInstance }
  obtain ⟨d, hd⟩ : ∃ d : NNReal, T.haar.inv = d • T.haar := ⟨_, Measure.isMulLeftInvariant_eq_smul _ _⟩
  have h1 : T.haar.inv.map f = T.haar.map f := by
    have h2 : T.haar.inv.map f = (T.haar.map f).map (fun x => x⁻¹) := by
      rw [Measure.inv_def, Measure.map_map hf measurable_inv, Measure.map_map measurable_inv hf]
      congr 1
      funext x
      simp
    rw [h2, hc, Measure.map_smul, Formalism.REAL.invInvariant_of Formalism.REAL.indefinite_unitary_unimodular _ ε]
  rw [hd, Measure.map_smul] at h1
  rw [hd, eq_one_of_smul_haar_eq _ h1, one_smul]

end GlobalTheory.HolDS
