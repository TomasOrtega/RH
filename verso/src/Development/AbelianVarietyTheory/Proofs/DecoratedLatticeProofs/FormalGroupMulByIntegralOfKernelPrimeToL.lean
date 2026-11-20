import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementC
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementK
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveSecondLogDerivative
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.AnalyticTransOfAdd
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.CmIntegralityOfTorsionPoints
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.IsogenyFormulaInstance
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SecondLogDerivativeUnique

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

namespace GlobalTheory.Honda

open Formalism.L2.Th1 in

/- English proof (translation)
Introduce `L l _ hl ι h2 h3 hD β N hst hβ hN hlN hker`. Establish `hβp : ι β ≠ 0`. Introduce `h`. Rewrite `hβ` using `[h, norm_zero]`. Conclude with `zero_ne_one hβ`.

Establish `hβ0 : β ≠ 0`. Introduce `h`. Rewrite `hβp` using `[h, map_zero]`. Conclude with `hβp rfl`. Establish `hW : E.IntCurve (E.curveL l L ι)` using `E.ScaledModelNorms.intCurve_short l hl _ _ h2 h3 hD`.

Establish `hΔ : (E.curveL l L ι).Δ ≠ 0`. Introduce `h`. Use `hW.2.2.2.2.2` as an intermediate fact. Rewrite `this` using `[h, norm_zero]`. Conclude with `zero_ne_one this`.

Establish `htwo` using `E.ScaledModelNorms.norm_two l hl`. Establish `hC : C.CoeffIn (Formalism.G.unitBall ℂ_[l]) (E.curveL l L ι)` using `⟨hW.1, hW.2.1, hW.2.2.1, hW.2.2.2.1, hW.2.2.2.2.1⟩`. Take `⟨S, hS⟩` from `F.kerRepsExist L β hβ0 hst`. Take `⟨neg, -, hE⟩` from `F.endoZInstance L β S hβ0 hst hS`. Establish `hb2 : (E.curveL l L ι).b₂ = 0` using `(A.shortInv ℂ_[l] _ _).1`.

Establish `hEp` using `D.CurveNormEndomorphisms.isEndoZ_map (ι : ℂ →+* ℂ_[l]) hE`. Rewrite `hEp` using `[← E.wpBridge l L ι]`. Establish `hEp' : C.IsEndoZ (A.wpReg (E.curveL l L ι)) neg (fun P : S => ι (L.weierstrassP (P : ℂ)) + (E.curveL l L ι).b₂ / 12) (fun P : S => PowerSeries.map (ι : ℂ →+* ℂ_[l]) (F.taylor0 (fun z => L.weierstrassP (z + (P : ℂ))))) (ι β)`. Rewrite using `[hb2]`. Simplify using `using hEp`.

Establish `hint : ∀ P : S, ‖ι (L.weierstrassP (P : ℂ))‖ ≤ 1 ∧ ‖ι (L.derivWeierstrassP (P : ℂ))‖ ≤ 1`. Introduce `P`. Use `E.cm4Int L l hl ι 1 one_ne_zero (by simpa using h2) (by simpa using h3) (by simpa using hD) (P : ℂ) N hN hlN (hker _ (hS.1 P P.2).1) (hS.1 P P.2).2` as an intermediate fact. Simplify using `using this`. Take `⟨hLP, hXW, hA, -, -⟩` from `C.curveFrame ℂ_[l] (Formalism.G.unitBall ℂ_[l]) (E.curveL l L ι) hC`.

Establish `hinv : ∀ x : ℂ_[l], ‖x‖ = 1 → x⁻¹ ∈ Formalism.G.unitBall ℂ_[l]`. Introduce `x hx`. Use `show ‖x⁻¹‖ ≤ 1`. Rewrite using `[norm_inv, hx, inv_one]`. Establish `hM` using `A.coeffMem.{0} ℂ_[l] (E.curveL l L ι) (Formalism.G.unitBall ℂ_[l]) hC.1 hC.2.1 hC.2.2.1 hC.2.2.2.1 hC.2.2.2.2`.

Establish `key` using `C.endIntFromDatum ℂ_[l] (Formalism.G.unitBall ℂ_[l]) (A.wpReg (E.curveL l L ι)) (A.logSer (E.curveL l L ι)) (A.expSer (E.curveL l L ι)) (A.xS (E.curveL l L ι)) ((E.curveL l L ι).b₂ / 12) S neg (fun P : S => ι (L.weierstrassP (P : ℂ))) (fun P : S => PowerSeries.map (ι : ℂ →+* ℂ_[l …`. Conclude with `fun n => key n`. Introduce `P`. Rewrite using `[hb2, zero_div, map_zero, add_zero]`. Conclude with `E.transWpBridge l L ι (P : ℂ) (hS.1 P P.2).2`.

Introduce `P n`. Unfold `E.xT`. Use `beta_reduce`. Rewrite using `[E.ScaledModelNorms.px_ptOf l L ι hΔ _ (hS.1 P P.2).2, E.ScaledModelNorms.py_ptOf l L ι hΔ _ (hS.1 P P.2).2]`. Use `(hM.2.2.2.2.2.2.2.2.2.2 _ (hint P).1 _ ?_ n).1` and prove the remaining obligations.

Use `show ‖ι (L.derivWeierstrassP (P : ℂ)) / 2‖ ≤ 1`. Rewrite using `[norm_div, htwo, div_one]`. Conclude with `(hint P).2`.
-/
theorem mulBy_coefLe_of_kernel_prime_to :
    ∀ (L : PeriodPair) (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ (ι : ℂ ≃+* ℂ_[l]), ‖ι L.g₂‖ ≤ 1 → ‖ι L.g₃‖ ≤ 1 → ‖ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2‖ = 1 → ∀ (β : ℂ) (N : ℕ), Formalism.L2.Th1.F.MulStable L β → ‖ι β‖ = 1 → 0 < N → ¬ l ∣ N → (∀ z, β * z ∈ L.lattice → (N : ℂ) * z ∈ L.lattice) → CoefLe 1 (Formalism.L2.Th1.C.mulBy (Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃))) (Formalism.L2.Th1.A.expSer (Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃))) (ι β)) := by
  intro L l _ hl ι h2 h3 hD β N hst hβ hN hlN hker
  have hβp : ι β ≠ 0 := by
    intro h
    rw [h, norm_zero] at hβ
    exact zero_ne_one hβ
  have hβ0 : β ≠ 0 := by
    intro h
    rw [h, map_zero] at hβp
    exact hβp rfl
  have hW : E.IntCurve (E.curveL l L ι) := E.ScaledModelNorms.intCurve_short l hl _ _ h2 h3 hD
  have hΔ : (E.curveL l L ι).Δ ≠ 0 := by
    intro h
    have := hW.2.2.2.2.2
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have htwo := E.ScaledModelNorms.norm_two l hl
  have hC : C.CoeffIn (Formalism.G.unitBall ℂ_[l]) (E.curveL l L ι) :=
    ⟨hW.1, hW.2.1, hW.2.2.1, hW.2.2.2.1, hW.2.2.2.2.1⟩
  obtain ⟨S, hS⟩ := F.kerRepsExist L β hβ0 hst
  obtain ⟨neg, -, hE⟩ := F.endoZInstance L β S hβ0 hst hS
  have hb2 : (E.curveL l L ι).b₂ = 0 := (A.shortInv ℂ_[l] _ _).1
  have hEp := D.CurveNormEndomorphisms.isEndoZ_map (ι : ℂ →+* ℂ_[l]) hE
  rw [← E.wpBridge l L ι] at hEp
  have hEp' : C.IsEndoZ (A.wpReg (E.curveL l L ι)) neg
      (fun P : S => ι (L.weierstrassP (P : ℂ)) + (E.curveL l L ι).b₂ / 12)
      (fun P : S => PowerSeries.map (ι : ℂ →+* ℂ_[l])
        (F.taylor0 (fun z => L.weierstrassP (z + (P : ℂ))))) (ι β) := by
    rw [hb2]
    simpa using hEp
  have hint : ∀ P : S, ‖ι (L.weierstrassP (P : ℂ))‖ ≤ 1 ∧ ‖ι (L.derivWeierstrassP (P : ℂ))‖ ≤ 1 := by
    intro P
    have := E.cm4Int L l hl ι 1 one_ne_zero (by simpa using h2) (by simpa using h3) (by simpa using hD)
      (P : ℂ) N hN hlN (hker _ (hS.1 P P.2).1) (hS.1 P P.2).2
    simpa using this
  obtain ⟨hLP, hXW, hA, -, -⟩ := C.curveFrame ℂ_[l] (Formalism.G.unitBall ℂ_[l]) (E.curveL l L ι) hC
  have hinv : ∀ x : ℂ_[l], ‖x‖ = 1 → x⁻¹ ∈ Formalism.G.unitBall ℂ_[l] := by
    intro x hx
    show ‖x⁻¹‖ ≤ 1
    rw [norm_inv, hx, inv_one]
  have hM := A.coeffMem.{0} ℂ_[l] (E.curveL l L ι) (Formalism.G.unitBall ℂ_[l]) hC.1 hC.2.1 hC.2.2.1 hC.2.2.2.1
    hC.2.2.2.2
  have key := C.endIntFromDatum ℂ_[l] (Formalism.G.unitBall ℂ_[l]) (A.wpReg (E.curveL l L ι))
    (A.logSer (E.curveL l L ι)) (A.expSer (E.curveL l L ι)) (A.xS (E.curveL l L ι))
    ((E.curveL l L ι).b₂ / 12) S neg (fun P : S => ι (L.weierstrassP (P : ℂ)))
    (fun P : S => PowerSeries.map (ι : ℂ →+* ℂ_[l])
        (F.taylor0 (fun z => L.weierstrassP (z + (P : ℂ)))))
    (fun P : S => E.xT (E.curveL l L ι) (E.ptOf l L ι (P : ℂ))) (ι β)
    ((ι β)⁻¹ * ((Fintype.card S : ℂ_[l]) + 1)) hLP hXW hA (hinv _ htwo)
    ⟨hEp', by rw [← mul_assoc, mul_inv_cancel₀ hβp, one_mul], ?_, ?_, fun P => (hint P).1, hβ.le,
      hinv _ hβ, by rw [hb2, zero_div, mul_zero]; exact zero_mem _⟩
  · exact fun n => key n
  · intro P
    rw [hb2, zero_div, map_zero, add_zero]
    exact E.transWpBridge l L ι (P : ℂ) (hS.1 P P.2).2
  · intro P n
    unfold E.xT
    beta_reduce
    rw [E.ScaledModelNorms.px_ptOf l L ι hΔ _ (hS.1 P P.2).2, E.ScaledModelNorms.py_ptOf l L ι hΔ _ (hS.1 P P.2).2]
    refine (hM.2.2.2.2.2.2.2.2.2.2 _ (hint P).1 _ ?_ n).1
    show ‖ι (L.derivWeierstrassP (P : ℂ)) / 2‖ ≤ 1
    rw [norm_div, htwo, div_one]
    exact (hint P).2

end GlobalTheory.Honda
