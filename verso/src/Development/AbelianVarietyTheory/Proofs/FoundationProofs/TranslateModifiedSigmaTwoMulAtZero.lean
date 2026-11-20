import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Cval
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormNatCastLe
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.SigmaDuplication

open Filter Topology

/- English proof (translation)
Take `⟨⟨hdiff, hd0, -, -⟩, hzero, -, hwp, -⟩` from `GlobalTheory.OddTheta.sgStar_laws Λ hΛ`. Take `⟨L, hL⟩` from `GlobalTheory.OddTheta.exists_periodPair Λ hΛ`. Establish `h0 : sgStar Λ 0 = 0` using `(hzero 0).2 (zero_mem Λ)`. Establish `hPL : P ∉ L.lattice` using `fun hm => hP ((hL P).2 hm)`. Establish `hwpfun : wpF Λ = L.weierstrassP` using `funext (GlobalTheory.OddTheta.wpF_eq L Λ hL)`.

Establish `hwpd : HasDerivAt (wpF Λ) (wpD Λ P) P`. Rewrite using `[hwpfun, GlobalTheory.LatticeInvariants.wpD_eq hL P, ← congrFun L.deriv_weierstrassP P]`. Conclude with `((L.differentiableOn_weierstrassP P hPL).differentiableAt (L.isClosed_lattice.isOpen_compl.mem_nhds hPL)).hasDerivAt`. Establish `hA : HasDerivAt (fun v => sgStar Λ (P + v)) (deriv (sgStar Λ) (P + P) * 1) P` using `(hdiff (P + P)).hasDerivAt.comp P ((hasDerivAt_id' P).const_add P)`. Establish `hB : HasDerivAt (fun v => sgStar Λ (P - v)) (deriv (sgStar Λ) (P - P) * -1) P` using `(hdiff (P - P)).hasDerivAt.comp P ((hasDerivAt_id' P).const_sub P)`.

Establish `hS` using `(hdiff P).hasDerivAt.pow 2`. Establish `hG` using `(hwpd.sub_const (wpF Λ P)).mul (hS.const_mul (sgStar Λ P ^ 2))`. Establish `hev : (fun v => sgStar Λ (P + v) * sgStar Λ (P - v)) =ᶠ[𝓝 P] (fun v => (wpF Λ v - wpF Λ P) * (sgStar Λ P ^ 2 * sgStar Λ v ^ 2))`. Establish `hne : sgStar Λ P ≠ 0` using `fun h => hP ((hzero P).1 h)`. Use `filter_upwards [(hdiff.continuous.continuousAt (x := P)).eventually_ne hne] with v hv`.

Establish `hvΛ : v ∉ Λ` using `fun hm => hv ((hzero v).2 hm)`. Take the linear combination `hwp P v hP hvΛ`. Establish `huniq` using `(hA.mul hB).unique (hG.congr_of_eventuallyEq hev)`. Simplify using `only [sub_self, h0, hd0, Pi.pow_apply] at huniq`. Rewrite using `[two_mul]`.

Take the linear combination `-huniq`.
-/
theorem sgStar_two_mul {Λ : AddSubgroup ℂ} (hΛ : GlobalTheory.EvenTheta.IsLat Λ) {P : ℂ} (hP : P ∉ Λ) :
    sgStar Λ (2 * P) = -(wpD Λ P) * sgStar Λ P ^ 4 := by
  obtain ⟨⟨hdiff, hd0, -, -⟩, hzero, -, hwp, -⟩ := GlobalTheory.OddTheta.sgStar_laws Λ hΛ
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ hΛ
  have h0 : sgStar Λ 0 = 0 := (hzero 0).2 (zero_mem Λ)
  have hPL : P ∉ L.lattice := fun hm => hP ((hL P).2 hm)
  have hwpfun : wpF Λ = L.weierstrassP := funext (GlobalTheory.OddTheta.wpF_eq L Λ hL)
  have hwpd : HasDerivAt (wpF Λ) (wpD Λ P) P := by
    rw [hwpfun, GlobalTheory.LatticeInvariants.wpD_eq hL P, ← congrFun L.deriv_weierstrassP P]
    exact ((L.differentiableOn_weierstrassP P hPL).differentiableAt
      (L.isClosed_lattice.isOpen_compl.mem_nhds hPL)).hasDerivAt
  have hA : HasDerivAt (fun v => sgStar Λ (P + v)) (deriv (sgStar Λ) (P + P) * 1) P :=
    (hdiff (P + P)).hasDerivAt.comp P ((hasDerivAt_id' P).const_add P)
  have hB : HasDerivAt (fun v => sgStar Λ (P - v)) (deriv (sgStar Λ) (P - P) * -1) P :=
    (hdiff (P - P)).hasDerivAt.comp P ((hasDerivAt_id' P).const_sub P)
  have hS := (hdiff P).hasDerivAt.pow 2
  have hG := (hwpd.sub_const (wpF Λ P)).mul (hS.const_mul (sgStar Λ P ^ 2))
  have hev : (fun v => sgStar Λ (P + v) * sgStar Λ (P - v)) =ᶠ[𝓝 P]
      (fun v => (wpF Λ v - wpF Λ P) * (sgStar Λ P ^ 2 * sgStar Λ v ^ 2)) := by
    have hne : sgStar Λ P ≠ 0 := fun h => hP ((hzero P).1 h)
    filter_upwards [(hdiff.continuous.continuousAt (x := P)).eventually_ne hne] with v hv
    have hvΛ : v ∉ Λ := fun hm => hv ((hzero v).2 hm)
    linear_combination hwp P v hP hvΛ
  have huniq := (hA.mul hB).unique (hG.congr_of_eventuallyEq hev)
  simp only [sub_self, h0, hd0, Pi.pow_apply] at huniq
  rw [two_mul]
  linear_combination -huniq

/- English proof (translation)
Introduce `Λ hΛ P hP`. Use `show sgStar Λ (0 + 2 * P) * Complex.exp _ = -(wpD Λ P) * (sgStar Λ (0 + P) * Complex.exp _) ^ 4`. Rewrite using `[zero_add, zero_add, sgStar_two_mul hΛ hP, mul_pow, ← Complex.exp_nat_mul, mul_assoc]`. Use `congr 2`. Simplify using `only [map_mul, map_ofNat]`.

Use `push_cast`. Put the polynomial expressions in normal form.
-/
theorem U1_two_mul_at_zero_eq_neg_wpD_mul_pow_four : ∀ (Λ : AddSubgroup ℂ), GlobalTheory.EvenTheta.IsLat Λ → ∀ P : ℂ, P ∉ Λ →
    U1 Λ (2 * P) (sgStar Λ) 0 = -(wpD Λ P) * U1 Λ P (sgStar Λ) 0 ^ 4 := by
  intro Λ hΛ P hP
  show sgStar Λ (0 + 2 * P) * Complex.exp _ = -(wpD Λ P) * (sgStar Λ (0 + P) * Complex.exp _) ^ 4
  rw [zero_add, zero_add, sgStar_two_mul hΛ hP, mul_pow, ← Complex.exp_nat_mul, mul_assoc]
  congr 2
  simp only [map_mul, map_ofNat]
  push_cast
  ring_nf

end GlobalTheory.SigmaDuplication
