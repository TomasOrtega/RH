import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgAnTrans

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

/- English proof (translation)
Take `⟨neg, hneg, hinv, -, hid⟩` from `F.endoZInstance L α S hα hst hS`. Establish `hb2 : (A.shortW (ι L.g₂) (ι L.g₃)).b₂ = 0`. Simplify using `[A.shortW, WeierstrassCurve.b₂]`. Establish `hnegeq : ∀ P : S, (neg P : ℂ) = -(P : ℂ) + ((⟨_, hneg P⟩ : L.lattice) : ℂ)`. Introduce `P`.

Simplify using the standard rewrite rules. Use `⟨neg, ?_, hinv, ?_, ?_⟩` and prove the remaining obligations. Introduce `P`. Establish `h` using `L.derivWeierstrassP_sq (P : ℂ) (hS.1 P P.2).2`. Establish `h'` using `congrArg ι h`.

Simplify using `only [map_pow, map_sub, map_mul, map_ofNat] at h'`. Rewrite using `[WeierstrassCurve.Affine.equation_iff]`. Simplify using `only [A.shortW]`. Take the linear combination `(1 / 4 : ℂ_[l]) * h'`. Introduce `P`.

Prove the components needed by the constructor for the conclusion. Use `show ι (L.weierstrassP (neg P : ℂ)) = _`. Rewrite using `[hnegeq P, L.weierstrassP_add_coe, L.weierstrassP_neg]`. Use `show ι (L.derivWeierstrassP (neg P : ℂ)) / 2 = _`. Rewrite using `[hnegeq P, L.derivWeierstrassP_add_coe, L.derivWeierstrassP_neg]`.

Simplify using `[WeierstrassCurve.Affine.negY, A.shortW, neg_div]`. Establish `h` using `congrArg (PowerSeries.map (ι : ℂ →+* ℂ_[l])) hid`. Rewrite using `[wp_bridge]`. Simplify using `only [C.wTr, hb2, zero_div, add_zero, map_zero]`. Simplify using `only [← trans_bridge l L ι _ (hS.1 _ (Subtype.coe_prop _)).2]`.

Simplify using `only [map_mul, map_add, map_sum, map_sub, PowerSeries.map_C, map_pow] at h`. Establish `hr : PowerSeries.map (ι : ℂ →+* ℂ_[l]) (PowerSeries.rescale α (F.pSeries L)) = PowerSeries.rescale (ι α) (PowerSeries.map (ι : ℂ →+* ℂ_[l]) (F.pSeries L))`. Use extensionality with `n`. Simplify using `[PowerSeries.coeff_rescale]`. Rewrite `h` using `[hr]`.

Simplify using `using h`.
-/
theorem endo_curve (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (α : ℂ)
    (S : Finset ℂ) (hα : α ≠ 0) (hst : F.MulStable L α) (hS : F.IsKerReps L α S) :
    ∃ neg : S → S, C.IsEndoCurve (A.shortW (ι L.g₂) (ι L.g₃)) neg
      (fun P : S => ι (L.weierstrassP (P : ℂ))) (fun P : S => ι (L.derivWeierstrassP (P : ℂ)) / 2)
      (ι α) := by
  obtain ⟨neg, hneg, hinv, -, hid⟩ := F.endoZInstance L α S hα hst hS
  have hb2 : (A.shortW (ι L.g₂) (ι L.g₃)).b₂ = 0 := by
    simp [A.shortW, WeierstrassCurve.b₂]
  have hnegeq : ∀ P : S, (neg P : ℂ) = -(P : ℂ) + ((⟨_, hneg P⟩ : L.lattice) : ℂ) := by
    intro P
    simp
  refine ⟨neg, ?_, hinv, ?_, ?_⟩
  · intro P
    have h := L.derivWeierstrassP_sq (P : ℂ) (hS.1 P P.2).2
    have h' := congrArg ι h
    simp only [map_pow, map_sub, map_mul, map_ofNat] at h'
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [A.shortW]
    linear_combination (1 / 4 : ℂ_[l]) * h'
  · intro P
    constructor
    · show ι (L.weierstrassP (neg P : ℂ)) = _
      rw [hnegeq P, L.weierstrassP_add_coe, L.weierstrassP_neg]
    · show ι (L.derivWeierstrassP (neg P : ℂ)) / 2 = _
      rw [hnegeq P, L.derivWeierstrassP_add_coe, L.derivWeierstrassP_neg]
      simp [WeierstrassCurve.Affine.negY, A.shortW, neg_div]
  · have h := congrArg (PowerSeries.map (ι : ℂ →+* ℂ_[l])) hid
    rw [wp_bridge]
    simp only [C.wTr, hb2, zero_div, add_zero, map_zero]
    simp only [← trans_bridge l L ι _ (hS.1 _ (Subtype.coe_prop _)).2]
    simp only [map_mul, map_add, map_sum, map_sub, PowerSeries.map_C, map_pow] at h
    have hr : PowerSeries.map (ι : ℂ →+* ℂ_[l]) (PowerSeries.rescale α (F.pSeries L))
        = PowerSeries.rescale (ι α) (PowerSeries.map (ι : ℂ →+* ℂ_[l]) (F.pSeries L)) := by
      ext n
      simp [PowerSeries.coeff_rescale]
    rw [hr] at h
    simpa using h

end ReciprocityTheory.ChartRestriction.L1
