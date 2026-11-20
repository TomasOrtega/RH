import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodicEqZeroOfFourierCoefficientsZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerCoefficientRationalMirabolicMulStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalMirabolicMovingRowToLastStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace GeneralLinearInduction

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {ψ : AddChar (Ad E) ℂ}

/- English proof (translation)
Introduce `g₀ hg`. Establish `hPer : Per (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1))) (fun x => f (blkU x * g₀))` using `per_blk hG.cont (fun c g => hG.left _ (isMir_blkU c) g) g₀`. Establish `hΦ : (fun x : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E => f (blkU x * g₀)) = 0`. Use `_root_.GlobalTheory.T.periodic_eq_zero_of_fourier_coefficients_zero E _ ψ hψ _ hPer fun ξ => ?_` and prove the remaining obligations. Distinguish the cases in `hξ0 : ξ = 0`.

Substitute `hξ0` using the available equality. Establish `hv` using `hG.van (m + 1) (Nat.succ_pos m) le_rfl g₀`. Establish `e : ∀ x : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E, ψ (-dot (0 : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E) x) = 1`. Introduce `x`. Simplify using `[dot]`.

Simplify using `only [e, one_mul]`. Conclude with `hv`. Take `⟨γ, hγ, hγξ⟩` from `_root_.GlobalTheory.T.exists_rationalMirabolic_moving_row_to_last E a m hma ξ hξ0`. Establish `h1` using `hc _ (hZ γ hγ g₀ hg)`. Simplify using `only [colT] at h1`.

Rewrite `h1` using `[_root_.GlobalTheory.T.whittakerCoefficient_rationalMirabolic_mul E a ψ hψ m f hG.cont hG.left γ hγ (eLast a (m + 1)) g₀]`. Establish `e : (fun t : UnipotentBlockColumnIndex a (m + 1) (m + 1) => ∑ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), eLast a (m + 1) s * γ.val s.1.1 t.1.1) = ξ` using `funext hγξ`. Rewrite `h1` using `[e]`. Conclude with `h1`. Establish `h1` using `congrFun hΦ 0`.

Simplify using `only [Pi.zero_apply] at h1`. Establish `e : (blkU (0 : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) : GA E a) = 1` using `posU_zero _`. Rewrite `h1` using `[e, one_mul]`. Conclude with `h1`.
-/
theorem step (hψ : StdPsi ψ) (m : ℕ) (f : GA E a → ℂ) (hma : m + 1 < a) (hG : Good ψ (m + 1) f)
    (Z : Set (GA E a)) (hZ : ∀ γ, IsMir (m + 1) γ → ∀ g ∈ Z, ratGL E a γ * g ∈ Z)
    (hc : ∀ g ∈ Z, colT ψ (m + 1) f g = 0) : ∀ g ∈ Z, f g = 0 := by
  intro g₀ hg
  have hPer : Per (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1))) (fun x => f (blkU x * g₀)) :=
    per_blk hG.cont (fun c g => hG.left _ (isMir_blkU c) g) g₀
  have hΦ : (fun x : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E => f (blkU x * g₀)) = 0 := by
    refine _root_.GlobalTheory.T.periodic_eq_zero_of_fourier_coefficients_zero E _ ψ hψ _ hPer fun ξ => ?_
    by_cases hξ0 : ξ = 0
    · subst hξ0
      have hv := hG.van (m + 1) (Nat.succ_pos m) le_rfl g₀
      have e : ∀ x : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E,
          ψ (-dot (0 : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E) x) = 1 := by
        intro x
        simp [dot]
      simp only [e, one_mul]
      exact hv
    · obtain ⟨γ, hγ, hγξ⟩ := _root_.GlobalTheory.T.exists_rationalMirabolic_moving_row_to_last E a m hma ξ hξ0
      have h1 := hc _ (hZ γ hγ g₀ hg)
      simp only [colT] at h1
      rw [_root_.GlobalTheory.T.whittakerCoefficient_rationalMirabolic_mul E a ψ hψ m f hG.cont hG.left γ hγ (eLast a (m + 1)) g₀] at h1
      have e : (fun t : UnipotentBlockColumnIndex a (m + 1) (m + 1) =>
          ∑ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), eLast a (m + 1) s * γ.val s.1.1 t.1.1) = ξ := funext hγξ
      rw [e] at h1
      exact h1
  have h1 := congrFun hΦ 0
  simp only [Pi.zero_apply] at h1
  have e : (blkU (0 : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) : GA E a) = 1 := posU_zero _
  rw [e, one_mul] at h1
  exact h1

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => intro f _ _ Z _ hw`. Conclude with `hw`. Consider the case `succ m ih`. Introduce `f hm hG Z hZ hw`.

Establish `hma : m + 1 < a` using `by omega`. Use `step hψ m f hma hG Z hZ ?_` and prove the remaining obligations. Use `ih _ (Or.inl (by omega)) (_root_.GlobalTheory.CuspRep.Generic.good_colT hψ hma hG) Z (fun γ hγ g hg => hZ γ (fun i k h => hγ i k (by omega)) g hg) ?_` and prove the remaining obligations. Introduce `g hg`. Conclude with `hw g hg`.
-/
theorem main (hψ : StdPsi ψ) (m : ℕ) : ∀ (f : GA E a → ℂ), (m < a ∨ m = 0) → Good ψ m f →
    ∀ Z : Set (GA E a), (∀ γ, IsMir m γ → ∀ g ∈ Z, ratGL E a γ * g ∈ Z) →
      (∀ g ∈ Z, whit ψ m f g = 0) → ∀ g ∈ Z, f g = 0 := by
  induction m with
  | zero => intro f _ _ Z _ hw; exact hw
  | succ m ih =>
    intro f hm hG Z hZ hw
    have hma : m + 1 < a := by omega
    refine step hψ m f hma hG Z hZ ?_
    refine ih _ (Or.inl (by omega)) (_root_.GlobalTheory.CuspRep.Generic.good_colT hψ hma hG) Z
      (fun γ hγ g hg => hZ γ (fun i k h => hγ i k (by omega)) g hg) ?_
    intro g hg
    exact hw g hg

end GeneralLinearInduction

/- English proof (translation)
Introduce `E _ _ _ a ψ hψ m f hm hG Z hZ _ hw`. Conclude with `GeneralLinearInduction.main hψ m f hm hG Z hZ hw`.
-/
theorem induction_g11_holds : FourierUniquenessMirabolic := by
  intro E _ _ _ a ψ hψ m f hm hG Z hZ _ hw
  exact GeneralLinearInduction.main hψ m f hm hG Z hZ hw

end PositivityTheory.jumpWindows

end
