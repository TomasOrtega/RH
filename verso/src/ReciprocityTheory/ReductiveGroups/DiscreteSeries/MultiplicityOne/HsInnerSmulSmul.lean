import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StCut1p
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

namespace Cut3H

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hsVec_smul (c : ℂ) (A : Wp →L[ℂ] Wp) : hsVec (c • A) = c • hsVec A := rfl

/- English proof (translation)
Unfold `hsInner`. Rewrite using `[hsVec_smul, hsVec_smul, inner_smul_left, inner_smul_right]`. Simplify using `only [starRingEnd_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hsInner_smul_smul (c c' : ℂ) (A B : Wp →L[ℂ] Wp) :
    hsInner (c • A) (c' • B) = c * star c' * hsInner A B := by
  unfold hsInner
  rw [hsVec_smul, hsVec_smul, inner_smul_left, inner_smul_right]
  simp only [starRingEnd_apply]
  ring

end Cut3H

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Cut3H

/- English proof (translation)
Introduce `hInv k r Wp _ _ _ D X hD hSq γ hγ hZ a₁ b₁ a₂ b₂ X₀ p hp`. Establish `hI` using `hInv k r Wp D X hD hSq γ hγ`. Establish `hG : ∀ g ∈ GV k r, gbar k r γ g ∈ GV k r` using `hI.1`. Establish `hmul : ∀ g ∈ GV k r, ∀ g' ∈ GV k r, th k r γ (g * g') = th k r γ g' * th k r γ g` using `hI.2.2.2.2.1`. Establish `thG : ∀ g ∈ GV k r, th k r γ g ∈ GV k r` using `fun g hg => WeylGroupFacts.uh_inv (hG g hg)`.

Establish `hrep` using `X.rep.1.2`. Take `⟨h1, h2, h3, h4⟩` from `hp`. Establish `m1 : (Matrix.of p.1.1 : Mat k r) ∈ GV k r` using `h1.1`. Establish `m2 : (Matrix.of p.1.2 : Mat k r) ∈ GV k r` using `h2.1`. Establish `m3 : (Matrix.of p.2.1 : Mat k r) ∈ GV k r` using `h3.1`.

Establish `m4 : (Matrix.of p.2.2 : Mat k r) ∈ GV k r` using `h4.1`. Use `set A : Mat k r := (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ with hA`. Use `set B : Mat k r := Matrix.of p.2.2 * Matrix.of p.2.1 with hB`. Establish `mA : A ∈ GV k r` using `WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv m1) (WeylGroupFacts.uh_inv m2)`. Establish `mB : B ∈ GV k r` using `WeylGroupFacts.uh_mul m4 m3`.

Use `set P : Wp →L[ℂ] Wp := (D.π (Matrix.of p.1.1)).comp (D.π (Matrix.of p.2.1)⁻¹) with hP`. Use `set x : X.Hs := X.σ (th k r γ A) a₁ with hx`. Use `set y : X.Hs := ContinuousLinearMap.adjoint (X.σ (th k r γ B)) b₁ with hy`. Establish `key : ∀ g : Mat k r, g ∈ GV k r → hsInner (rho D p (scalF Wp (mc X a₁ b₁ ∘ th k r γ)) g) (mc X a₂ b₂ g • X₀) = hsInner P X₀ * (⟪y, X.σ (th k r γ g) x⟫_ℂ * star ⟪b₂, X.σ g a₂⟫_ℂ)`. Introduce `g hg`.

Establish `e1 : sgs p g = A * g * B` using `by simp only [sgs, hA, hB, Matrix.mul_assoc]`. Establish `mAg : A * g ∈ GV k r` using `WeylGroupFacts.uh_mul mA hg`. Establish `e2 : th k r γ (sgs p g) = th k r γ B * (th k r γ g * th k r γ A)`. Rewrite using `[e1, hmul _ mAg _ mB, hmul _ mA _ hg]`. Establish `e3 : X.σ (th k r γ (sgs p g)) = (X.σ (th k r γ B)).comp ((X.σ (th k r γ g)).comp (X.σ (th k r γ A)))`.

Rewrite using `[e2, hrep _ (thG _ mB) _ (WeylGroupFacts.uh_mul (thG _ hg) (thG _ mA)), hrep _ (thG _ hg) _ (thG _ mA)]`. Establish `e4 : rho D p (scalF Wp (mc X a₁ b₁ ∘ th k r γ)) g = (mc X a₁ b₁ (th k r γ (sgs p g))) • P`. Simplify using `only [rho, scalF, Function.comp_apply, hP, hD.π_eq, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, ContinuousLinearMap.id_comp]`. Rewrite using `[e4, hsInner_smul_smul]`. Establish `e5 : mc X a₁ b₁ (th k r γ (sgs p g)) = ⟪y, X.σ (th k r γ g) x⟫_ℂ`.

Rewrite using `[mc, e3, hy, hx, ContinuousLinearMap.adjoint_inner_left]`. Both sides reduce to the same expression. Rewrite using `[e5, mc]`. Expand and normalize the polynomial expressions, which then agree. Unfold `Ph`.

Establish `hae : ∀ᵐ g ∂D.μG, (g : Mt k r) ∈ (GV k r : Set (Mt k r))` using `mem_ae_iff.2 D.haarG.conc`. Rewrite using `[integral_congr_ae (g := fun g : Mt k r => hsInner P X₀ * (⟪y, X.σ (th k r γ (Matrix.of g)) x⟫_ℂ * star ⟪b₂, X.σ (Matrix.of g) a₂⟫_ℂ)) (by filter_upwards [hae] with g hg; exact key _ hg)]`. Rewrite using `[integral_const_mul, hZ x y a₂ b₂, mul_zero]`.
-/
theorem stCut3 (h : UnitaryGroupStructuralFacts) : StCut3 := by
  intro hInv k r Wp _ _ _ D X hD hSq γ hγ hZ a₁ b₁ a₂ b₂ X₀ p hp
  have hI := hInv k r Wp D X hD hSq γ hγ
  have hG : ∀ g ∈ GV k r, gbar k r γ g ∈ GV k r := hI.1
  have hmul : ∀ g ∈ GV k r, ∀ g' ∈ GV k r, th k r γ (g * g') = th k r γ g' * th k r γ g := hI.2.2.2.2.1
  have thG : ∀ g ∈ GV k r, th k r γ g ∈ GV k r := fun g hg => WeylGroupFacts.uh_inv (hG g hg)
  have hrep := X.rep.1.2
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have m1 : (Matrix.of p.1.1 : Mat k r) ∈ GV k r := h1.1
  have m2 : (Matrix.of p.1.2 : Mat k r) ∈ GV k r := h2.1
  have m3 : (Matrix.of p.2.1 : Mat k r) ∈ GV k r := h3.1
  have m4 : (Matrix.of p.2.2 : Mat k r) ∈ GV k r := h4.1
  set A : Mat k r := (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ with hA
  set B : Mat k r := Matrix.of p.2.2 * Matrix.of p.2.1 with hB
  have mA : A ∈ GV k r := WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv m1) (WeylGroupFacts.uh_inv m2)
  have mB : B ∈ GV k r := WeylGroupFacts.uh_mul m4 m3
  set P : Wp →L[ℂ] Wp := (D.π (Matrix.of p.1.1)).comp (D.π (Matrix.of p.2.1)⁻¹) with hP
  set x : X.Hs := X.σ (th k r γ A) a₁ with hx
  set y : X.Hs := ContinuousLinearMap.adjoint (X.σ (th k r γ B)) b₁ with hy
  have key : ∀ g : Mat k r, g ∈ GV k r →
      hsInner (rho D p (scalF Wp (mc X a₁ b₁ ∘ th k r γ)) g) (mc X a₂ b₂ g • X₀) =
        hsInner P X₀ * (⟪y, X.σ (th k r γ g) x⟫_ℂ * star ⟪b₂, X.σ g a₂⟫_ℂ) := by
    intro g hg
    have e1 : sgs p g = A * g * B := by simp only [sgs, hA, hB, Matrix.mul_assoc]
    have mAg : A * g ∈ GV k r := WeylGroupFacts.uh_mul mA hg
    have e2 : th k r γ (sgs p g) = th k r γ B * (th k r γ g * th k r γ A) := by
      rw [e1, hmul _ mAg _ mB, hmul _ mA _ hg]
    have e3 : X.σ (th k r γ (sgs p g)) =
        (X.σ (th k r γ B)).comp ((X.σ (th k r γ g)).comp (X.σ (th k r γ A))) := by
      rw [e2, hrep _ (thG _ mB) _ (WeylGroupFacts.uh_mul (thG _ hg) (thG _ mA)), hrep _ (thG _ hg) _ (thG _ mA)]
    have e4 : rho D p (scalF Wp (mc X a₁ b₁ ∘ th k r γ)) g = (mc X a₁ b₁ (th k r γ (sgs p g))) • P := by
      simp only [rho, scalF, Function.comp_apply, hP, hD.π_eq, ContinuousLinearMap.smul_comp,
        ContinuousLinearMap.comp_smul, ContinuousLinearMap.id_comp]
    rw [e4, hsInner_smul_smul]
    have e5 : mc X a₁ b₁ (th k r γ (sgs p g)) = ⟪y, X.σ (th k r γ g) x⟫_ℂ := by
      rw [mc, e3, hy, hx, ContinuousLinearMap.adjoint_inner_left]
      rfl
    rw [e5, mc]
    ring
  unfold Ph
  have hae : ∀ᵐ g ∂D.μG, (g : Mt k r) ∈ (GV k r : Set (Mt k r)) := mem_ae_iff.2 D.haarG.conc
  rw [integral_congr_ae (g := fun g : Mt k r =>
      hsInner P X₀ * (⟪y, X.σ (th k r γ (Matrix.of g)) x⟫_ℂ * star ⟪b₂, X.σ (Matrix.of g) a₂⟫_ℂ))
    (by filter_upwards [hae] with g hg; exact key _ hg)]
  rw [integral_const_mul, hZ x y a₂ b₂, mul_zero]

end ReciprocityTheory.ChartRestriction.DS.Mult1
