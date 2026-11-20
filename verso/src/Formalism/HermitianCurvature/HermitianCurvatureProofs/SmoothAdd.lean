import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LowSmooth
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.Smooth

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate ContDiff

noncomputable section

set_option maxHeartbeats 1600000

namespace Formalism.FourierDecayAlt.P.DDSmoothness

open Formalism.FourierDecayAlt.ThreeDimData

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Smooth

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/- English proof (translation)
Simplify using `only [PI.UpqRep.smoothVecs, Set.mem_setOf_eq, PI.UpqRep.IsSmoothVec, PI.UpqRep.SmoothOnH]`. Introduce `g₀ _`. Conclude with `⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun g _ _ => map_zero (σ g)⟩`.
-/
theorem smooth_zero (σ : Mx k r → (H →L[ℂ] H)) : (0 : H) ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
  simp only [PI.UpqRep.smoothVecs, Set.mem_setOf_eq, PI.UpqRep.IsSmoothVec, PI.UpqRep.SmoothOnH]
  intro g₀ _
  exact ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun g _ _ => map_zero (σ g)⟩

/- English proof (translation)
Simplify using `only [PI.UpqRep.smoothVecs, Set.mem_setOf_eq, PI.UpqRep.IsSmoothVec, PI.UpqRep.SmoothOnH] at hv hw ⊢`. Introduce `g₀ hg₀`. Take `⟨U, F, hU, hgU, hF, hFe⟩` from `hv g₀ hg₀`. Take `⟨V, G, hV, hgV, hG, hGe⟩` from `hw g₀ hg₀`. Use `⟨U ∩ V, fun g => F g + G g, hU.inter hV, ⟨hgU, hgV⟩, (hF.mono Set.inter_subset_left).add (hG.mono Set.inter_subset_right), fun g hg hgH => ?_⟩` and prove the remaining obligations.

Simplify using `only [map_add, hFe g hg.1 hgH, hGe g hg.2 hgH]`.
-/
theorem smooth_add {σ : Mx k r → (H →L[ℂ] H)} {v w : H} (hv : v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ)
    (hw : w ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ) : v + w ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
  simp only [PI.UpqRep.smoothVecs, Set.mem_setOf_eq, PI.UpqRep.IsSmoothVec, PI.UpqRep.SmoothOnH] at hv hw ⊢
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hFe⟩ := hv g₀ hg₀
  obtain ⟨V, G, hV, hgV, hG, hGe⟩ := hw g₀ hg₀
  refine ⟨U ∩ V, fun g => F g + G g, hU.inter hV, ⟨hgU, hgV⟩,
    (hF.mono Set.inter_subset_left).add (hG.mono Set.inter_subset_right), fun g hg hgH => ?_⟩
  simp only [map_add, hFe g hg.1 hgH, hGe g hg.2 hgH]

/- English proof (translation)
Simplify using `only [PI.UpqRep.smoothVecs, Set.mem_setOf_eq, PI.UpqRep.IsSmoothVec, PI.UpqRep.SmoothOnH] at hv ⊢`. Introduce `g₀ hg₀`. Take `⟨U, F, hU, hgU, hF, hFe⟩` from `hv g₀ hg₀`. Use `⟨U, fun g => a • F g, hU, hgU, hF.const_smul a, fun g hg hgH => ?_⟩` and prove the remaining obligations. Simplify using `only [map_smul, hFe g hg hgH]`.
-/
theorem smooth_smul {σ : Mx k r → (H →L[ℂ] H)} (a : ℂ) {v : H} (hv : v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ) :
    a • v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
  simp only [PI.UpqRep.smoothVecs, Set.mem_setOf_eq, PI.UpqRep.IsSmoothVec, PI.UpqRep.SmoothOnH] at hv ⊢
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hFe⟩ := hv g₀ hg₀
  refine ⟨U, fun g => a • F g, hU, hgU, hF.const_smul a, fun g hg hgH => ?_⟩
  simp only [map_smul, hFe g hg hgH]

/- English proof (translation)
Take `⟨P, ⟨⟨hPu, hPJ⟩, hPun⟩, hDS⟩` from `hσ`. Establish `hdet : IsUnit P.det` using `(Matrix.isUnit_iff_isUnit_det P).mp hPu`. Establish `hPP : P⁻¹ * P = 1` using `Matrix.nonsing_inv_mul P hdet`. Establish `hrep` using `hDS.2.2.1.1.2`. Establish `hconj` using `Formalism.QuantumDeterminants.unitary_conjugation_holds _ ε (PI.UpqRep.Hpk k r) P hdet hPJ`.

Establish `hback : ∀ g, P⁻¹ * (P * g * P⁻¹) * P = g`. Introduce `g`. Rewrite using `[show P⁻¹ * (P * g * P⁻¹) * P = (P⁻¹ * P) * g * (P⁻¹ * P) by simp only [Matrix.mul_assoc], hPP, Matrix.one_mul, Matrix.mul_one]`. Establish `hmul : ∀ a b, PI.UpqRep.inUH (PI.UpqRep.Hpk k r) a → PI.UpqRep.inUH (PI.UpqRep.Hpk k r) b → σ (a * b) = (σ a).comp (σ b)`. Introduce `a b ha hb`.

Establish `ha'` using `(hconj a).mp ha`. Establish `hb'` using `(hconj b).mp hb`. Establish `h` using `hrep _ ha' _ hb'`. Simplify using `only [hback] at h`. Rewrite using `[← h]`.

Use `congr 1`. Rewrite using `[show P⁻¹ * (P * a * P⁻¹ * (P * b * P⁻¹)) * P = (P⁻¹ * P) * a * (P⁻¹ * P) * b * (P⁻¹ * P) by`. Simplify using `only [Matrix.mul_assoc], hPP, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one]`. Establish `hinUH : ∀ a b, PI.UpqRep.inUH (PI.UpqRep.Hpk k r) a → PI.UpqRep.inUH (PI.UpqRep.Hpk k r) b → PI.UpqRep.inUH (PI.UpqRep.Hpk k r) (a * b)`. Introduce `a b ha hb`.

Unfold `PI.UpqRep.inUH at *`. Rewrite using `[Matrix.conjTranspose_mul, show bᴴ * aᴴ * PI.UpqRep.Hpk k r * (a * b) = bᴴ * (aᴴ * PI.UpqRep.Hpk k r * a) * b by simp only [Matrix.mul_assoc], ha, hb]`. Establish `hw0 : PI.UpqRep.SmoothOnH (PI.UpqRep.Hpk k r) (fun g => σ g w0)` using `low_smooth_of_k_finite hK k r ε lam H σ w0 hl ⟨P, ⟨⟨hPu, hPJ⟩, hPun⟩, hDS⟩ hw`. Establish `htr : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), σ g w0 ∈ PI.UpqRep.smoothVecs (k` using `k) (r := r) σ := by`. Introduce `g hg`.

Establish `hgH : PI.UpqRep.inUH (PI.UpqRep.Hpk k r) g` using `hg`. Establish `hcd : ContDiff ℝ ∞ (fun x : Mx k r => x * g)` using `(LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ g)).contDiff`. Use `show PI.UpqRep.SmoothOnH (PI.UpqRep.Hpk k r) (fun g' => σ g' (σ g w0))`. Introduce `g₀ hg₀`. Take `⟨U, F, hU, hgU, hF, hFeq⟩` from `hw0 (g₀ * g) (hinUH _ _ hg₀ hgH)`.

Use `⟨(fun x => x * g) ⁻¹' U, fun x => F (x * g), hU.preimage hcd.continuous, hgU, hF.comp hcd.contDiffOn (fun x hx => hx), ?_⟩` and prove the remaining obligations. Introduce `x hx hxH`. Establish `hx'` using `hFeq (x * g) hx (hinUH _ _ hxH hgH)`. Simplify using `only at hx'`. Use `show σ x (σ g w0) = F (x * g)`.

Rewrite using `[← hx', hmul x g hxH hgH]`. Both sides reduce to the same expression. Introduce `x hx`. Unfold `DDsp at hx`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem y hy`. Take `⟨g, hg, rfl⟩` from `hy`. Conclude with `htr g hg`. Consider the case `zero => exact smooth_zero σ`. Consider the case `add y z _ _ hy hz => exact smooth_add hy hz`.

Consider the case `smul a y _ hy => exact smooth_smul a hy`.
-/
theorem DD_smooth (hK : PI.KFinSmooth) {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    [CompleteSpace H] {σ : Mx k r → (H →L[ℂ] H)} {w0 : H}
    (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) (hw : PI.UpqRep.IsLowUnitH k r ε lam σ w0) :
    ∀ x ∈ DDsp σ w0, x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
  obtain ⟨P, ⟨⟨hPu, hPJ⟩, hPun⟩, hDS⟩ := hσ
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have hrep := hDS.2.2.1.1.2
  have hconj := Formalism.QuantumDeterminants.unitary_conjugation_holds _ ε (PI.UpqRep.Hpk k r) P hdet hPJ
  have hback : ∀ g, P⁻¹ * (P * g * P⁻¹) * P = g := by
    intro g
    rw [show P⁻¹ * (P * g * P⁻¹) * P = (P⁻¹ * P) * g * (P⁻¹ * P) by simp only [Matrix.mul_assoc],
      hPP, Matrix.one_mul, Matrix.mul_one]
  have hmul : ∀ a b, PI.UpqRep.inUH (PI.UpqRep.Hpk k r) a → PI.UpqRep.inUH (PI.UpqRep.Hpk k r) b →
      σ (a * b) = (σ a).comp (σ b) := by
    intro a b ha hb
    have ha' := (hconj a).mp ha
    have hb' := (hconj b).mp hb
    have h := hrep _ ha' _ hb'
    simp only [hback] at h
    rw [← h]
    congr 1
    rw [show P⁻¹ * (P * a * P⁻¹ * (P * b * P⁻¹)) * P = (P⁻¹ * P) * a * (P⁻¹ * P) * b * (P⁻¹ * P) by
      simp only [Matrix.mul_assoc], hPP, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one]
  have hinUH : ∀ a b, PI.UpqRep.inUH (PI.UpqRep.Hpk k r) a → PI.UpqRep.inUH (PI.UpqRep.Hpk k r) b →
      PI.UpqRep.inUH (PI.UpqRep.Hpk k r) (a * b) := by
    intro a b ha hb
    unfold PI.UpqRep.inUH at *
    rw [Matrix.conjTranspose_mul, show bᴴ * aᴴ * PI.UpqRep.Hpk k r * (a * b) =
      bᴴ * (aᴴ * PI.UpqRep.Hpk k r * a) * b by simp only [Matrix.mul_assoc], ha, hb]
  have hw0 : PI.UpqRep.SmoothOnH (PI.UpqRep.Hpk k r) (fun g => σ g w0) :=
    low_smooth_of_k_finite hK k r ε lam H σ w0 hl ⟨P, ⟨⟨hPu, hPJ⟩, hPun⟩, hDS⟩ hw
  have htr : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), σ g w0 ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
    intro g hg
    have hgH : PI.UpqRep.inUH (PI.UpqRep.Hpk k r) g := hg
    have hcd : ContDiff ℝ ∞ (fun x : Mx k r => x * g) :=
      (LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ g)).contDiff
    show PI.UpqRep.SmoothOnH (PI.UpqRep.Hpk k r) (fun g' => σ g' (σ g w0))
    intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hFeq⟩ := hw0 (g₀ * g) (hinUH _ _ hg₀ hgH)
    refine ⟨(fun x => x * g) ⁻¹' U, fun x => F (x * g), hU.preimage hcd.continuous, hgU,
      hF.comp hcd.contDiffOn (fun x hx => hx), ?_⟩
    intro x hx hxH
    have hx' := hFeq (x * g) hx (hinUH _ _ hxH hgH)
    simp only at hx'
    show σ x (σ g w0) = F (x * g)
    rw [← hx', hmul x g hxH hgH]
    rfl
  intro x hx
  unfold DDsp at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g, hg, rfl⟩ := hy
    exact htr g hg
  | zero => exact smooth_zero σ
  | add y z _ _ hy hz => exact smooth_add hy hz
  | smul a y _ hy => exact smooth_smul a hy

end Smooth

end Formalism.FourierDecayAlt.P.DDSmoothness
