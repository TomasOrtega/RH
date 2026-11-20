import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.CoreDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.HeckeMultiplication
import Formalism.FormalDegreeBessel.FormalDegreeRatio.CapelliHighestWeightConjugated

open Matrix PI.UpqRep
open scoped ContDiff

noncomputable section

namespace PI.UnitaryGroupMassFormula.CapelliEig

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `k r ε lam Hs _ _ σ hσ v hv c hc`. Establish `key : ∀ g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, gᴴ * Hpk k r * g = Hpk k r → (g * c)ᴴ * Hpk k r * (g * c) = Hpk k r`. Introduce `g hg`. Establish `h2 : cᴴ * Hpk k r * c = Hpk k r` using `hc`. Rewrite using `[Matrix.conjTranspose_mul]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Hpk k r := by rw [hg, h2]`. Introduce `g₀ hg₀`. Take `⟨U, F, hUo, hgU, hF, hEq⟩` from `hv (g₀ * c) (key g₀ hg₀)`.

Set `L` to `LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ c : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ →ₗ[ℝ] _)`. Use `⟨(fun g => g * c) ⁻¹' U, fun g => F (g * c), hUo.preimage (continuous_id.matrix_mul continuous_const), hgU, ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `hF.comp (L.contDiff.contDiffOn (s := (fun g => g * c) ⁻¹' U)) (fun g hg => by show g * c ∈ U; exact hg)`. Use `h.congr fun g _ => ?_` and prove the remaining obligations. Use `show F (g * c) = F (g * c)`.

Both sides reduce to the same expression. Introduce `g _ hgH`. Establish `hgH' : gᴴ * Hpk k r * g = Hpk k r` using `hgH`. Use `show σ g (σ c v) = F (g * c)`. Rewrite using `[← hEq (g * c) (by assumption) (key g hgH')]`.

Use `show σ g (σ c v) = σ (g * c) v`. Rewrite using `[Hecke_multiplication k r ε lam Hs σ hσ g hgH c hc]`. Both sides reduce to the same expression.
-/
theorem smooth_right_action : SmRight := by
  intro k r ε lam Hs _ _ σ hσ v hv c hc
  have key : ∀ g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      gᴴ * Hpk k r * g = Hpk k r → (g * c)ᴴ * Hpk k r * (g * c) = Hpk k r := by
    intro g hg
    have h2 : cᴴ * Hpk k r * c = Hpk k r := hc
    rw [Matrix.conjTranspose_mul]
    calc cᴴ * gᴴ * Hpk k r * (g * c) = cᴴ * (gᴴ * Hpk k r * g) * c := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [hg, h2]
  intro g₀ hg₀
  obtain ⟨U, F, hUo, hgU, hF, hEq⟩ := hv (g₀ * c) (key g₀ hg₀)
  let L := LinearMap.toContinuousLinearMap
    (LinearMap.mulRight ℝ c : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ →ₗ[ℝ] _)
  refine ⟨(fun g => g * c) ⁻¹' U, fun g => F (g * c),
    hUo.preimage (continuous_id.matrix_mul continuous_const), hgU, ?_, ?_⟩
  · have h := hF.comp (L.contDiff.contDiffOn (s := (fun g => g * c) ⁻¹' U))
      (fun g hg => by show g * c ∈ U; exact hg)
    refine h.congr fun g _ => ?_
    show F (g * c) = F (g * c)
    rfl
  · intro g _ hgH
    have hgH' : gᴴ * Hpk k r * g = Hpk k r := hgH
    show σ g (σ c v) = F (g * c)
    rw [← hEq (g * c) (by assumption) (key g hgH')]
    show σ g (σ c v) = σ (g * c) v
    rw [Hecke_multiplication k r ε lam Hs σ hσ g hgH c hc]
    rfl

/- English proof (translation)
Introduce `g₀ hg₀`. Set `b` to `Module.finBasis ℂ Wq`. Set `c : Fin (Module.finrank ℂ Wq) → (Wq →L[ℂ] ℂ)` to `fun i => LinearMap.toContinuousLinearMap (b.coord i)`. Use `choose U F hUo hgU hF hEq using fun i => hQ (b i) g₀ hg₀`. Use `⟨⋂ i, U i, fun g => ∑ i, (c i).smulRight (P (F i g)), isOpen_iInter_of_finite hUo, Set.mem_iInter.2 hgU, ?_, ?_⟩` and prove the remaining obligations.

Use `ContDiffOn.sum fun i _ => ?_` and prove the remaining obligations. Establish `hL : ContDiff ℝ ∞ (fun y : Hs => (c i).smulRight (P y))` using `(((ContinuousLinearMap.smulRightL ℂ Wq Wp (c i)).comp P).restrictScalars ℝ).contDiff`. Conclude with `hL.comp_contDiffOn ((hF i).mono (Set.iInter_subset _ i))`. Introduce `g hg hgJ`. Establish `h' : ∀ i, F i g = τ g (Q (b i))` using `fun i => (hEq i g (Set.mem_iInter.1 hg i) hgJ).symm`.

Use extensionality with `w`. Simplify using `only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smulRight_apply, h', c, LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]`. Use `conv_lhs => rw [← b.sum_repr w]`. Simplify using `only [map_sum, map_smul]`.
-/
lemma coef_smoothOnGV {n : ℕ} (ε : Fin n → Bool) {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
    {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (τ : Matrix (Fin n) (Fin n) ℂ → (Hs →L[ℂ] Hs)) (P : Hs →L[ℂ] Wp) (Q : Wq →L[ℂ] Hs)
    (hQ : ∀ w, Formalism.REAL.SmoothOnGV ε (fun x => τ x (Q w))) :
    Formalism.REAL.SmoothOnGV ε (fun x => P.comp ((τ x).comp Q)) := by
  intro g₀ hg₀
  let b := Module.finBasis ℂ Wq
  let c : Fin (Module.finrank ℂ Wq) → (Wq →L[ℂ] ℂ) := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  choose U F hUo hgU hF hEq using fun i => hQ (b i) g₀ hg₀
  refine ⟨⋂ i, U i, fun g => ∑ i, (c i).smulRight (P (F i g)), isOpen_iInter_of_finite hUo,
    Set.mem_iInter.2 hgU, ?_, ?_⟩
  · refine ContDiffOn.sum fun i _ => ?_
    have hL : ContDiff ℝ ∞ (fun y : Hs => (c i).smulRight (P y)) :=
      (((ContinuousLinearMap.smulRightL ℂ Wq Wp (c i)).comp P).restrictScalars ℝ).contDiff
    exact hL.comp_contDiffOn ((hF i).mono (Set.iInter_subset _ i))
  · intro g hg hgJ
    have h' : ∀ i, F i g = τ g (Q (b i)) := fun i => (hEq i g (Set.mem_iInter.1 hg i) hgJ).symm
    ext w
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.coe_sum',
      Finset.sum_apply, ContinuousLinearMap.smulRight_apply, h', c,
      LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
    conv_lhs => rw [← b.sum_repr w]
    simp only [map_sum, map_smul]

/- English proof (translation)
Introduce `k r ε Hs _ _ σ Wp Wq _ _ _ _ _ _ P₀ hP P Q hQ`. Establish `hdet : IsUnit P₀.det` using `(Matrix.isUnit_iff_isUnit_det P₀).mp hP.1.1`. Establish `hw : ∀ w, Formalism.REAL.SmoothOnGV ε (fun x => σ (P₀⁻¹ * x * P₀) (Q w))` using `fun w => Formalism.QuantumDeterminants.ioh_smooth ε (Hpk k r) P₀ P₀⁻¹ (fun g => σ g (Q w)) (Matrix.mul_nonsing_inv P₀ hdet) hP.1.2.symm (hQ w)`. Conclude with `⟨fun w => hw w, coef_smoothOnGV ε _ P Q hw⟩`.
-/
theorem smooth_translation : SmTrans := by
  intro k r ε Hs _ _ σ Wp Wq _ _ _ _ _ _ P₀ hP P Q hQ
  have hdet : IsUnit P₀.det := (Matrix.isUnit_iff_isUnit_det P₀).mp hP.1.1
  have hw : ∀ w, Formalism.REAL.SmoothOnGV ε (fun x => σ (P₀⁻¹ * x * P₀) (Q w)) := fun w =>
    Formalism.QuantumDeterminants.ioh_smooth ε (Hpk k r) P₀ P₀⁻¹ (fun g => σ g (Q w))
      (Matrix.mul_nonsing_inv P₀ hdet) hP.1.2.symm (hQ w)
  exact ⟨fun w => hw w, coef_smoothOnGV ε _ P Q hw⟩

end PI.UnitaryGroupMassFormula.CapelliEig

end
