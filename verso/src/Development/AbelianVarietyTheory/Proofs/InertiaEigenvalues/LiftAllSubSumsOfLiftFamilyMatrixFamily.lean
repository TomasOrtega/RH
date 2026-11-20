import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSummandTw

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual

noncomputable section

namespace GlobalTheory.Pass.LocDual

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp : Type} [Field Qp]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]

/- English proof (translation)
Take `⟨a, b, p, q, hp, hq, hinj⟩` from `hW`. Take `⟨a₁, x₁, p₁, hp₁, hinj₁⟩` from `hA`. Take `⟨a₂, x₂, p₂, hp₂, hinj₂⟩` from `hA'`. Set `e : Fin (a * a₁ + b * a₂) ≃ (Fin a × Fin a₁) ⊕ (Fin b × Fin a₂)` to `finSumFinEquiv.symm.trans (Equiv.sumCongr finProdFinEquiv.symm finProdFinEquiv.symm)`. Set `X : (Fin a × Fin a₁) ⊕ (Fin b × Fin a₂) → ι` to `Sum.elim (fun ij => x₁ ij.2) (fun ij => x₂ ij.2)`.

Set `P : (Fin a × Fin a₁) ⊕ (Fin b × Fin a₂) → W.V →ₗ[LL] (Fin k → LL)` to `Sum.elim (fun ij => (p₁ ij.2).comp (p ij.1)) (fun ij => (p₂ ij.2).comp (q ij.1))`. Use `⟨a * a₁ + b * a₂, X ∘ e, P ∘ e, ?_, ?_⟩` and prove the remaining obligations. Introduce `j g v`. Simplify using `only [Function.comp]`. Generalize the expression as in `e j = s`.

Break down `s with ⟨i, j'⟩ | ⟨i, j'⟩` into its components or cases. Simplify using `only [P, X, Sum.elim_inl, LinearMap.comp_apply, hp, hp₁]`. Simplify using `only [P, X, Sum.elim_inr, LinearMap.comp_apply, hq, hp₂]`. Introduce `v hv`. Apply `hinj v` to reduce the goal to its premises.

Introduce `i`. Apply `hinj₁` to reduce the goal to its premises. Introduce `j'`. Establish `h` using `hv (e.symm (Sum.inl (i, j')))`. Simplify `h` using `[P]`.

Introduce `i`. Apply `hinj₂` to reduce the goal to its premises. Introduce `j'`. Establish `h` using `hv (e.symm (Sum.inr (i, j')))`. Simplify `h` using `[P]`.
-/
theorem isSubFam_of_isSubSumOf {ι : Type} {k : ℕ} (Ms : ι → (G →* Matrix (Fin k) (Fin k) LL))
    (W A A' : GRep G Qp LL O) (hW : BlochKatoDuality.IsSubSumOf W.ρ A.ρ A'.ρ) (hA : IsSubFam Ms A)
    (hA' : IsSubFam Ms A') : IsSubFam Ms W := by
  obtain ⟨a, b, p, q, hp, hq, hinj⟩ := hW
  obtain ⟨a₁, x₁, p₁, hp₁, hinj₁⟩ := hA
  obtain ⟨a₂, x₂, p₂, hp₂, hinj₂⟩ := hA'
  let e : Fin (a * a₁ + b * a₂) ≃ (Fin a × Fin a₁) ⊕ (Fin b × Fin a₂) :=
    finSumFinEquiv.symm.trans (Equiv.sumCongr finProdFinEquiv.symm finProdFinEquiv.symm)
  let X : (Fin a × Fin a₁) ⊕ (Fin b × Fin a₂) → ι :=
    Sum.elim (fun ij => x₁ ij.2) (fun ij => x₂ ij.2)
  let P : (Fin a × Fin a₁) ⊕ (Fin b × Fin a₂) → W.V →ₗ[LL] (Fin k → LL) :=
    Sum.elim (fun ij => (p₁ ij.2).comp (p ij.1)) (fun ij => (p₂ ij.2).comp (q ij.1))
  refine ⟨a * a₁ + b * a₂, X ∘ e, P ∘ e, ?_, ?_⟩
  · intro j g v
    simp only [Function.comp]
    generalize e j = s
    rcases s with ⟨i, j'⟩ | ⟨i, j'⟩
    · simp only [P, X, Sum.elim_inl, LinearMap.comp_apply, hp, hp₁]
    · simp only [P, X, Sum.elim_inr, LinearMap.comp_apply, hq, hp₂]
  · intro v hv
    apply hinj v
    · intro i
      apply hinj₁
      intro j'
      have h := hv (e.symm (Sum.inl (i, j')))
      simpa [P] using h
    · intro i
      apply hinj₂
      intro j'
      have h := hv (e.symm (Sum.inr (i, j')))
      simpa [P] using h

end Gen

section OnePD

/- English proof (translation)
Introduce `G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ ι k Ms e A A' hL hA hA'`. Introduce `W₁ W₂ h₁ h₂ L₁ L₂ F hF`. Conclude with `hL W₁ W₂ (isSubFam_of_isSubSumOf Ms W₁ A A' h₁ hA hA') (isSubFam_of_isSubSumOf Ms W₂ A A' h₂ hA hA') L₁ L₂ F hF`.
-/
theorem liftAll_of_liftFam :
    ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {ι : Type} {k : ℕ} (Ms : ι → (G →* Matrix (Fin k) (Fin k) LL)) (e : ℕ)
    (A A' : GRep G Qp LL O), LiftFam (O := O) PD Ms e → IsSubFam Ms A → IsSubFam Ms A' → BlochKatoDuality.LiftAll PD A A' e := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ ι k Ms e A A' hL hA hA'
  intro W₁ W₂ h₁ h₂ L₁ L₂ F hF
  exact hL W₁ W₂ (isSubFam_of_isSubSumOf Ms W₁ A A' h₁ hA hA')
    (isSubFam_of_isSubSumOf Ms W₂ A A' h₂ hA hA') L₁ L₂ F hF

end OnePD

end GlobalTheory.Pass.LocDual

end
