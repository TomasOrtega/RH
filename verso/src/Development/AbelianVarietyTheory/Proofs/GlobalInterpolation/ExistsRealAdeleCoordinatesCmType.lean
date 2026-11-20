import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.DualExponentDensity
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ActionCoordinates
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LocalDensityEuler
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeTensorUnfolding
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.InfAdeleTensorBijective

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

namespace GlobalTheory.RealAdeleCoord

/- English proof (translation)
Take `⟨hF, hE, h2, hσ⟩` from `h`. Use `haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)`. Set `c : E ≃ₐ[F] E` to `AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)`. Establish `hc' : ∀ (τ : E →+* ℂ) x, τ (c x) = starRingEnd ℂ (τ x)` using `hσ`. Establish `hnr : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate φ ≠ φ` using `fun φ hφ => IsTotallyComplex.complexEmbedding_not_isReal φ (ComplexEmbedding.isReal_iff.2 hφ)`.

Establish `hc : c ≠ 1`. Introduce `h1`. Take `⟨φ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Use `hnr φ (RingHom.ext fun x => ?_)` and prove the remaining obligations. Rewrite using `[ComplexEmbedding.conjugate_coe_eq, ← hc', h1]`.

Both sides reduce to the same expression. Take `⟨δ, h0, hcδ, hs⟩` from `GlobalTheory.InfAdeleCM.exists_delta c h2 hc hc'`. Prove the components needed by the constructor for the conclusion. Introduce `i j hij`. Apply `hτ.1` to reduce the goal to its premises.

Break down `GlobalTheory.InfAdeleCM.eq_or_conj c hc' h0 hcδ hs _ _ (GlobalTheory.InfAdeleCM.mk_eq_iff hij) with e | e` into its components or cases. Simplify using `only [e]`. Simplify using `only [e, InfinitePlace.mk_conjugate_eq]`. Introduce `w`. Take `⟨i, hi⟩` from `hτ.2 (InfinitePlace.mk (ComplexEmbedding.lift E w.embedding))`.

Use `⟨i, ?_⟩` and prove the remaining obligations. Use `congrArg (fun v : InfinitePlace E => v.comap (algebraMap F E)) hi` as an intermediate fact. Simplify using `only [InfinitePlace.comap_mk, ComplexEmbedding.lift_comp_algebraMap, InfinitePlace.mk_embedding] at this`. Conclude with `this`.
-/
theorem bijective_place {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) {T : Type} (τ : T → (E →+* ℂ))
    (hτ : Function.Bijective fun ρ => InfinitePlace.mk (τ ρ)) :
    Function.Bijective fun ρ => InfinitePlace.mk ((τ ρ).comp (algebraMap F E)) := by
  obtain ⟨hF, hE, h2, hσ⟩ := h
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let c : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  have hc' : ∀ (τ : E →+* ℂ) x, τ (c x) = starRingEnd ℂ (τ x) := hσ
  have hnr : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate φ ≠ φ := fun φ hφ =>
    IsTotallyComplex.complexEmbedding_not_isReal φ (ComplexEmbedding.isReal_iff.2 hφ)
  have hc : c ≠ 1 := by
    intro h1
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    refine hnr φ (RingHom.ext fun x => ?_)
    rw [ComplexEmbedding.conjugate_coe_eq, ← hc', h1]
    rfl
  obtain ⟨δ, h0, hcδ, hs⟩ := GlobalTheory.InfAdeleCM.exists_delta c h2 hc hc'
  constructor
  · intro i j hij
    apply hτ.1
    rcases GlobalTheory.InfAdeleCM.eq_or_conj c hc' h0 hcδ hs _ _ (GlobalTheory.InfAdeleCM.mk_eq_iff hij) with e | e
    · simp only [e]
    · simp only [e, InfinitePlace.mk_conjugate_eq]
  · intro w
    obtain ⟨i, hi⟩ := hτ.2 (InfinitePlace.mk (ComplexEmbedding.lift E w.embedding))
    refine ⟨i, ?_⟩
    have := congrArg (fun v : InfinitePlace E => v.comap (algebraMap F E)) hi
    simp only [InfinitePlace.comap_mk, ComplexEmbedding.lift_comp_algebraMap, InfinitePlace.mk_embedding] at this
    exact this

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ h T _ τ θ hτ hθ`. Use `haveI hF := h.1`. Set `u : T ≃ InfinitePlace F` to `Equiv.ofBijective _ (bijective_place σ h τ hτ)`. Set `s : ∀ w : InfinitePlace F, w.Completion ≃+* ℝ` to `fun w => InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)`. Establish `hs : ∀ w, Continuous (s w)` using `fun w => (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous`.

Establish `hs' : ∀ w, Continuous (s w).symm` using `fun w => (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm.continuous`. Establish `hsc : ∀ w x, ((s w x : ℝ) : ℂ) = InfinitePlace.Completion.extensionEmbedding w x` using `fun w x => InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w) x`. Set `r : Ainf F ≃+* (T → ℝ)` to `{ toFun := fun a ρ => s (u ρ) (a (u ρ)) invFun := fun y w => (s w).symm (y (u.symm w)) left_inv := fun a => funext fun w => by`. Take `⟨ρ, rfl⟩` from `u.surjective w`. Use `show (s (u ρ)).symm (s (u (u.symm (u ρ))) (a (u (u.symm (u ρ))))) = _`.

Rewrite using `[u.symm_apply_apply, RingEquiv.symm_apply_apply]`. Use `right_inv := fun y => funext fun ρ => by show s (u ρ) ((s (u ρ)).symm (y (u.symm (u ρ)))) = _`. Rewrite using `[RingEquiv.apply_symm_apply, u.symm_apply_apply]`. Use the proof step `map_mul' := fun a b => funext fun ρ => map_mul (s (u ρ)) (a (u ρ)) (b (u ρ))`. Use the proof step `map_add' := fun a b => funext fun ρ => map_add (s (u ρ)) (a (u ρ)) (b (u ρ)) }`.

Establish `hr : ∀ a ρ, r a ρ = s (u ρ) (a (u ρ))` using `fun _ _ => rfl`. Use `⟨r, continuous_pi fun ρ => (hs _).comp (continuous_apply (u ρ)), continuous_pi fun w => (hs' w).comp (continuous_apply (u.symm w)), fun a ρ => ?_, fun a => ?_, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.InfAdeleCM.hom_tmul _ _ (hθ ρ).1 (hθ ρ).2, map_one, mul_one, hr, hsc]`. Both sides reduce to the same expression. Unfold `LocalAdditiveCharacterDual.stdInf`.

Rewrite using `[← Complex.exp_sum, ← u.sum_comp]`. Use `congr 1`. Simplify using `only [← hsc, ← hr, Complex.ofReal_re]`. Use `push_cast`. Rewrite using `[← Finset.mul_sum]`.

Expand and normalize the polynomial expressions, which then agree. Prove the components needed by the constructor for the conclusion. Introduce `ha ρ`. Rewrite using `[hr]`. Conclude with `(map_ne_zero _).2 (ha _)`.

Introduce `ha w`. Take `⟨ρ, rfl⟩` from `u.surjective w`. Conclude with `(map_ne_zero (s (u ρ))).1 (ha ρ)`.
-/
theorem exists_realCoord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (T : Type) [Fintype T] (τ : T → (E →+* ℂ)) (θ : T → (Ainf F ⊗[F] E →+* ℂ)), (Function.Bijective fun ρ => InfinitePlace.mk (τ ρ)) → (∀ ρ, IsInfEmb (τ ρ) (θ ρ)) → ∃ r : Ainf F ≃+* (T → ℝ), Continuous r ∧ Continuous r.symm ∧ (∀ a ρ, ((r a ρ : ℝ) : ℂ) = θ ρ (a ⊗ₜ[F] (1 : E))) ∧ (∀ a, LocalAdditiveCharacterDual.stdInf F a = Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℝ) * ∑ ρ, r a ρ : ℝ) : ℂ))) ∧ ∀ a, (∀ w, a w ≠ 0) ↔ ∀ ρ, r a ρ ≠ 0 := by
  intro F E _ _ _ _ _ σ h T _ τ θ hτ hθ
  haveI hF := h.1
  let u : T ≃ InfinitePlace F := Equiv.ofBijective _ (bijective_place σ h τ hτ)
  let s : ∀ w : InfinitePlace F, w.Completion ≃+* ℝ := fun w =>
    InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)
  have hs : ∀ w, Continuous (s w) := fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous
  have hs' : ∀ w, Continuous (s w).symm := fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm.continuous
  have hsc : ∀ w x, ((s w x : ℝ) : ℂ) = InfinitePlace.Completion.extensionEmbedding w x := fun w x =>
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w) x
  let r : Ainf F ≃+* (T → ℝ) :=
    { toFun := fun a ρ => s (u ρ) (a (u ρ))
      invFun := fun y w => (s w).symm (y (u.symm w))
      left_inv := fun a => funext fun w => by
        obtain ⟨ρ, rfl⟩ := u.surjective w
        show (s (u ρ)).symm (s (u (u.symm (u ρ))) (a (u (u.symm (u ρ))))) = _
        rw [u.symm_apply_apply, RingEquiv.symm_apply_apply]
      right_inv := fun y => funext fun ρ => by
        show s (u ρ) ((s (u ρ)).symm (y (u.symm (u ρ)))) = _
        rw [RingEquiv.apply_symm_apply, u.symm_apply_apply]
      map_mul' := fun a b => funext fun ρ => map_mul (s (u ρ)) (a (u ρ)) (b (u ρ))
      map_add' := fun a b => funext fun ρ => map_add (s (u ρ)) (a (u ρ)) (b (u ρ)) }
  have hr : ∀ a ρ, r a ρ = s (u ρ) (a (u ρ)) := fun _ _ => rfl
  refine ⟨r, continuous_pi fun ρ => (hs _).comp (continuous_apply (u ρ)),
    continuous_pi fun w => (hs' w).comp (continuous_apply (u.symm w)), fun a ρ => ?_, fun a => ?_, fun a => ?_⟩
  · rw [GlobalTheory.InfAdeleCM.hom_tmul _ _ (hθ ρ).1 (hθ ρ).2, map_one, mul_one, hr, hsc]
    rfl
  · unfold LocalAdditiveCharacterDual.stdInf
    rw [← Complex.exp_sum, ← u.sum_comp]
    congr 1
    simp only [← hsc, ← hr, Complex.ofReal_re]
    push_cast
    rw [← Finset.mul_sum]
    ring
  · constructor
    · intro ha ρ
      rw [hr]
      exact (map_ne_zero _).2 (ha _)
    · intro ha w
      obtain ⟨ρ, rfl⟩ := u.surjective w
      exact (map_ne_zero (s (u ρ))).1 (ha ρ)

end GlobalTheory.RealAdeleCoord
