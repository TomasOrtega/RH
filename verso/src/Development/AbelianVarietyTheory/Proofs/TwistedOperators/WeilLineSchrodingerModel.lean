import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetaplecticTransfer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionUnitaryCompactStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchActOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanWeilOperatorsLinearOneMulStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanWeilOperatorIntertwinesSchroedingerStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryArchimedeanCoordinateActionLinearMulStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryArchimedeanCoordinateActionSymplecticStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousOneParameterUnitaryCoordinateActionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousOneParameterArchimedeanWeilOperatorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchWeilOperatorUnitaryWLintegralNormEqStatement

noncomputable section

open scoped Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord
open scoped Classical
open MeasureTheory

namespace GlobalTheory.ArchLine

open scoped SchwartzMap

/- English proof (translation)
Introduce `hP F E _ _ _ _ _ σ n d X W M ψ χX χW om hCM hψ hW γ hγ`. Establish `hex : ∀ h ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, h)) ⇑f ⇑f₁` using `fun h hh f => GlobalTheory.T.weil_action_unitary_compact hP M ψ χX χW om hCM hψ hW h hh f`. Take `⟨hadd, hsmul, hone, hmul⟩` from `GlobalTheory.T.archimedean_weilOperators_linear_one_mul M ψ χX χW om hW hex`. Take `⟨aadd, asmul, amul⟩` from `GlobalTheory.T.unitary_archimedean_coordinate_action_linear_mul M`. Establish `hγU : ∀ t : ℝ, γ (Multiplicative.ofAdd t) ∈ UAt σ W (evI F)` using `fun t => hγ.2 _`.

Establish `hγ0 : γ (Multiplicative.ofAdd 0) = 1` using `by rw [ofAdd_zero, map_one]`. Establish `hγadd : ∀ s t : ℝ, γ (Multiplicative.ofAdd (s + t)) = γ (Multiplicative.ofAdd s) * γ (Multiplicative.ofAdd t)` using `fun s t => by rw [ofAdd_add, map_mul]`. Take `⟨N, hN⟩ : ∃ N, Module.finrank ℝ (Fin n × Fin d → mixedEmbedding.mixedSpace F) = N` from `⟨_, rfl⟩`. Take `⟨C, φ, hφ, hC⟩` from `pairingCoords (Fin n × Fin d → mixedEmbedding.mixedSpace F) (trP F (Fin n × Fin d)) (isPairing_trP _) N hN`. Set `S : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)` to `fun t => { toFun := archOp om (γ (Multiplicative.ofAdd t)) map_add' := hadd _ (hγU t) map_smul' := hsmul _ (hγU t) }`.

Set `A : ℝ → ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))` to `fun t => { toFun := archAct M (γ (Multiplicative.ofAdd t)) map_add' := aadd _ map_smul' := asmul _ }`. Set `ψt : ℝ → (Fin N ⊕ Fin N → ℝ) →ₗ[ℝ] (Fin N ⊕ Fin N → ℝ)` to `fun t => φ.toLinearMap ∘ₗ A t ∘ₗ φ.symm.toLinearMap`. Establish `hψt : ∀ t w, ψt t w = φ (archAct M (γ (Multiplicative.ofAdd t)) (φ.symm w))` using `fun t w => rfl`. Set `g : ℝ → Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ` to `fun t => LinearMap.toMatrix' (ψt t)`. Establish `hg : ∀ t w, g t *ᵥ w = ψt t w` using `fun t w => LinearMap.toMatrix'_mulVec _ _`.

Set `P1 : SInf F (Fin n × Fin d) →L[ℂ] GlobalTheory.RealWeil.Sch (Fin N)` to `SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C.symm`. Set `P2 : GlobalTheory.RealWeil.Sch (Fin N) →L[ℂ] SInf F (Fin n × Fin d)` to `SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C`. Set `eΦ : SInf F (Fin n × Fin d) ≃L[ℂ] GlobalTheory.RealWeil.Sch (Fin N)` to `ContinuousLinearEquiv.equivOfInverse P1 P2 (fun f => by ext x; simp [P1, P2]) (fun h => by ext x; simp [P1, P2])`. Establish `hΦ : ∀ f x, eΦ f x = f (C.symm x)` using `fun f x => rfl`. Establish `hΦs : ∀ h x, eΦ.symm h x = h (C x)` using `fun h x => rfl`.

Set `T : ℝ → GlobalTheory.RealWeil.Sch (Fin N) →ₗ[ℂ] GlobalTheory.RealWeil.Sch (Fin N)` to `fun t => eΦ.toLinearMap ∘ₗ S t ∘ₗ eΦ.symm.toLinearMap`. Establish `hT : ∀ t h x, T t h x = archOp om (γ (Multiplicative.ofAdd t)) (eΦ.symm h) (C.symm x)` using `fun t h x => rfl`. Use `⟨Fin N, inferInstance, inferInstance, eΦ, g, T, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Simplify using `only [g, LinearMap.toMatrix'_apply]`.

Conclude with `(continuous_apply i).comp ((LinearMap.continuous_of_finiteDimensional φ.toLinearMap).comp (GlobalTheory.T.continuous_oneParameter_unitary_coordinate_action M γ hγ _))`. Establish `e : ψt 0 = LinearMap.id` using `LinearMap.ext fun w => by rw [hψt, hγ0, archAct_one]; simp`. Simplify using `only [g, e, LinearMap.toMatrix'_id]`. Introduce `s t`. Establish `e : ψt (s + t) = ψt s ∘ₗ ψt t` using `LinearMap.ext fun w => by`.

Rewrite using `[hψt, LinearMap.comp_apply, hψt, hψt, hγadd, amul, LinearEquiv.symm_apply_apply]`. Simplify using `only [g, e, LinearMap.toMatrix'_comp]`. Introduce `t`. Establish `hsym : ∀ w w', GlobalTheory.RealWeil.sympl (ψt t w) (ψt t w') = GlobalTheory.RealWeil.sympl w w'` using `fun w w' => by`. Rewrite using `[hψt, hψt, hφ, GlobalTheory.T.unitary_archimedean_coordinate_action_symplectic, ← hφ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]`.

Take `⟨Mx, hMx⟩` from `symplMatrix (Fin N) (ψt t) hsym`. Establish `e : g t = Mx` using `Matrix.toLin'.injective (LinearMap.ext fun w => by`. Rewrite using `[Matrix.toLin'_apply, Matrix.toLin'_apply, hg, hMx])`. Rewrite using `[e]`. Conclude with `Mx.2`.

Use `LinearMap.ext fun h => ?_` and prove the remaining obligations. Use extensionality with `x`. Rewrite using `[hT, hγ0, hone, hΦs]`. Simplify using the standard rewrite rules. Introduce `s t`.

Use `LinearMap.ext fun h => ?_` and prove the remaining obligations. Use extensionality with `x`. Use `show archOp om (γ (Multiplicative.ofAdd (s + t))) (eΦ.symm h) (C.symm x) = archOp om (γ (Multiplicative.ofAdd s)) (eΦ.symm (T t h)) (C.symm x)`. Rewrite using `[hγadd, hmul _ (hγU s) _ (hγU t)]`. Use `congr 2`.

Conclude with `(eΦ.symm_apply_apply (S t (eΦ.symm h))).symm`. Introduce `t w h h₁ hh₁`. Establish `hf : ⇑(eΦ.symm h₁) = schrF (trP F (Fin n × Fin d)) (φ.symm w) ⇑(eΦ.symm h)`. Establish `e1 : ⇑(eΦ.symm h) = ⇑h ∘ ⇑C` using `funext (hΦs h)`. Rewrite using `[e1, hC, LinearEquiv.apply_symm_apply]`.

Use function extensionality and compare the values at `y`. Rewrite using `[hΦs, hh₁]`. Both sides reduce to the same expression. Establish `key` using `GlobalTheory.T.archimedean_weilOperator_intertwines_schroedinger M ψ χX χW om hψ hW hex _ (hγU t) (φ.symm w) _ _ hf`. Establish `e2 : ⇑(archOp om (γ (Multiplicative.ofAdd t)) (eΦ.symm h)) = ⇑(T t h) ∘ ⇑C`.

Use function extensionality and compare the values at `y`. Rewrite using `[Function.comp_apply, hT, ContinuousLinearEquiv.symm_apply_apply]`. Use function extensionality and compare the values at `x`. Rewrite using `[hT, key, e2, hC, hg, hψt]`. Simplify using the standard rewrite rules.

Introduce `t h`. Establish `e` using `GlobalTheory.T.archWeilOperator_unitaryW_lintegral_norm_eq M ψ χX χW om hW hex _ (hγU t) N C (eΦ.symm h)`. Use `Eq.trans ?_ (e.trans ?_)` and prove the remaining obligations. Both sides reduce to the same expression. Simplify using `only [hΦs, ContinuousLinearEquiv.apply_symm_apply]`.

Introduce `h x`. Conclude with `GlobalTheory.T.continuous_oneParameter_archimedean_weilOperator M ψ χX χW om hW hex γ hγ (eΦ.symm h) (C.symm x)`. Introduce `t f`. Establish `e : eΦ.symm (T t (eΦ f)) = archOp om (γ (Multiplicative.ofAdd t)) f`. Use extensionality with `y`.

Rewrite using `[hΦs, hT]`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `acts_archOp om _ f (hex _ (hγU t) f)`.
-/
theorem realLine : GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (χX χW : Chr F E) (om : Rep σ X W), IsCMExt F E σ → IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ Lines σ W, ∃ (l : Type) (_ : Fintype l) (_ : DecidableEq l)
      (Φ : SInf F (Fin n × Fin d) ≃L[ℂ] GlobalTheory.RealWeil.Sch l) (g : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ)
      (T : ℝ → GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l),
      Continuous g ∧ g 0 = 1 ∧ (∀ s t, g (s + t) = g s * g t) ∧ (∀ t, g t ∈ Matrix.symplecticGroup l ℝ) ∧
      T 0 = LinearMap.id ∧ (∀ s t, T (s + t) = T s ∘ₗ T t) ∧
      (∀ (t : ℝ) (w : l ⊕ l → ℝ) (h h₁ : GlobalTheory.RealWeil.Sch l), ⇑h₁ = GlobalTheory.RealWeil.rhoFun w ⇑h →
        ⇑(T t h₁) = GlobalTheory.RealWeil.rhoFun (g t *ᵥ w) ⇑(T t h)) ∧
      (∀ (t : ℝ) (h : GlobalTheory.RealWeil.Sch l), ∫⁻ x, ‖T t h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2) ∧
      (∀ (h : GlobalTheory.RealWeil.Sch l) (x : EuclideanSpace ℝ l), Continuous fun t => T t h x) ∧
      ∀ (t : ℝ) (f : SInf F (Fin n × Fin d)),
        Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑(Φ.symm (T t (Φ f))) := by
  intro hP F E _ _ _ _ _ σ n d X W M ψ χX χW om hCM hψ hW γ hγ
  have hex : ∀ h ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, h)) ⇑f ⇑f₁ := fun h hh f => GlobalTheory.T.weil_action_unitary_compact hP M ψ χX χW om hCM hψ hW h hh f
  obtain ⟨hadd, hsmul, hone, hmul⟩ := GlobalTheory.T.archimedean_weilOperators_linear_one_mul M ψ χX χW om hW hex
  obtain ⟨aadd, asmul, amul⟩ := GlobalTheory.T.unitary_archimedean_coordinate_action_linear_mul M
  have hγU : ∀ t : ℝ, γ (Multiplicative.ofAdd t) ∈ UAt σ W (evI F) := fun t => hγ.2 _
  have hγ0 : γ (Multiplicative.ofAdd 0) = 1 := by rw [ofAdd_zero, map_one]
  have hγadd : ∀ s t : ℝ, γ (Multiplicative.ofAdd (s + t)) = γ (Multiplicative.ofAdd s) * γ (Multiplicative.ofAdd t) :=
    fun s t => by rw [ofAdd_add, map_mul]
  obtain ⟨N, hN⟩ : ∃ N, Module.finrank ℝ (Fin n × Fin d → mixedEmbedding.mixedSpace F) = N := ⟨_, rfl⟩
  obtain ⟨C, φ, hφ, hC⟩ := pairingCoords (Fin n × Fin d → mixedEmbedding.mixedSpace F) (trP F (Fin n × Fin d))
    (isPairing_trP _) N hN
  let S : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d) := fun t =>
    { toFun := archOp om (γ (Multiplicative.ofAdd t))
      map_add' := hadd _ (hγU t)
      map_smul' := hsmul _ (hγU t) }
  let A : ℝ → ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
      ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) := fun t =>
    { toFun := archAct M (γ (Multiplicative.ofAdd t))
      map_add' := aadd _
      map_smul' := asmul _ }
  let ψt : ℝ → (Fin N ⊕ Fin N → ℝ) →ₗ[ℝ] (Fin N ⊕ Fin N → ℝ) := fun t =>
    φ.toLinearMap ∘ₗ A t ∘ₗ φ.symm.toLinearMap
  have hψt : ∀ t w, ψt t w = φ (archAct M (γ (Multiplicative.ofAdd t)) (φ.symm w)) := fun t w => rfl
  let g : ℝ → Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ := fun t => LinearMap.toMatrix' (ψt t)
  have hg : ∀ t w, g t *ᵥ w = ψt t w := fun t w => LinearMap.toMatrix'_mulVec _ _
  let P1 : SInf F (Fin n × Fin d) →L[ℂ] GlobalTheory.RealWeil.Sch (Fin N) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C.symm
  let P2 : GlobalTheory.RealWeil.Sch (Fin N) →L[ℂ] SInf F (Fin n × Fin d) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C
  let eΦ : SInf F (Fin n × Fin d) ≃L[ℂ] GlobalTheory.RealWeil.Sch (Fin N) := ContinuousLinearEquiv.equivOfInverse P1 P2
    (fun f => by ext x; simp [P1, P2]) (fun h => by ext x; simp [P1, P2])
  have hΦ : ∀ f x, eΦ f x = f (C.symm x) := fun f x => rfl
  have hΦs : ∀ h x, eΦ.symm h x = h (C x) := fun h x => rfl
  let T : ℝ → GlobalTheory.RealWeil.Sch (Fin N) →ₗ[ℂ] GlobalTheory.RealWeil.Sch (Fin N) := fun t =>
    eΦ.toLinearMap ∘ₗ S t ∘ₗ eΦ.symm.toLinearMap
  have hT : ∀ t h x, T t h x = archOp om (γ (Multiplicative.ofAdd t)) (eΦ.symm h) (C.symm x) := fun t h x => rfl
  refine ⟨Fin N, inferInstance, inferInstance, eΦ, g, T, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [g, LinearMap.toMatrix'_apply]
    exact (continuous_apply i).comp ((LinearMap.continuous_of_finiteDimensional φ.toLinearMap).comp
      (GlobalTheory.T.continuous_oneParameter_unitary_coordinate_action M γ hγ _))
  · have e : ψt 0 = LinearMap.id := LinearMap.ext fun w => by rw [hψt, hγ0, archAct_one]; simp
    simp only [g, e, LinearMap.toMatrix'_id]
  · intro s t
    have e : ψt (s + t) = ψt s ∘ₗ ψt t := LinearMap.ext fun w => by
      rw [hψt, LinearMap.comp_apply, hψt, hψt, hγadd, amul, LinearEquiv.symm_apply_apply]
    simp only [g, e, LinearMap.toMatrix'_comp]
  · intro t
    have hsym : ∀ w w', GlobalTheory.RealWeil.sympl (ψt t w) (ψt t w') = GlobalTheory.RealWeil.sympl w w' := fun w w' => by
      rw [hψt, hψt, hφ, GlobalTheory.T.unitary_archimedean_coordinate_action_symplectic, ← hφ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    obtain ⟨Mx, hMx⟩ := symplMatrix (Fin N) (ψt t) hsym
    have e : g t = Mx := Matrix.toLin'.injective (LinearMap.ext fun w => by
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hg, hMx])
    rw [e]; exact Mx.2
  · refine LinearMap.ext fun h => ?_
    ext x
    rw [hT, hγ0, hone, hΦs]
    simp
  · intro s t
    refine LinearMap.ext fun h => ?_
    ext x
    show archOp om (γ (Multiplicative.ofAdd (s + t))) (eΦ.symm h) (C.symm x) =
      archOp om (γ (Multiplicative.ofAdd s)) (eΦ.symm (T t h)) (C.symm x)
    rw [hγadd, hmul _ (hγU s) _ (hγU t)]
    congr 2
    exact (eΦ.symm_apply_apply (S t (eΦ.symm h))).symm
  · intro t w h h₁ hh₁
    have hf : ⇑(eΦ.symm h₁) = schrF (trP F (Fin n × Fin d)) (φ.symm w) ⇑(eΦ.symm h) := by
      have e1 : ⇑(eΦ.symm h) = ⇑h ∘ ⇑C := funext (hΦs h)
      rw [e1, hC, LinearEquiv.apply_symm_apply]
      funext y; rw [hΦs, hh₁]; rfl
    have key := GlobalTheory.T.archimedean_weilOperator_intertwines_schroedinger M ψ χX χW om hψ hW hex _ (hγU t) (φ.symm w) _ _ hf
    have e2 : ⇑(archOp om (γ (Multiplicative.ofAdd t)) (eΦ.symm h)) = ⇑(T t h) ∘ ⇑C := by
      funext y; rw [Function.comp_apply, hT, ContinuousLinearEquiv.symm_apply_apply]
    funext x
    rw [hT, key, e2, hC, hg, hψt]
    simp
  · intro t h
    have e := GlobalTheory.T.archWeilOperator_unitaryW_lintegral_norm_eq M ψ χX χW om hW hex _ (hγU t) N C (eΦ.symm h)
    refine Eq.trans ?_ (e.trans ?_)
    · rfl
    · simp only [hΦs, ContinuousLinearEquiv.apply_symm_apply]
  · intro h x
    exact GlobalTheory.T.continuous_oneParameter_archimedean_weilOperator M ψ χX χW om hW hex γ hγ (eΦ.symm h) (C.symm x)
  · intro t f
    have e : eΦ.symm (T t (eΦ f)) = archOp om (γ (Multiplicative.ofAdd t)) f := by
      ext y; rw [hΦs, hT]; simp
    rw [e]
    exact acts_archOp om _ f (hex _ (hγU t) f)

end GlobalTheory.ArchLine
