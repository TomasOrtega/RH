import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.IsCoordA
import Development.AutomorphicArithmetic.CommutativeAlgebra.CommutantEqRangeActOnAndInjective
import Development.AutomorphicArithmetic.CommutativeAlgebra.LiftBaseChangeRealBijectiveOfLattice
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsEquivOfFinrank
open NumberField GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.PELU GlobalTheory.UPel.HT
open scoped Matrix TensorProduct Classical

/- English proof (translation)
Set `b` to `RingOfIntegers.basis F`. Set `e : ℚ ⊗[ℤ] 𝓞 F ≃ₗ[ℚ] F` to `(b.baseChange ℚ).equiv (integralBasis F) (Equiv.refl _)`. Establish `he : ∀ a : 𝓞 F, e ((1 : ℚ) ⊗ₜ[ℤ] a) = (a : F)`. Establish `key : (e.toLinearMap.restrictScalars ℤ) ∘ₗ (TensorProduct.mk ℤ ℚ (𝓞 F) (1 : ℚ)) = (Algebra.linearMap (𝓞 F) F).restrictScalars ℤ`. Use `b.ext fun i => ?_` and prove the remaining obligations.

Establish `h1 : e ((b.baseChange ℚ) i) = integralBasis F i`. Conclude with `Module.Basis.equiv_apply _ _ _ _`. Rewrite `h1` using `[Module.Basis.baseChange_apply, integralBasis_apply]`. Conclude with `h1`. Introduce `a`.

Conclude with `congrArg (fun f => f a) key`. Set `θ : ℚ ⊗[ℤ] 𝓞 F →ₐ[ℚ] F` to `Algebra.TensorProduct.lift (Algebra.ofId ℚ F) ((algebraMap (𝓞 F) F).toIntAlgHom) (fun _ _ => Commute.all _ _)`. Establish `hθ1 : ∀ a : 𝓞 F, θ ((1 : ℚ) ⊗ₜ[ℤ] a) = (a : F)`. Introduce `a`. Simplify using `[θ]`.

Establish `hθ : ∀ x, θ x = e x`. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul q a`.

Establish `h : q ⊗ₜ[ℤ] a = q • ((1 : ℚ) ⊗ₜ[ℤ] a)`. Simplify using `[TensorProduct.smul_tmul']`. Rewrite using `[h, map_smul, map_smul, he, hθ1]`. Consider the case `add x y hx hy => simp [hx, hy]`. Establish `hbij : Function.Bijective θ`.

Establish `h : (θ : ℚ ⊗[ℤ] 𝓞 F → F) = e` using `funext hθ`. Rewrite using `[h]`. Conclude with `e.bijective`. Set `E : ℚ ⊗[ℤ] 𝓞 F ≃ₐ[ℚ] F` to `AlgEquiv.ofBijective θ hbij`. Set `ρ : ℚ ⊗[ℤ] 𝓞 F →ₐ[ℚ] Module.End ℚ V` to `Algebra.TensorProduct.lift (Algebra.ofId ℚ _) φ.toIntAlgHom (fun x y => Algebra.commute_algebraMap_left x _)`.

Use `⟨ρ.comp E.symm.toAlgHom, fun c => ?_⟩` and prove the remaining obligations. Establish `h : E.symm (c : F) = (1 : ℚ) ⊗ₜ[ℤ] c`. Rewrite using `[AlgEquiv.symm_apply_eq]`. Conclude with `(hθ1 c).symm`. Use `show ρ (E.symm (c : F)) = φ c`.

Rewrite using `[h]`. Use `(Algebra.TensorProduct.lift_tmul _ _ _ _ _).trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
private theorem exists_algHom_end {F : Type} [Field F] [NumberField F] {V : Type} [AddCommGroup V] [Module ℚ V]
    (φ : 𝓞 F →+* Module.End ℚ V) :
    ∃ ψ : F →ₐ[ℚ] Module.End ℚ V, ∀ c : 𝓞 F, ψ (c : F) = φ c := by
  let b := RingOfIntegers.basis F
  let e : ℚ ⊗[ℤ] 𝓞 F ≃ₗ[ℚ] F := (b.baseChange ℚ).equiv (integralBasis F) (Equiv.refl _)
  have he : ∀ a : 𝓞 F, e ((1 : ℚ) ⊗ₜ[ℤ] a) = (a : F) := by
    have key : (e.toLinearMap.restrictScalars ℤ) ∘ₗ (TensorProduct.mk ℤ ℚ (𝓞 F) (1 : ℚ)) =
        (Algebra.linearMap (𝓞 F) F).restrictScalars ℤ := by
      refine b.ext fun i => ?_
      have h1 : e ((b.baseChange ℚ) i) = integralBasis F i := by
        exact Module.Basis.equiv_apply _ _ _ _
      rw [Module.Basis.baseChange_apply, integralBasis_apply] at h1
      exact h1
    intro a
    exact congrArg (fun f => f a) key
  let θ : ℚ ⊗[ℤ] 𝓞 F →ₐ[ℚ] F :=
    Algebra.TensorProduct.lift (Algebra.ofId ℚ F) ((algebraMap (𝓞 F) F).toIntAlgHom)
      (fun _ _ => Commute.all _ _)
  have hθ1 : ∀ a : 𝓞 F, θ ((1 : ℚ) ⊗ₜ[ℤ] a) = (a : F) := by
    intro a
    simp [θ]
  have hθ : ∀ x, θ x = e x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul q a =>
      have h : q ⊗ₜ[ℤ] a = q • ((1 : ℚ) ⊗ₜ[ℤ] a) := by
        simp [TensorProduct.smul_tmul']
      rw [h, map_smul, map_smul, he, hθ1]
    | add x y hx hy => simp [hx, hy]
  have hbij : Function.Bijective θ := by
    have h : (θ : ℚ ⊗[ℤ] 𝓞 F → F) = e := funext hθ
    rw [h]
    exact e.bijective
  let E : ℚ ⊗[ℤ] 𝓞 F ≃ₐ[ℚ] F := AlgEquiv.ofBijective θ hbij
  let ρ : ℚ ⊗[ℤ] 𝓞 F →ₐ[ℚ] Module.End ℚ V :=
    Algebra.TensorProduct.lift (Algebra.ofId ℚ _) φ.toIntAlgHom
      (fun x y => Algebra.commute_algebraMap_left x _)
  refine ⟨ρ.comp E.symm.toAlgHom, fun c => ?_⟩
  have h : E.symm (c : F) = (1 : ℚ) ⊗ₜ[ℤ] c := by
    rw [AlgEquiv.symm_apply_eq]
    exact (hθ1 c).symm
  show ρ (E.symm (c : F)) = φ c
  rw [h]
  refine (Algebra.TensorProduct.lift_tmul _ _ _ _ _).trans ?_
  simp

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.ExistsEquivOfFinrank.exists_equiv_of_finrank φ φ' h`.
-/
private theorem exists_equiv_of_finrank {F : Type} [Field F] [NumberField F] {V V' : Type}
    [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    [AddCommGroup V'] [Module ℚ V'] [FiniteDimensional ℚ V']
    (φ : 𝓞 F →+* Module.End ℚ V) (φ' : 𝓞 F →+* Module.End ℚ V')
    (h : Module.finrank ℚ V = Module.finrank ℚ V') :
    ∃ e : V ≃ₗ[ℚ] V', ∀ (c : 𝓞 F) (v : V), e (φ c v) = φ' c (e v) :=
  _root_.UpperTheory.Reformulated.B.ExistsEquivOfFinrank.exists_equiv_of_finrank φ φ' h

private def repOn {O M : Type} [Ring O] [AddCommGroup M] [Module O M] :
    O →+* Module.End ℚ (ℚ ⊗[ℤ] M) :=
  ((Module.End.baseChangeHom ℤ ℚ M).toRingHom).comp (Module.toModuleEnd ℤ M)

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem repOn_apply {O M : Type} [Ring O] [AddCommGroup M] [Module O M] (b : O) :
    (repOn b : Module.End ℚ (ℚ ⊗[ℤ] M)) = (DistribMulAction.toLinearMap ℤ M b).baseChange ℚ := rfl

/- English proof (translation)
Introduce `p _ D Y hs hr`. Use `haveI := D.freeLa`. Use `haveI := D.finLa`. Establish `hfin : Module.finrank ℚ (ℚ ⊗[ℤ] Y.La) = Module.finrank ℚ (VQ D)`. Rewrite using `[Module.finrank_baseChange, Module.finrank_baseChange, hr]`.

Take `⟨e, he⟩` from `exists_equiv_of_finrank (F := D.F) ((repOn (O := D.O) (M := Y.La)).comp (algebraMap (𝓞 D.F) D.O)) ((repOn (O := D.O) (M := D.La)).comp (algebraMap (𝓞 D.F) D.O)) hfin`. Use `⟨e, fun c u => ?_⟩` and prove the remaining obligations. Take `⟨c, rfl⟩` from `hs c`. Conclude with `he c u`.
-/
theorem UpperTheory.exists_rational_equiv_of_rank :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (Y : PLat D.O D.inv), Function.Surjective (algebraMap (𝓞 D.F) D.O) → Module.finrank ℤ Y.La = Module.finrank ℤ D.La → ∃ e : (ℚ ⊗[ℤ] Y.La) ≃ₗ[ℚ] VQ D, ∀ (c : D.O) (u : ℚ ⊗[ℤ] Y.La), e ((DistribMulAction.toLinearMap ℤ Y.La c).baseChange ℚ u) = actQ D c (e u) := by
  intro p _ D Y hs hr
  haveI := D.freeLa
  haveI := D.finLa
  have hfin : Module.finrank ℚ (ℚ ⊗[ℤ] Y.La) = Module.finrank ℚ (VQ D) := by
    rw [Module.finrank_baseChange, Module.finrank_baseChange, hr]
  obtain ⟨e, he⟩ := exists_equiv_of_finrank (F := D.F)
    ((repOn (O := D.O) (M := Y.La)).comp (algebraMap (𝓞 D.F) D.O))
    ((repOn (O := D.O) (M := D.La)).comp (algebraMap (𝓞 D.F) D.O)) hfin
  refine ⟨e, fun c u => ?_⟩
  obtain ⟨c, rfl⟩ := hs c
  exact he c u
