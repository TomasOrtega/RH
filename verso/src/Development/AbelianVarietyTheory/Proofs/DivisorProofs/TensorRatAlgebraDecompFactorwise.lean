import Mathlib
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `S F B _ _ _ _ _ _ _ _ _`. Use `haveI hEt : Algebra.Etale ℚ F := by haveI : Algebra.IsSeparable ℚ F := inferInstance haveI : Algebra.FormallyEtale ℚ F := Algebra.FormallyEtale.of_isSeparable ℚ F haveI : Algebra.FinitePresentation ℚ F := Algebra.FinitePresentation.of_finiteType.mp inferInstance`. Apply the tactic sequence `constructor <;> infer_instance`. Use `haveI : Algebra.Etale S (S ⊗[ℚ] F) := Algebra.Etale.baseChange ℚ F S`. Take `⟨I, hI, L, hL, hAL, e, -⟩` from `(Algebra.Etale.iff_exists_algEquiv_prod S (S ⊗[ℚ] F)).mp this`.

Use `letI : Fintype I := Fintype.ofFinite I`. Set `ψ : S ⊗[ℚ] F ≃+* ((i : I) → L i)` to `e.toRingEquiv`. Use `letI instF : ∀ i, Algebra F (L i) := fun i => ((Pi.evalRingHom L i).comp (ψ.toRingHom.comp (Algebra.TensorProduct.includeRight : F →ₐ[ℚ] S ⊗[ℚ] F).toRingHom)).toAlgebra`. Establish `hchar : ∀ i, CharZero (L i)` using `fun i => charZero_of_injective_algebraMap (R := S) (algebraMap S (L i)).injective`. Set `φ : F ⊗[ℚ] S ≃ₐ[F] ((i : I) → L i)` to `AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm ℚ F S).toRingEquiv.trans ψ) (fun x => by`.

Use function extensionality and compare the values at `i`. Use the proof step `rfl)`. Set `c : B ⊗[ℚ] S ≃ₐ[F] B ⊗[F] (F ⊗[ℚ] S)` to `AlgEquiv.ofLinearEquiv (TensorProduct.AlgebraTensorModule.cancelBaseChange ℚ F F B S).symm (by simp [Algebra.TensorProduct.one_def]) (LinearMap.map_mul_of_map_mul_tmul (fun _ _ _ _ ↦ by simp))`. Set `Φ : S ⊗[ℚ] B ≃+* ((i : I) → L i ⊗[F] B)` to `(Algebra.TensorProduct.comm ℚ S B).toRingEquiv.trans <| c.toRingEquiv.trans <| (Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[F] B) φ).toRingEquiv.trans <| (Algebra.TensorProduct.piRight F F B L).toRingEquiv.trans (AlgEquiv.piCongrRight fun i => Algebra.TensorProduct.comm F B …`. Establish `hΦ : ∀ (s : S) (b : B), Φ (s ⊗ₜ b) = fun i => ψ (s ⊗ₜ 1) i ⊗ₜ[F] b`.

Introduce `s b`. Establish `hc : c (b ⊗ₜ s) = b ⊗ₜ ((1 : F) ⊗ₜ s)` using `TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul ℚ F F b s`. Use `show (AlgEquiv.piCongrRight fun i => Algebra.TensorProduct.comm F B (L i)) ((Algebra.TensorProduct.piRight F F B L) ((Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[F] B) φ) (c (b ⊗ₜ s)))) = _`. Rewrite using `[hc]`. Both sides reduce to the same expression.

Use `⟨I, inferInstance, L, hL, hchar, instF, Φ, ψ, ?_, ?_⟩` and prove the remaining obligations. Introduce `b`. Rewrite using `[hΦ]`. Use function extensionality and compare the values at `i`. Rewrite using `[← Algebra.TensorProduct.one_def, map_one, Pi.one_apply]`.

Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => funext i`. Simplify using the standard rewrite rules. Consider the case `add x y hx hy`.

Rewrite using `[map_add, map_add, hx, hy]`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.add_apply, map_add]`. Consider the case `tmul s f`. Establish `key : ∀ i, (algebraMap F (L i) f) * ψ (s ⊗ₜ 1) i = ψ (s ⊗ₜ f) i`.

Introduce `i`. Use `show ψ (1 ⊗ₜ f) i * ψ (s ⊗ₜ 1) i = _`. Rewrite using `[← Pi.mul_apply, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]`. Rewrite using `[Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.coe_toAlgHom', hΦ]`. Use function extensionality and compare the values at `i`.

Rewrite using `[Algebra.algebraMap_eq_smul_one f, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, key, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]`.
-/
theorem tensor_decomp_factorwise : ∀ (S F B : Type) [Field S] [CharZero S] [Field F] [Algebra ℚ F] [FiniteDimensional ℚ F] [Ring B]
    [Algebra F B] [Algebra ℚ B] [IsScalarTower ℚ F B],
    ∃ (ι : Type) (_ : Fintype ι) (L : ι → Type) (_ : ∀ i, Field (L i)) (_ : ∀ i, CharZero (L i))
      (_ : ∀ i, Algebra F (L i)) (Φ : S ⊗[ℚ] B ≃+* ((i : ι) → L i ⊗[F] B)) (ψ : S ⊗[ℚ] F ≃+* ((i : ι) → L i)),
      (∀ b : B, Φ ((1 : S) ⊗ₜ[ℚ] b) = fun i => (1 : L i) ⊗ₜ[F] b) ∧
      (∀ z : S ⊗[ℚ] F, Φ (Algebra.TensorProduct.map (AlgHom.id S S) (IsScalarTower.toAlgHom ℚ F B) z) =
        fun i => algebraMap (L i) (L i ⊗[F] B) (ψ z i)) := by
  intro S F B _ _ _ _ _ _ _ _ _
  haveI hEt : Algebra.Etale ℚ F := by
    haveI : Algebra.IsSeparable ℚ F := inferInstance
    haveI : Algebra.FormallyEtale ℚ F := Algebra.FormallyEtale.of_isSeparable ℚ F
    haveI : Algebra.FinitePresentation ℚ F := Algebra.FinitePresentation.of_finiteType.mp inferInstance
    constructor <;> infer_instance
  haveI : Algebra.Etale S (S ⊗[ℚ] F) := Algebra.Etale.baseChange ℚ F S
  obtain ⟨I, hI, L, hL, hAL, e, -⟩ := (Algebra.Etale.iff_exists_algEquiv_prod S (S ⊗[ℚ] F)).mp this
  letI : Fintype I := Fintype.ofFinite I
  classical
  let ψ : S ⊗[ℚ] F ≃+* ((i : I) → L i) := e.toRingEquiv
  letI instF : ∀ i, Algebra F (L i) := fun i =>
    ((Pi.evalRingHom L i).comp (ψ.toRingHom.comp
      (Algebra.TensorProduct.includeRight : F →ₐ[ℚ] S ⊗[ℚ] F).toRingHom)).toAlgebra
  have hchar : ∀ i, CharZero (L i) := fun i =>
    charZero_of_injective_algebraMap (R := S) (algebraMap S (L i)).injective
  let φ : F ⊗[ℚ] S ≃ₐ[F] ((i : I) → L i) :=
    AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm ℚ F S).toRingEquiv.trans ψ) (fun x => by
      funext i
      rfl)
  let c : B ⊗[ℚ] S ≃ₐ[F] B ⊗[F] (F ⊗[ℚ] S) :=
    AlgEquiv.ofLinearEquiv (TensorProduct.AlgebraTensorModule.cancelBaseChange ℚ F F B S).symm
      (by simp [Algebra.TensorProduct.one_def])
      (LinearMap.map_mul_of_map_mul_tmul (fun _ _ _ _ ↦ by simp))
  let Φ : S ⊗[ℚ] B ≃+* ((i : I) → L i ⊗[F] B) :=
    (Algebra.TensorProduct.comm ℚ S B).toRingEquiv.trans <| c.toRingEquiv.trans <|
      (Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[F] B) φ).toRingEquiv.trans <|
      (Algebra.TensorProduct.piRight F F B L).toRingEquiv.trans
      (AlgEquiv.piCongrRight fun i => Algebra.TensorProduct.comm F B (L i)).toRingEquiv
  have hΦ : ∀ (s : S) (b : B), Φ (s ⊗ₜ b) = fun i => ψ (s ⊗ₜ 1) i ⊗ₜ[F] b := by
    intro s b
    have hc : c (b ⊗ₜ s) = b ⊗ₜ ((1 : F) ⊗ₜ s) :=
      TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul ℚ F F b s
    show (AlgEquiv.piCongrRight fun i => Algebra.TensorProduct.comm F B (L i))
      ((Algebra.TensorProduct.piRight F F B L)
        ((Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[F] B) φ) (c (b ⊗ₜ s)))) = _
    rw [hc]
    rfl
  refine ⟨I, inferInstance, L, hL, hchar, instF, Φ, ψ, ?_, ?_⟩
  · intro b
    rw [hΦ]
    funext i
    rw [← Algebra.TensorProduct.one_def, map_one, Pi.one_apply]
  · intro z
    induction z using TensorProduct.induction_on with
    | zero => funext i; simp
    | add x y hx hy =>
      rw [map_add, map_add, hx, hy]
      funext i
      simp only [Pi.add_apply, map_add]
    | tmul s f =>
      have key : ∀ i, (algebraMap F (L i) f) * ψ (s ⊗ₜ 1) i = ψ (s ⊗ₜ f) i := by
        intro i
        show ψ (1 ⊗ₜ f) i * ψ (s ⊗ₜ 1) i = _
        rw [← Pi.mul_apply, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.coe_toAlgHom', hΦ]
      funext i
      rw [Algebra.algebraMap_eq_smul_one f, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        Algebra.smul_def, key, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply]

end GlobalTheory
