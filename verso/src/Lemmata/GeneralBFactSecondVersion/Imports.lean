import Mathlib

namespace Bl.general_b_fact_second_version

/- English proof (translation)
Introduce `k A _ _ _ W S _ _ _ _ _ _ _ _ _ h`. Establish `: Nontrivial S` using `IsSimpleModule.nontrivial A S`. Take `⟨s, hs⟩` from `exists_ne (0 : S)`. Set `b` to `Module.finBasis k W`. Set `φ : A →ₗ[A] (Fin (Module.finrank k W) → W)` to `LinearMap.pi (fun i => LinearMap.toSpanSingleton A W (b i))`.

Set `σ : A →ₗ[A] S` to `LinearMap.toSpanSingleton A S s`. Establish `hker : LinearMap.ker φ ≤ LinearMap.ker σ`. Introduce `a ha`. Simplify using `only [LinearMap.mem_ker] at ha ⊢`. Establish `hb : ∀ i, a • b i = 0` using `fun i => by`.

Simplify `congr_fun ha i` using `[φ]`. Establish `hw : ∀ w : W, a • w = 0`. Introduce `w`. Establish `e : (DistribSMul.toLinearMap k W a) = 0` using `b.ext (fun i => hb i)`. Conclude with `LinearMap.congr_fun e w`.

Simplify `h a hw s` using `[σ]`. Set `ψ₀ : LinearMap.range φ →ₗ[A] S` to `(LinearMap.ker φ).liftQ σ hker ∘ₗ φ.quotKerEquivRange.symm.toLinearMap`. Establish `hsm : IsSemisimpleModule A (Fin (Module.finrank k W) → W)` using `inferInstance`. Take `⟨C, hC⟩` from `ComplementedLattice.exists_isCompl (LinearMap.range φ)`. Set `Ψ : (Fin (Module.finrank k W) → W) →ₗ[A] S` to `ψ₀ ∘ₗ Submodule.linearProjOfIsCompl _ _ hC`.

Establish `hΨ : Ψ (φ 1) = s`. Establish `h1 : Submodule.linearProjOfIsCompl _ _ hC (φ 1) = ⟨φ 1, LinearMap.mem_range_self φ 1⟩` using `Submodule.linearProjOfIsCompl_apply_left hC ⟨φ 1, LinearMap.mem_range_self φ 1⟩`. Simplify using `only [Ψ, ψ₀, LinearMap.comp_apply, h1, LinearEquiv.coe_toLinearMap, LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]`. Simplify using `[σ]`. Assume the negation of the conclusion as `hne`.

Use `push_neg at hne`. Establish `hz : Ψ = 0`. Apply `LinearMap.pi_ext'` to reduce the goal to its premises. Introduce `i`. Conclude with `hne _`.

Rewrite `hΨ` using `[hz]`. Conclude with `hs hΨ.symm`.
-/
theorem goal1 :
  ∀ {k A : Type} [inst : Field.{0} k] [inst_1 : Ring.{0} A] [inst_2 : Algebra.{0, 0} k A] {W S : Type}
  [inst_3 : AddCommGroup.{0} W] [inst_4 : Module.{0, 0} k W] [inst_5 : Module.{0, 0} A W]
  [IsScalarTower.{0, 0, 0} k A W] [inst_7 : AddCommGroup.{0} S] [inst_8 : Module.{0, 0} A S]
  [FiniteDimensional.{0, 0} k W] [IsSemisimpleModule.{0, 0} A W] [IsSimpleModule.{0, 0} A S],
  (∀ (a : A), (∀ (w : W), Eq.{1} (HSMul.hSMul.{0, 0, 0} a w) 0) → ∀ (s : S), Eq.{1} (HSMul.hSMul.{0, 0, 0} a s) 0) →
    Exists.{1} fun (f : LinearMap.{0, 0, 0, 0} (RingHom.id.{0} A) W S) ↦ Ne.{1} f 0 := by
  intro k A _ _ _ W S _ _ _ _ _ _ _ _ _ h
  classical
  have : Nontrivial S := IsSimpleModule.nontrivial A S
  obtain ⟨s, hs⟩ := exists_ne (0 : S)
  let b := Module.finBasis k W
  let φ : A →ₗ[A] (Fin (Module.finrank k W) → W) :=
    LinearMap.pi (fun i => LinearMap.toSpanSingleton A W (b i))
  let σ : A →ₗ[A] S := LinearMap.toSpanSingleton A S s
  have hker : LinearMap.ker φ ≤ LinearMap.ker σ := by
    intro a ha
    simp only [LinearMap.mem_ker] at ha ⊢
    have hb : ∀ i, a • b i = 0 := fun i => by
      simpa [φ] using congr_fun ha i
    have hw : ∀ w : W, a • w = 0 := by
      intro w
      have e : (DistribSMul.toLinearMap k W a) = 0 :=
        b.ext (fun i => hb i)
      exact LinearMap.congr_fun e w
    simpa [σ] using h a hw s
  let ψ₀ : LinearMap.range φ →ₗ[A] S :=
    (LinearMap.ker φ).liftQ σ hker ∘ₗ φ.quotKerEquivRange.symm.toLinearMap
  have hsm : IsSemisimpleModule A (Fin (Module.finrank k W) → W) := inferInstance
  obtain ⟨C, hC⟩ := ComplementedLattice.exists_isCompl (LinearMap.range φ)
  let Ψ : (Fin (Module.finrank k W) → W) →ₗ[A] S :=
    ψ₀ ∘ₗ Submodule.linearProjOfIsCompl _ _ hC
  have hΨ : Ψ (φ 1) = s := by
    have h1 : Submodule.linearProjOfIsCompl _ _ hC (φ 1) = ⟨φ 1, LinearMap.mem_range_self φ 1⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hC ⟨φ 1, LinearMap.mem_range_self φ 1⟩
    simp only [Ψ, ψ₀, LinearMap.comp_apply, h1, LinearEquiv.coe_toLinearMap,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
    simp [σ]
  by_contra hne
  push_neg at hne
  have hz : Ψ = 0 := by
    apply LinearMap.pi_ext'
    intro i
    exact hne _
  rw [hz] at hΨ
  exact hs hΨ.symm

end Bl.general_b_fact_second_version
