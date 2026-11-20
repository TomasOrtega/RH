import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexificationBaseChangeLinearOneTmul

open scoped TensorProduct

noncomputable section
namespace GlobalTheory.DefRead.Transport

section General

variable {Ks LL WL C : Type} [Field Ks] [Field LL] [Algebra Ks LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL]
    [IsScalarTower Ks LL WL] [AddCommGroup C] [Module Ks C] [Algebra Ks ℂ] [Algebra LL ℂ] [IsScalarTower Ks LL ℂ]

def phiBil (e : C →ₗ[Ks] WL) : ℂ →+ C →+ ℂ ⊗[LL] WL :=
  AddMonoidHom.mk' (fun z => ((TensorProduct.mk LL ℂ WL z).toAddMonoidHom.comp e.toAddMonoidHom))
    (fun a b => by ext f; exact TensorProduct.add_tmul a b (e f))

/- English proof (translation)
Use `show (r • z) ⊗ₜ[LL] e f = z ⊗ₜ[LL] e (r • f)`. Rewrite using `[map_smul, ← algebraMap_smul LL r (e f), TensorProduct.tmul_smul, TensorProduct.smul_tmul', algebraMap_smul LL r z]`.
-/
theorem phiBil_compat (e : C →ₗ[Ks] WL) (r : Ks) (z : ℂ) (f : C) :
    phiBil (LL := LL) e (r • z) f = phiBil (LL := LL) e z (r • f) := by
  show (r • z) ⊗ₜ[LL] e f = z ⊗ₜ[LL] e (r • f)
  rw [map_smul, ← algebraMap_smul LL r (e f), TensorProduct.tmul_smul, TensorProduct.smul_tmul',
    algebraMap_smul LL r z]

def phi (e : C →ₗ[Ks] WL) : ℂ ⊗[Ks] C →ₗ[ℂ] ℂ ⊗[LL] WL where
  toFun := TensorProduct.liftAddHom (phiBil (LL := LL) e) (phiBil_compat e)
  map_add' := map_add _
  map_smul' c x := by
    induction x using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul z f =>
      rw [TensorProduct.smul_tmul', TensorProduct.liftAddHom_tmul, TensorProduct.liftAddHom_tmul]
      show (c • z) ⊗ₜ[LL] e f = c • (z ⊗ₜ[LL] e f)
      rw [TensorProduct.smul_tmul']
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/- English proof (translation)
The claim follows from `TensorProduct.liftAddHom_tmul (phiBil (LL := LL) e) (phiBil_compat e) z f`.
-/
@[simp] theorem phi_tmul (e : C →ₗ[Ks] WL) (z : ℂ) (f : C) : phi e (z ⊗ₜ[Ks] f) = z ⊗ₜ[LL] e f :=
  TensorProduct.liftAddHom_tmul (phiBil (LL := LL) e) (phiBil_compat e) z f

/- English proof (translation)
Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul z f => simp [h]`. Consider the case `add x y hx hy => simp only [LinearMap.comp_apply, map_add] at hx hy ⊢`.

Rewrite using `[hx, hy]`.
-/
theorem phi_comm (e : C →ₗ[Ks] WL) (a : C →ₗ[Ks] C) (r : WL →ₗ[LL] WL) (h : ∀ f, e (a f) = r (e f)) :
    phi e ∘ₗ a.baseChange ℂ = r.baseChange ℂ ∘ₗ phi e := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z f => simp [h]
  | add x y hx hy => simp only [LinearMap.comp_apply, map_add] at hx hy ⊢; rw [hx, hy]

/- English proof (translation)
Set `bW : Module.Basis (Fin n) Ks (Submodule.span Ks (Set.range b))` to `Module.Basis.span hliK`. Set `bK : Module.Basis (Fin n) Ks WK` to `bW.map (LinearEquiv.ofEq _ _ hspK)`. Set `bC : Module.Basis (Fin n) Ks C` to `bK.map e.symm`. Set `bL : Module.Basis (Fin n) LL WL` to `Module.Basis.mk hliL (by rw [hspL])`. Set `cC` to `Algebra.TensorProduct.basis ℂ bC`.

Set `cL` to `Algebra.TensorProduct.basis ℂ bL`. Establish `key : phi (LL` using `LL) (WK.subtype ∘ₗ e.toLinearMap) = (cC.equiv cL (Equiv.refl _)).toLinearMap := by`. Use `cC.ext fun j => ?_` and prove the remaining obligations. Use `show _ = (cC.equiv cL (Equiv.refl _)) (cC j)`. Rewrite using `[Module.Basis.equiv_apply, Equiv.refl_apply]`.

Simplify using `[cC, cL, bC, bK, bW, bL, Module.Basis.span_apply]`. Rewrite using `[key]`. Conclude with `(cC.equiv cL (Equiv.refl _)).bijective`.
-/
theorem phi_bijective (WK : Submodule Ks WL) (n : ℕ) (b : Fin n → WL) (hliK : LinearIndependent Ks b)
    (hspK : Submodule.span Ks (Set.range b) = WK) (hliL : LinearIndependent LL b)
    (hspL : Submodule.span LL (Set.range b) = ⊤) (e : C ≃ₗ[Ks] WK) :
    Function.Bijective (phi (LL := LL) (WK.subtype ∘ₗ e.toLinearMap)) := by
  let bW : Module.Basis (Fin n) Ks (Submodule.span Ks (Set.range b)) := Module.Basis.span hliK
  let bK : Module.Basis (Fin n) Ks WK := bW.map (LinearEquiv.ofEq _ _ hspK)
  let bC : Module.Basis (Fin n) Ks C := bK.map e.symm
  let bL : Module.Basis (Fin n) LL WL := Module.Basis.mk hliL (by rw [hspL])
  let cC := Algebra.TensorProduct.basis ℂ bC
  let cL := Algebra.TensorProduct.basis ℂ bL
  have key : phi (LL := LL) (WK.subtype ∘ₗ e.toLinearMap) = (cC.equiv cL (Equiv.refl _)).toLinearMap := by
    refine cC.ext fun j => ?_
    show _ = (cC.equiv cL (Equiv.refl _)) (cC j)
    rw [Module.Basis.equiv_apply, Equiv.refl_apply]
    simp [cC, cL, bC, bK, bW, bL, Module.Basis.span_apply]
  rw [key]
  exact (cC.equiv cL (Equiv.refl _)).bijective

/- English proof (translation)
Set `Ψ` to `LinearEquiv.ofBijective (phi (LL := LL) (WK.subtype ∘ₗ e.toLinearMap)) (phi_bijective WK n b hliK hspK hliL hspL e)`. Set `o` to `Submodule.orderIsoMapComap Ψ`. Use `⟨fun y => o (A y), ?_, ?_⟩` and prove the remaining obligations. Rewrite `hA`, the goal using `[DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]`. Use `⟨iSupIndep.map_orderIso o hA.1, ?_⟩` and prove the remaining obligations.

Rewrite using `[← o.map_iSup, hA.2, o.map_top]`. Introduce `h y v hv`. Take `⟨u, hu, rfl⟩` from `(Submodule.mem_map).1 hv`. Establish `hc` using `LinearMap.congr_fun (phi_comm (WK.subtype ∘ₗ e.toLinearMap) (act (φ h)) (ρ0 (φ h)) (fun f => he _ f)) u`. Use `Submodule.mem_map.2 ⟨s (φ h) • (act (φ h)).baseChange ℂ u, (A (h • y)).smul_mem _ (hinv h y u hu), ?_⟩` and prove the remaining obligations.

Simplify using `only [LinearMap.comp_apply] at hc`. Simplify using `only [LinearMap.smul_apply, map_smul]`. Use `show s (φ h) • phi (LL := LL) (WK.subtype ∘ₗ e.toLinearMap) _ = s (φ h) • (ρ0 (φ h)).baseChange ℂ (phi (LL := LL) (WK.subtype ∘ₗ e.toLinearMap) u)`. Rewrite using `[hc]`.
-/
theorem transport_general {H G X : Type} [Group G] [Group H] [DecidableEq X] [MulAction H X]
    (WK : Submodule Ks WL) (n : ℕ) (b : Fin n → WL) (hliK : LinearIndependent Ks b)
    (hspK : Submodule.span Ks (Set.range b) = WK) (hliL : LinearIndependent LL b)
    (hspL : Submodule.span LL (Set.range b) = ⊤) (e : C ≃ₗ[Ks] WK) (ρ0 : G → (WL →ₗ[LL] WL))
    (act : G → C →ₗ[Ks] C) (he : ∀ g f, ((e (act g f) : WK) : WL) = ρ0 g (e f)) (s : G → ℂ) (φ : H →* G)
    (A : X → Submodule ℂ (ℂ ⊗[Ks] C)) (hA : DirectSum.IsInternal A)
    (hinv : ∀ (h : H) (y : X), ∀ v ∈ A y, (act (φ h)).baseChange ℂ v ∈ A (h • y)) :
    ∃ A' : X → Submodule ℂ (ℂ ⊗[LL] WL), DirectSum.IsInternal A' ∧
      ∀ (h : H) (y : X), ∀ v ∈ A' y, (s (φ h) • (ρ0 (φ h)).baseChange ℂ) v ∈ A' (h • y) := by
  let Ψ := LinearEquiv.ofBijective (phi (LL := LL) (WK.subtype ∘ₗ e.toLinearMap))
    (phi_bijective WK n b hliK hspK hliL hspL e)
  let o := Submodule.orderIsoMapComap Ψ
  refine ⟨fun y => o (A y), ?_, ?_⟩
  · rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hA ⊢
    refine ⟨iSupIndep.map_orderIso o hA.1, ?_⟩
    rw [← o.map_iSup, hA.2, o.map_top]
  · intro h y v hv
    obtain ⟨u, hu, rfl⟩ := (Submodule.mem_map).1 hv
    have hc := LinearMap.congr_fun (phi_comm (WK.subtype ∘ₗ e.toLinearMap) (act (φ h)) (ρ0 (φ h))
      (fun f => he _ f)) u
    refine Submodule.mem_map.2 ⟨s (φ h) • (act (φ h)).baseChange ℂ u, (A (h • y)).smul_mem _ (hinv h y u hu), ?_⟩
    simp only [LinearMap.comp_apply] at hc
    simp only [LinearMap.smul_apply, map_smul]
    show s (φ h) • phi (LL := LL) (WK.subtype ∘ₗ e.toLinearMap) _ = s (φ h) • (ρ0 (φ h)).baseChange ℂ (phi (LL := LL) (WK.subtype ∘ₗ e.toLinearMap) u)
    rw [hc]

end General

open GlobalTheory.DefRead in

/- English proof (translation)
Introduce `Ks LL WL C H G X _ _ _ _ _ _ _ _ _ _ _ _ _ _ σ WK n b _ hliK hspK hliL hspL e ρ0 χ act he φ A hA hinv`. Use `letI : Algebra Ks ℂ := (σ.comp (algebraMap Ks LL)).toAlgebra`. Use `letI : Algebra LL ℂ := σ.toAlgebra`. Use `haveI : IsScalarTower Ks LL ℂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Take `⟨A', h1, h2⟩` from `transport_general (X := X) WK n b hliK hspK hliL hspL e (fun g => ρ0 g) act he (fun g => σ (((χ g)⁻¹ : LLˣ) : LL)) φ A hA hinv`.

Conclude with `⟨A', h1, fun h y v hv => by rw [twBC_apply]; exact h2 h y v hv⟩`.
-/
theorem transport : ∀ (Ks LL WL C H G X : Type) [Field Ks] [Field LL] [Algebra Ks LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL]
    [IsScalarTower Ks LL WL] [AddCommGroup C] [Module Ks C] [Group G] [Group H] [Fintype X] [DecidableEq X] [MulAction H X]
    (σ : LL →+* ℂ) (WK : Submodule Ks WL) (n : ℕ) (b : Fin n → WL), (∀ j, b j ∈ WK) → LinearIndependent Ks b →
    Submodule.span Ks (Set.range b) = WK → LinearIndependent LL b → Submodule.span LL (Set.range b) = ⊤ →
    ∀ (e : C ≃ₗ[Ks] WK) (ρ0 : G →* (WL →ₗ[LL] WL)) (χ : G →* LLˣ) (act : G → C →ₗ[Ks] C),
    (∀ g f, ((e (act g f) : WK) : WL) = ρ0 g (e f)) → ∀ (φ : H →* G) (A : X → Submodule ℂ (GlobalTheory.DefRead.VC (σ.comp (algebraMap Ks LL)) C)),
    DirectSum.IsInternal A → (∀ (h : H) (y : X), ∀ v ∈ A y, GlobalTheory.DefRead.bcLin (σ.comp (algebraMap Ks LL)) (act (φ h)) v ∈ A (h • y)) →
    ∃ A' : X → Submodule ℂ (GlobalTheory.DefRead.VC σ WL), DirectSum.IsInternal A' ∧
      ∀ (h : H) (y : X), ∀ v ∈ A' y, GlobalTheory.DefRead.twBC σ ρ0 χ (φ h) v ∈ A' (h • y) := by
  intro Ks LL WL C H G X _ _ _ _ _ _ _ _ _ _ _ _ _ _ σ WK n b _ hliK hspK hliL hspL e ρ0 χ act he φ A hA hinv
  letI : Algebra Ks ℂ := (σ.comp (algebraMap Ks LL)).toAlgebra
  letI : Algebra LL ℂ := σ.toAlgebra
  haveI : IsScalarTower Ks LL ℂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨A', h1, h2⟩ := transport_general (X := X) WK n b hliK hspK hliL hspL e (fun g => ρ0 g) act he
    (fun g => σ (((χ g)⁻¹ : LLˣ) : LL)) φ A hA hinv
  exact ⟨A', h1, fun h y v hv => by rw [twBC_apply]; exact h2 h y v hv⟩

end GlobalTheory.DefRead.Transport
