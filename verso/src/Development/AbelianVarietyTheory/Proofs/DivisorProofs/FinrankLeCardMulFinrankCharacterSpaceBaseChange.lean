import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTraceEquivariantAndInjectiveOfGroupDet

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module
open scoped TensorProduct

namespace GlobalTheory.BadCount

/- English proof (translation)
Rewrite using `[mem_nonZeroDivisors_iff_right]`. Introduce `x hx`. Establish `hinj : Function.Injective ((LinearMap.mulRight K d).lTensor L)` using `Module.Flat.lTensor_preserves_injective_linearMap _ (fun a b hab => by`. Establish `: (a - b) * d = 0` using `by simpa [sub_mul, sub_eq_zero] using hab`. Conclude with `sub_eq_zero.1 ((mem_nonZeroDivisors_iff_right.1 hd) _ this))`.

Establish `heq : ∀ y : L ⊗[K] R, (LinearMap.mulRight K d).lTensor L y = y * ((1 : L) ⊗ₜ[K] d)`. Introduce `y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul l r => simp [Algebra.TensorProduct.tmul_mul_tmul]`.

Consider the case `add a b ha hb => simp [map_add, add_mul, ha, hb]`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[heq, hx, map_zero]`.
-/
theorem tmul_one_mem_nonZeroDivisors_of_field {K L R : Type} [Field K] [Field L] [Algebra K L]
    [CommRing R] [Algebra K R] (d : R) (hd : d ∈ nonZeroDivisors R) :
    ((1 : L) ⊗ₜ[K] d) ∈ nonZeroDivisors (L ⊗[K] R) := by
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  have hinj : Function.Injective ((LinearMap.mulRight K d).lTensor L) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (fun a b hab => by
      have : (a - b) * d = 0 := by simpa [sub_mul, sub_eq_zero] using hab
      exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff_right.1 hd) _ this))
  have heq : ∀ y : L ⊗[K] R, (LinearMap.mulRight K d).lTensor L y = y * ((1 : L) ⊗ₜ[K] d) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul l r => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add a b ha hb => simp [map_add, add_mul, ha, hb]
  apply hinj
  rw [heq, hx, map_zero]

/- English proof (translation)
Introduce `K L Γ R W _ _ _ _ _ _ _ act H _ _ u hdet Vm V _ ρ hρ hVm _ _ _ _ f hf ρ' hρ' lam`. Set `actL : Γ → (L ⊗[K] R →ₐ[L] L ⊗[K] R)` to `fun g => Algebra.TensorProduct.map (AlgHom.id L L) (act g)`. Establish `actL_tmul : ∀ g (l : L) (r : R), actL g (l ⊗ₜ r) = l ⊗ₜ act g r` using `fun g l r => by`. Simplify using `[actL, Algebra.TensorProduct.map_tmul]`. Establish `actL_mul : ∀ g g' x, actL (g * g') x = actL g (actL g' x)`.

Introduce `g g' x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul l r => simp only [actL_tmul, map_mul, AlgHom.mul_apply]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.

Establish `actL_one : ∀ x, actL 1 x = x`. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul l r => simp only [actL_tmul, map_one, AlgHom.one_apply]`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Establish `inj_of : ∀ {M : Type} [AddCommGroup M] [Module K M] (g : M →ₗ[K] R), Function.Injective g → Function.Injective (g.baseChange L)`. Introduce `M _ _ g hg`. Rewrite using `[LinearMap.baseChange_eq_ltensor]`. Conclude with `Module.Flat.lTensor_preserves_injective_linearMap g hg`.

Set `ιV : L ⊗[K] V →ₗ[L] L ⊗[K] R` to `V.subtype.baseChange L`. Set `ιm : L ⊗[K] Vm →ₗ[L] L ⊗[K] R` to `Vm.subtype.baseChange L`. Set `A : H → (Vm →ₗ[K] V)` to `fun h => { toFun := fun x => ⟨(x : R) * act h u, hVm h x x.2⟩ map_add' := by intro x y; ext; simp [add_mul] map_smul' := by intro c x; ext; simp [smul_mul_assoc] }`. Establish `hA : ∀ h y, ιV ((A h).baseChange L y) = ιm y * ((1 : L) ⊗ₜ act h u)`. Introduce `h y`.

Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul l x => simp [ιV, ιm, A, Algebra.TensorProduct.tmul_mul_tmul]`. Consider the case `add x y hx hy => simp only [map_add, add_mul, hx, hy]`. Set `e` to `hf.equiv`.

Set `j : W →ₗ[L] L ⊗[K] R` to `ιV ∘ₗ e.symm.toLinearMap`. Establish `hj : ∀ (g : Γ) w, j (ρ' g w) = actL g (j w)`. Introduce `g w`. Take `⟨z, rfl⟩` from `e.surjective w`. Proceed by induction on `z using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul l v`. Establish `h1 : e (l ⊗ₜ v) = l • f v` using `hf.equiv_tmul l v`. Establish `h2 : e (l ⊗ₜ ρ g v) = l • f (ρ g v)` using `hf.equiv_tmul l _`. Simplify using `only [j, LinearMap.comp_apply, LinearEquiv.coe_coe]`.

Rewrite using `[h1, map_smul, hρ', ← h2, ← h1, e.symm_apply_apply, e.symm_apply_apply]`. Simplify using `[ιV, actL_tmul, hρ]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Establish `hje : ∀ z, j (e z) = ιV z` using `fun z => by simp [j]`. Set `T : W →ₗ[L] W` to `∑ g : H, (((lam g)⁻¹ : Lˣ) : L) • ρ' g`.

Establish `hT : ∀ w, T w ∈ eig ρ' H lam`. Introduce `w`. Rewrite using `[mem_eig]`. Introduce `k`. Simplify using `only [T, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum]`.

Use `Fintype.sum_equiv (Equiv.mulLeft k) _ _ (fun g => ?_)` and prove the remaining obligations. Rewrite using `[Equiv.coe_mulLeft, Subgroup.coe_mul, map_mul ρ', Module.End.mul_apply, smul_smul, map_mul lam]`. Use `congr 1`. Rewrite using `[← Units.val_mul, mul_inv, mul_inv_cancel_left]`. Establish `hjT : ∀ w, j (T w) = ∑ g : H, (((lam g)⁻¹ : Lˣ) : L) • actL g (j w)`.

Introduce `w`. Simplify using `only [T, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hj]`. Set `Ψ : L ⊗[K] Vm →ₗ[L] (H → eig ρ' H lam)` to `LinearMap.pi fun h => LinearMap.codRestrict (eig ρ' H lam) (T ∘ₗ e.toLinearMap ∘ₗ (A h).baseChange L) (fun y => hT _)`. Establish `hΨ : Function.Injective Ψ`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `y hy`. Establish `P : ∀ h : H, ∑ g : H, (((lam g)⁻¹ : Lˣ) : L) • actL g (ιm y * ((1 : L) ⊗ₜ act h u)) = 0`. Introduce `h`. Establish `h0` using `congrArg Subtype.val (congrFun hy h)`. Simplify using `only [Ψ, LinearMap.pi_apply, LinearMap.codRestrict_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, Pi.zero_apply, ZeroMemClass.coe_zero] at h0`.

Establish `h1` using `congrArg j h0`. Rewrite `h1` using `[hjT, hje, hA, map_zero]`. Conclude with `h1`. Establish `key` using `GlobalTheory.twistedTrace_equivariant_and_injective_of_groupDet H L (L ⊗[K] R) (fun h => actL ((h : Γ)⁻¹)) (fun x => by simp [actL_one]) (fun h h' x => by simp [mul_inv_rev, actL_mul]) lam⁻¹ ((1 : L) ⊗ₜ u) ?_`. Establish `hy0 : ιm y = 0`.

Use `key.2.1 (ιm y) (fun h' => ?_)` and prove the remaining obligations. Rewrite using `[← P h'⁻¹]`. Use `Fintype.sum_equiv (Equiv.inv H) _ _ (fun g => ?_)` and prove the remaining obligations. Simplify using `[actL_tmul]`. Conclude with `inj_of _ Vm.injective_subtype (by rw [hy0, map_zero])`.

Establish `hM : (Matrix.of fun h g : H => actL (((h * g : H) : Γ)⁻¹) ((1 : L) ⊗ₜ[K] u)) = (Algebra.TensorProduct.includeRight : R →ₐ[K] L ⊗[K] R).mapMatrix ((Matrix.transpose (Matrix.of fun h g : H => act ((h : Γ) * g) u)).submatrix (Equiv.inv H) (Equiv.inv H))`. Use extensionality with `h g`. Simplify using `[actL_tmul, mul_inv_rev]`. Use `show (Matrix.of fun h g : H => actL (((h * g : H) : Γ)⁻¹) ((1 : L) ⊗ₜ[K] u)).det ∈ _`. Rewrite using `[hM, ← AlgHom.map_det, Matrix.det_submatrix_equiv_self, Matrix.det_transpose, Algebra.TensorProduct.includeRight_apply]`.

Conclude with `tmul_one_mem_nonZeroDivisors_of_field _ hdet`. Establish `hfinW : Module.Finite L W` using `Module.Finite.equiv e`. Establish `h1 : finrank K Vm = finrank L (L ⊗[K] Vm)` using `(Module.finrank_baseChange).symm`. Rewrite using `[h1]`. Use `(LinearMap.finrank_le_finrank_of_injective hΨ).trans (le_of_eq ?_)` and prove the remaining obligations.

Rewrite using `[Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]`.
-/
theorem finrank_le_card_mul_finrank_eig_baseChange : ∀ (K L Γ R W : Type) [Field K] [Field L] [Algebra K L] [Group Γ] [Finite Γ] [CommRing R] [Algebra K R] (act : Γ →* (R →ₐ[K] R)) (H : Subgroup Γ) [Fintype H] [DecidableEq H] (u : R), (Matrix.of fun h g : H => act ((h : Γ) * g) u).det ∈ nonZeroDivisors R → ∀ (Vm V : Submodule K R) [FiniteDimensional K V] (ρ : Representation K Γ V), (∀ g x, (ρ g x : R) = act g x) → (∀ h : H, ∀ x ∈ Vm, x * act h u ∈ V) → ∀ [AddCommGroup W] [Module K W] [Module L W] [IsScalarTower K L W] (f : V →ₗ[K] W), IsBaseChange L f → ∀ (ρ' : Representation L Γ W), (∀ g v, ρ' g (f v) = f (ρ g v)) → ∀ lam : H →* Lˣ, finrank K Vm ≤ Nat.card H * finrank L (eig ρ' H lam) := by
  intro K L Γ R W _ _ _ _ _ _ _ act H _ _ u hdet Vm V _ ρ hρ hVm _ _ _ _ f hf ρ' hρ' lam
  classical
  let actL : Γ → (L ⊗[K] R →ₐ[L] L ⊗[K] R) := fun g => Algebra.TensorProduct.map (AlgHom.id L L) (act g)
  have actL_tmul : ∀ g (l : L) (r : R), actL g (l ⊗ₜ r) = l ⊗ₜ act g r := fun g l r => by
    simp [actL, Algebra.TensorProduct.map_tmul]
  have actL_mul : ∀ g g' x, actL (g * g') x = actL g (actL g' x) := by
    intro g g' x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul l r => simp only [actL_tmul, map_mul, AlgHom.mul_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  have actL_one : ∀ x, actL 1 x = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul l r => simp only [actL_tmul, map_one, AlgHom.one_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  have inj_of : ∀ {M : Type} [AddCommGroup M] [Module K M] (g : M →ₗ[K] R), Function.Injective g →
      Function.Injective (g.baseChange L) := by
    intro M _ _ g hg
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap g hg
  let ιV : L ⊗[K] V →ₗ[L] L ⊗[K] R := V.subtype.baseChange L
  let ιm : L ⊗[K] Vm →ₗ[L] L ⊗[K] R := Vm.subtype.baseChange L
  let A : H → (Vm →ₗ[K] V) := fun h =>
    { toFun := fun x => ⟨(x : R) * act h u, hVm h x x.2⟩
      map_add' := by intro x y; ext; simp [add_mul]
      map_smul' := by intro c x; ext; simp [smul_mul_assoc] }
  have hA : ∀ h y, ιV ((A h).baseChange L y) = ιm y * ((1 : L) ⊗ₜ act h u) := by
    intro h y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul l x => simp [ιV, ιm, A, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => simp only [map_add, add_mul, hx, hy]
  let e := hf.equiv
  let j : W →ₗ[L] L ⊗[K] R := ιV ∘ₗ e.symm.toLinearMap
  have hj : ∀ (g : Γ) w, j (ρ' g w) = actL g (j w) := by
    intro g w
    obtain ⟨z, rfl⟩ := e.surjective w
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul l v =>
      have h1 : e (l ⊗ₜ v) = l • f v := hf.equiv_tmul l v
      have h2 : e (l ⊗ₜ ρ g v) = l • f (ρ g v) := hf.equiv_tmul l _
      simp only [j, LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [h1, map_smul, hρ', ← h2, ← h1, e.symm_apply_apply, e.symm_apply_apply]
      simp [ιV, actL_tmul, hρ]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hje : ∀ z, j (e z) = ιV z := fun z => by simp [j]
  let T : W →ₗ[L] W := ∑ g : H, (((lam g)⁻¹ : Lˣ) : L) • ρ' g
  have hT : ∀ w, T w ∈ eig ρ' H lam := by
    intro w
    rw [mem_eig]
    intro k
    simp only [T, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft k) _ _ (fun g => ?_)
    rw [Equiv.coe_mulLeft, Subgroup.coe_mul, map_mul ρ', Module.End.mul_apply, smul_smul, map_mul lam]
    congr 1
    rw [← Units.val_mul, mul_inv, mul_inv_cancel_left]
  have hjT : ∀ w, j (T w) = ∑ g : H, (((lam g)⁻¹ : Lˣ) : L) • actL g (j w) := by
    intro w
    simp only [T, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hj]
  let Ψ : L ⊗[K] Vm →ₗ[L] (H → eig ρ' H lam) :=
    LinearMap.pi fun h => LinearMap.codRestrict (eig ρ' H lam) (T ∘ₗ e.toLinearMap ∘ₗ (A h).baseChange L)
      (fun y => hT _)
  have hΨ : Function.Injective Ψ := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    have P : ∀ h : H, ∑ g : H, (((lam g)⁻¹ : Lˣ) : L) • actL g (ιm y * ((1 : L) ⊗ₜ act h u)) = 0 := by
      intro h
      have h0 := congrArg Subtype.val (congrFun hy h)
      simp only [Ψ, LinearMap.pi_apply, LinearMap.codRestrict_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        Pi.zero_apply, ZeroMemClass.coe_zero] at h0
      have h1 := congrArg j h0
      rw [hjT, hje, hA, map_zero] at h1
      exact h1
    have key := GlobalTheory.twistedTrace_equivariant_and_injective_of_groupDet H L (L ⊗[K] R)
      (fun h => actL ((h : Γ)⁻¹)) (fun x => by simp [actL_one])
      (fun h h' x => by simp [mul_inv_rev, actL_mul]) lam⁻¹ ((1 : L) ⊗ₜ u) ?_
    · have hy0 : ιm y = 0 := by
        refine key.2.1 (ιm y) (fun h' => ?_)
        rw [← P h'⁻¹]
        refine Fintype.sum_equiv (Equiv.inv H) _ _ (fun g => ?_)
        simp [actL_tmul]
      exact inj_of _ Vm.injective_subtype (by rw [hy0, map_zero])
    · have hM : (Matrix.of fun h g : H => actL (((h * g : H) : Γ)⁻¹) ((1 : L) ⊗ₜ[K] u)) =
          (Algebra.TensorProduct.includeRight : R →ₐ[K] L ⊗[K] R).mapMatrix
            ((Matrix.transpose (Matrix.of fun h g : H => act ((h : Γ) * g) u)).submatrix (Equiv.inv H) (Equiv.inv H)) := by
        ext h g
        simp [actL_tmul, mul_inv_rev]
      show (Matrix.of fun h g : H => actL (((h * g : H) : Γ)⁻¹) ((1 : L) ⊗ₜ[K] u)).det ∈ _
      rw [hM, ← AlgHom.map_det, Matrix.det_submatrix_equiv_self, Matrix.det_transpose,
        Algebra.TensorProduct.includeRight_apply]
      exact tmul_one_mem_nonZeroDivisors_of_field _ hdet
  have hfinW : Module.Finite L W := Module.Finite.equiv e
  have h1 : finrank K Vm = finrank L (L ⊗[K] Vm) := (Module.finrank_baseChange).symm
  rw [h1]
  refine (LinearMap.finrank_le_finrank_of_injective hΨ).trans (le_of_eq ?_)
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

end GlobalTheory.BadCount
