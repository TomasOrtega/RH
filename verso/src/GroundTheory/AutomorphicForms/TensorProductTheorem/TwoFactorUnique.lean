import Mathlib
import GroundTheory.AutomorphicForms.TensorProductTheorem.TwoFactor

noncomputable section

namespace GroundTheory.Automorphic

namespace RestrictedTensor

open Module Set TensorProduct

open scoped TensorProduct

variable {M₁ M₂ : Type*} [Monoid M₁] [Monoid M₂]
  {V₁ V₂ V₁' V₂' : Type*} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
  [AddCommGroup V₁'] [Module ℂ V₁'] [AddCommGroup V₂'] [Module ℂ V₂']

def contractRight (l : Dual ℂ V₂) : V₁ ⊗[ℂ] V₂ →ₗ[ℂ] V₁ :=
  TensorProduct.rid ℂ V₁ ∘ₗ TensorProduct.map LinearMap.id l

def contractLeft (l : Dual ℂ V₁) : V₁ ⊗[ℂ] V₂ →ₗ[ℂ] V₂ :=
  TensorProduct.lid ℂ V₂ ∘ₗ TensorProduct.map l LinearMap.id

/- English proof (translation)
Simplify using `[contractRight]`.
-/
theorem contractRight_tmul (l : Dual ℂ V₂) (x : V₁) (y : V₂) :
    contractRight l (x ⊗ₜ y) = l y • x := by
  simp [contractRight]

/- English proof (translation)
Simplify using `[contractLeft]`.
-/
theorem contractLeft_tmul (l : Dual ℂ V₁) (x : V₁) (y : V₂) :
    contractLeft (V₂ := V₂) l (x ⊗ₜ y) = l x • y := by
  simp [contractLeft]

/- English proof (translation)
Set `b` to `Basis.ofVectorSpace ℂ V₂`. Use `set F := TensorProduct.equivFinsuppOfBasisRight (M := V₁) b`. Establish `hfz : F z ≠ 0` using `fun h => hz (F.injective (h.trans (map_zero F).symm))`. Take `⟨j₀, hj₀⟩` from `Finsupp.ne_iff.1 hfz`. Simplify using `only [Finsupp.coe_zero, Pi.zero_apply] at hj₀`.

Use `⟨b.coord j₀, ?_⟩` and prove the remaining obligations. Establish `hz' : z = (F z).sum fun j a => a ⊗ₜ[ℂ] b j` using `by conv_lhs => rw [← F.symm_apply_apply z]`. Conclude with `TensorProduct.equivFinsuppOfBasisRight_symm_apply b (F z)`. Rewrite using `[hz', map_finsuppSum]`. Simplify using `only [contractRight_tmul, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]`.

Rewrite using `[Finsupp.sum, Finset.sum_eq_single j₀]`. Simplify using `using hj₀`. Introduce `j _ hj`. Simplify using `[hj]`. Introduce `h`.

Conclude with `absurd (Finsupp.mem_support_iff.2 hj₀) h`.
-/
theorem exists_contractRight_ne_zero {z : V₁ ⊗[ℂ] V₂} (hz : z ≠ 0) :
    ∃ l : Dual ℂ V₂, contractRight l z ≠ 0 := by
  classical
  let b := Basis.ofVectorSpace ℂ V₂
  set F := TensorProduct.equivFinsuppOfBasisRight (M := V₁) b
  have hfz : F z ≠ 0 := fun h => hz (F.injective (h.trans (map_zero F).symm))
  obtain ⟨j₀, hj₀⟩ := Finsupp.ne_iff.1 hfz
  simp only [Finsupp.coe_zero, Pi.zero_apply] at hj₀
  refine ⟨b.coord j₀, ?_⟩
  have hz' : z = (F z).sum fun j a => a ⊗ₜ[ℂ] b j := by
    conv_lhs => rw [← F.symm_apply_apply z]
    exact TensorProduct.equivFinsuppOfBasisRight_symm_apply b (F z)
  rw [hz', map_finsuppSum]
  simp only [contractRight_tmul, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
  rw [Finsupp.sum, Finset.sum_eq_single j₀]
  · simpa using hj₀
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finsupp.mem_support_iff.2 hj₀) h

/- English proof (translation)
Take `⟨l, hl⟩` from `exists_contractRight_ne_zero (V₁ := V₂) (V₂ := V₁) (z := TensorProduct.comm ℂ V₁ V₂ z) (fun h => hz (by`. Use `congrArg (TensorProduct.comm ℂ V₁ V₂).symm h` as an intermediate fact. Simplify using `using this))`. Use `⟨l, ?_⟩` and prove the remaining obligations. Establish `key : ∀ z' : V₁ ⊗[ℂ] V₂, contractLeft (V₂` using `V₂) l z' = contractRight l (TensorProduct.comm ℂ V₁ V₂ z') := by`.

Introduce `z'`. Proceed by induction on `z' using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y => simp [contractLeft_tmul, contractRight_tmul]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.

Rewrite using `[key]` and apply the resulting hypothesis.
-/
theorem exists_contractLeft_ne_zero {z : V₁ ⊗[ℂ] V₂} (hz : z ≠ 0) :
    ∃ l : Dual ℂ V₁, contractLeft l z ≠ 0 := by
  obtain ⟨l, hl⟩ := exists_contractRight_ne_zero (V₁ := V₂) (V₂ := V₁)
    (z := TensorProduct.comm ℂ V₁ V₂ z) (fun h => hz (by
      have := congrArg (TensorProduct.comm ℂ V₁ V₂).symm h
      simpa using this))
  refine ⟨l, ?_⟩
  have key : ∀ z' : V₁ ⊗[ℂ] V₂,
      contractLeft (V₂ := V₂) l z' = contractRight l (TensorProduct.comm ℂ V₁ V₂ z') := by
    intro z'
    induction z' using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [contractLeft_tmul, contractRight_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  rwa [key]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y => simp [outerTensor_tmul, contractRight_tmul]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem contractRight_outerTensor (π₁ : Representation ℂ M₁ V₁) (π₂ : Representation ℂ M₂ V₂)
    (l : Dual ℂ V₂) (a : M₁) (z : V₁ ⊗[ℂ] V₂) :
    contractRight l (outerTensor π₁ π₂ (a, 1) z) = π₁ a (contractRight l z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [outerTensor_tmul, contractRight_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y => simp [outerTensor_tmul, contractLeft_tmul]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem contractLeft_outerTensor (π₁ : Representation ℂ M₁ V₁) (π₂ : Representation ℂ M₂ V₂)
    (l : Dual ℂ V₁) (b : M₂) (z : V₁ ⊗[ℂ] V₂) :
    contractLeft l (outerTensor π₁ π₂ (1, b) z) = π₂ b (contractLeft l z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [outerTensor_tmul, contractLeft_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨l, hl⟩ : ∃ l : Dual ℂ V₂, l y ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Conclude with `hy ((Module.forall_dual_apply_eq_zero_iff ℂ y).1 hcon)`. Introduce `h`.

Use `congrArg (contractRight l) h` as an intermediate fact. Rewrite `this` using `[contractRight_tmul, map_zero]`. Conclude with `(smul_ne_zero hl hx) this`.
-/
theorem tmul_ne_zero_of {x : V₁} {y : V₂} (hx : x ≠ 0) (hy : y ≠ 0) : x ⊗ₜ[ℂ] y ≠ 0 := by
  obtain ⟨l, hl⟩ : ∃ l : Dual ℂ V₂, l y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hy ((Module.forall_dual_apply_eq_zero_iff ℂ y).1 hcon)
  intro h
  have := congrArg (contractRight l) h
  rw [contractRight_tmul, map_zero] at this
  exact (smul_ne_zero hl hx) this

variable {π₁ : Representation ℂ M₁ V₁} {π₂ : Representation ℂ M₂ V₂}
  {π₁' : Representation ℂ M₁ V₁'} {π₂' : Representation ℂ M₂ V₂'}

/- English proof (translation)
Use `haveI := h₁`. Use `haveI := h₁'`. Use `nontrivial_of_irreducible h₁` as an intermediate fact. Use `nontrivial_of_irreducible h₂` as an intermediate fact. Take `⟨u, hu⟩` from `exists_ne (0 : V₁)`.

Take `⟨v, hv⟩` from `exists_ne (0 : V₂)`. Establish `hΦ : ∀ p z, Φ (outerTensor π₁ π₂ p z) = outerTensor π₁' π₂' p (Φ z)` using `fun p z => Representation.IntertwiningMap.isIntertwining _ _ Φ.toIntertwiningMap p z`. Establish `hy : Φ (u ⊗ₜ v) ≠ 0` using `fun h => tmul_ne_zero_of hu hv (Φ.toLinearEquiv.injective (h.trans (map_zero _).symm))`. Take `⟨l₂, hl₂⟩` from `exists_contractRight_ne_zero hy`. Choose the witnesses or unpack the hypotheses as in `⟨l₁, hl₁⟩ : ∃ l : Dual ℂ V₁', l (contractRight l₂ (Φ (u ⊗ₜ v))) ≠ 0 := by`.

Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Conclude with `hl₂ ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hcon)`. Set `μ : Dual ℂ V₁` to `l₁ ∘ₗ contractRight l₂ ∘ₗ Φ.toLinearEquiv.toLinearMap ∘ₗ (TensorProduct.mk ℂ V₁ V₂).flip v`. Use `nonempty_equiv_of_matrixCoeff_eq' (v := u) (l := μ) (w := contractRight l₂ (Φ (u ⊗ₜ v))) (m := l₁) (fun a => ?_) ⟨1, ?_⟩` and prove the remaining obligations.

Establish `: π₁ a u ⊗ₜ[ℂ] v = outerTensor π₁ π₂ (a, 1) (u ⊗ₜ v)`. Rewrite using `[outerTensor_tmul, map_one, Module.End.one_apply]`. Use `show l₁ (contractRight l₂ (Φ (π₁ a u ⊗ₜ v))) = _`. Rewrite using `[this, hΦ, contractRight_outerTensor]`. Use `show l₁ (contractRight l₂ (Φ (π₁ 1 u ⊗ₜ v))) ≠ 0`.

Rewrite using `[map_one, Module.End.one_apply]` and apply the resulting hypothesis.
-/
theorem nonempty_equiv_fst_of_equiv (h₁ : π₁.IsIrreducible) (h₂ : π₂.IsIrreducible)
    (h₁' : π₁'.IsIrreducible) (Φ : (outerTensor π₁ π₂).Equiv (outerTensor π₁' π₂')) :
    Nonempty (π₁.Equiv π₁') := by
  haveI := h₁
  haveI := h₁'
  have := nontrivial_of_irreducible h₁
  have := nontrivial_of_irreducible h₂
  obtain ⟨u, hu⟩ := exists_ne (0 : V₁)
  obtain ⟨v, hv⟩ := exists_ne (0 : V₂)
  have hΦ : ∀ p z, Φ (outerTensor π₁ π₂ p z) = outerTensor π₁' π₂' p (Φ z) :=
    fun p z => Representation.IntertwiningMap.isIntertwining _ _ Φ.toIntertwiningMap p z
  have hy : Φ (u ⊗ₜ v) ≠ 0 := fun h =>
    tmul_ne_zero_of hu hv (Φ.toLinearEquiv.injective (h.trans (map_zero _).symm))
  obtain ⟨l₂, hl₂⟩ := exists_contractRight_ne_zero hy
  obtain ⟨l₁, hl₁⟩ : ∃ l : Dual ℂ V₁', l (contractRight l₂ (Φ (u ⊗ₜ v))) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hl₂ ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hcon)
  let μ : Dual ℂ V₁ := l₁ ∘ₗ contractRight l₂ ∘ₗ Φ.toLinearEquiv.toLinearMap ∘ₗ
    (TensorProduct.mk ℂ V₁ V₂).flip v
  refine nonempty_equiv_of_matrixCoeff_eq' (v := u) (l := μ)
    (w := contractRight l₂ (Φ (u ⊗ₜ v))) (m := l₁) (fun a => ?_) ⟨1, ?_⟩
  · have : π₁ a u ⊗ₜ[ℂ] v = outerTensor π₁ π₂ (a, 1) (u ⊗ₜ v) := by
      rw [outerTensor_tmul, map_one, Module.End.one_apply]
    show l₁ (contractRight l₂ (Φ (π₁ a u ⊗ₜ v))) = _
    rw [this, hΦ, contractRight_outerTensor]
  · show l₁ (contractRight l₂ (Φ (π₁ 1 u ⊗ₜ v))) ≠ 0
    rwa [map_one, Module.End.one_apply]

/- English proof (translation)
Use `haveI := h₂`. Use `haveI := h₂'`. Use `nontrivial_of_irreducible h₁` as an intermediate fact. Use `nontrivial_of_irreducible h₂` as an intermediate fact. Take `⟨u, hu⟩` from `exists_ne (0 : V₁)`.

Take `⟨v, hv⟩` from `exists_ne (0 : V₂)`. Establish `hΦ : ∀ p z, Φ (outerTensor π₁ π₂ p z) = outerTensor π₁' π₂' p (Φ z)` using `fun p z => Representation.IntertwiningMap.isIntertwining _ _ Φ.toIntertwiningMap p z`. Establish `hy : Φ (u ⊗ₜ v) ≠ 0` using `fun h => tmul_ne_zero_of hu hv (Φ.toLinearEquiv.injective (h.trans (map_zero _).symm))`. Take `⟨l₁, hl₁⟩` from `exists_contractLeft_ne_zero hy`. Choose the witnesses or unpack the hypotheses as in `⟨l₂, hl₂⟩ : ∃ l : Dual ℂ V₂', l (contractLeft l₁ (Φ (u ⊗ₜ v))) ≠ 0 := by`.

Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Conclude with `hl₁ ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hcon)`. Set `μ : Dual ℂ V₂` to `l₂ ∘ₗ contractLeft l₁ ∘ₗ Φ.toLinearEquiv.toLinearMap ∘ₗ TensorProduct.mk ℂ V₁ V₂ u`. Use `nonempty_equiv_of_matrixCoeff_eq' (v := v) (l := μ) (w := contractLeft l₁ (Φ (u ⊗ₜ v))) (m := l₂) (fun b => ?_) ⟨1, ?_⟩` and prove the remaining obligations.

Establish `: u ⊗ₜ[ℂ] π₂ b v = outerTensor π₁ π₂ (1, b) (u ⊗ₜ v)`. Rewrite using `[outerTensor_tmul, map_one, Module.End.one_apply]`. Use `show l₂ (contractLeft l₁ (Φ (u ⊗ₜ π₂ b v))) = _`. Rewrite using `[this, hΦ, contractLeft_outerTensor]`. Use `show l₂ (contractLeft l₁ (Φ (u ⊗ₜ π₂ 1 v))) ≠ 0`.

Rewrite using `[map_one, Module.End.one_apply]` and apply the resulting hypothesis.
-/
theorem nonempty_equiv_snd_of_equiv (h₁ : π₁.IsIrreducible) (h₂ : π₂.IsIrreducible)
    (h₂' : π₂'.IsIrreducible) (Φ : (outerTensor π₁ π₂).Equiv (outerTensor π₁' π₂')) :
    Nonempty (π₂.Equiv π₂') := by
  haveI := h₂
  haveI := h₂'
  have := nontrivial_of_irreducible h₁
  have := nontrivial_of_irreducible h₂
  obtain ⟨u, hu⟩ := exists_ne (0 : V₁)
  obtain ⟨v, hv⟩ := exists_ne (0 : V₂)
  have hΦ : ∀ p z, Φ (outerTensor π₁ π₂ p z) = outerTensor π₁' π₂' p (Φ z) :=
    fun p z => Representation.IntertwiningMap.isIntertwining _ _ Φ.toIntertwiningMap p z
  have hy : Φ (u ⊗ₜ v) ≠ 0 := fun h =>
    tmul_ne_zero_of hu hv (Φ.toLinearEquiv.injective (h.trans (map_zero _).symm))
  obtain ⟨l₁, hl₁⟩ := exists_contractLeft_ne_zero hy
  obtain ⟨l₂, hl₂⟩ : ∃ l : Dual ℂ V₂', l (contractLeft l₁ (Φ (u ⊗ₜ v))) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hl₁ ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hcon)
  let μ : Dual ℂ V₂ := l₂ ∘ₗ contractLeft l₁ ∘ₗ Φ.toLinearEquiv.toLinearMap ∘ₗ
    TensorProduct.mk ℂ V₁ V₂ u
  refine nonempty_equiv_of_matrixCoeff_eq' (v := v) (l := μ)
    (w := contractLeft l₁ (Φ (u ⊗ₜ v))) (m := l₂) (fun b => ?_) ⟨1, ?_⟩
  · have : u ⊗ₜ[ℂ] π₂ b v = outerTensor π₁ π₂ (1, b) (u ⊗ₜ v) := by
      rw [outerTensor_tmul, map_one, Module.End.one_apply]
    show l₂ (contractLeft l₁ (Φ (u ⊗ₜ π₂ b v))) = _
    rw [this, hΦ, contractLeft_outerTensor]
  · show l₂ (contractLeft l₁ (Φ (u ⊗ₜ π₂ 1 v))) ≠ 0
    rwa [map_one, Module.End.one_apply]

end RestrictedTensor

end GroundTheory.Automorphic
