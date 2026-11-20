import Mathlib

namespace GlobalTheory

open TensorProduct

noncomputable def rightContract {F : Type} [Field F] {E E' : Type} [AddCommGroup E] [Module F E]
    [AddCommGroup E'] [Module F E'] (l : E' →ₗ[F] F) : TensorProduct F E E' →ₗ[F] E :=
  (TensorProduct.rid F E).toLinearMap ∘ₗ TensorProduct.map LinearMap.id l

/- English proof (translation)
Simplify using `[rightContract]`.
-/
theorem rightContract_tmul {F : Type} [Field F] {E E' : Type} [AddCommGroup E] [Module F E]
    [AddCommGroup E'] [Module F E'] (l : E' →ₗ[F] F) (x : E) (y : E') :
    rightContract l (x ⊗ₜ[F] y) = l y • x := by
  simp [rightContract]

/- English proof (translation)
Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y => simp [rightContract_tmul]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.
-/
theorem rightContract_map {F : Type} [Field F] {E E' : Type} [AddCommGroup E] [Module F E]
    [AddCommGroup E'] [Module F E'] (l : E' →ₗ[F] F) (f : E →ₗ[F] E) (g : E' →ₗ[F] E')
    (w : TensorProduct F E E') :
    rightContract l (TensorProduct.map f g w) = f (rightContract (l ∘ₗ g) w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [rightContract_tmul]
  | add a b ha hb => simp only [map_add, ha, hb]

/- English proof (translation)
Set `b` to `Module.Basis.ofVectorSpace F E'`. Establish `key : ∀ (i) (v : TensorProduct F E E'), TensorProduct.equivFinsuppOfBasisRight b v i = rightContract (b.coord i) v`. Introduce `i v`. Proceed by induction on `v using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul x y => simp [rightContract_tmul]`. Consider the case `add a c ha hc => simp only [map_add, Finsupp.add_apply, ha, hc]`. Apply `(TensorProduct.equivFinsuppOfBasisRight b).injective` to reduce the goal to its premises. Use extensionality with `i`. Rewrite using `[key, h]`.

Simplify using the standard rewrite rules.
-/
theorem eq_zero_of_rightContract {F : Type} [Field F] {E E' : Type} [AddCommGroup E] [Module F E]
    [AddCommGroup E'] [Module F E'] (w : TensorProduct F E E')
    (h : ∀ l : E' →ₗ[F] F, rightContract l w = 0) : w = 0 := by
  classical
  let b := Module.Basis.ofVectorSpace F E'
  have key : ∀ (i) (v : TensorProduct F E E'),
      TensorProduct.equivFinsuppOfBasisRight b v i = rightContract (b.coord i) v := by
    intro i v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [rightContract_tmul]
    | add a c ha hc => simp only [map_add, Finsupp.add_apply, ha, hc]
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  ext i
  rw [key, h]
  simp

/- English proof (translation)
Introduce `F _ E E' Ix _ _ _ _ Φ Φ' hirr w hw heig π hπ`. Set `U : Submodule F E` to `Submodule.span F (Set.range fun l : E' →ₗ[F] F => rightContract l w)`. Establish `hmem : ∀ l : E' →ₗ[F] F, rightContract l w ∈ U` using `fun l => Submodule.subset_span ⟨l, rfl⟩`. Establish `hstab : ∀ i, ∀ v ∈ U, Φ i v ∈ U`. Introduce `i v hv`.

Establish `hle : U ≤ U.comap (Φ i)`. Apply `Submodule.span_le.2` to reduce the goal to its premises. Introduce and unpack `_ ⟨l, rfl⟩`. Take `⟨r, hr⟩` from `heig i`. Establish `h1` using `rightContract_map (l ∘ₗ ((Φ' i).symm : E' →ₗ[F] E')) (Φ i) (Φ' i : E' →ₗ[F] E') w`.

Establish `h2 : (l ∘ₗ ((Φ' i).symm : E' →ₗ[F] E')) ∘ₗ (Φ' i : E' →ₗ[F] E') = l`. Use extensionality with `y`. Simplify using the standard rewrite rules. Rewrite `h1` using `[h2, hr, map_smul]`. Use `show Φ i (rightContract l w) ∈ U`.

Rewrite using `[← h1]`. Conclude with `U.smul_mem _ (hmem _)`. Conclude with `hle hv`. Break down `hirr U hstab with hU | hU` into its components or cases. It suffices to derive a contradiction.

Apply `hw` to reduce the goal to its premises. Apply `eq_zero_of_rightContract` to reduce the goal to its premises. Introduce `l`. Use `hmem l` as an intermediate fact. Rewrite `this` using `[hU, Submodule.mem_bot]`. Then use the resulting hypothesis.

Establish `hle : U ≤ LinearMap.ker π`. Apply `Submodule.span_le.2` to reduce the goal to its premises. Introduce and unpack `_ ⟨l, rfl⟩`. Establish `h1` using `rightContract_map l π LinearMap.id w`. Rewrite `h1` using `[hπ, map_zero, LinearMap.comp_id]`.

Conclude with `h1.symm`. Rewrite `hle` using `[hU, top_le_iff]`. Conclude with `LinearMap.ker_eq_top.1 hle`.
-/
theorem eigenTensor_full_left_support :
    ∀ (F : Type) [Field F] (E E' Ix : Type) [AddCommGroup E] [Module F E] [AddCommGroup E'] [Module F E'] (Φ : Ix → (E →ₗ[F] E)) (Φ' : Ix → (E' ≃ₗ[F] E')), (∀ U : Submodule F E, (∀ i, ∀ v ∈ U, Φ i v ∈ U) → U = ⊥ ∨ U = ⊤) → ∀ w : TensorProduct F E E', w ≠ 0 → (∀ i, ∃ r : F, TensorProduct.map (Φ i) (Φ' i : E' →ₗ[F] E') w = r • w) → ∀ π : E →ₗ[F] E, TensorProduct.map π (LinearMap.id : E' →ₗ[F] E') w = 0 → π = 0 := by
  intro F _ E E' Ix _ _ _ _ Φ Φ' hirr w hw heig π hπ
  let U : Submodule F E := Submodule.span F (Set.range fun l : E' →ₗ[F] F => rightContract l w)
  have hmem : ∀ l : E' →ₗ[F] F, rightContract l w ∈ U := fun l => Submodule.subset_span ⟨l, rfl⟩
  have hstab : ∀ i, ∀ v ∈ U, Φ i v ∈ U := by
    intro i v hv
    have hle : U ≤ U.comap (Φ i) := by
      apply Submodule.span_le.2
      rintro _ ⟨l, rfl⟩
      obtain ⟨r, hr⟩ := heig i
      have h1 := rightContract_map (l ∘ₗ ((Φ' i).symm : E' →ₗ[F] E')) (Φ i) (Φ' i : E' →ₗ[F] E') w
      have h2 : (l ∘ₗ ((Φ' i).symm : E' →ₗ[F] E')) ∘ₗ (Φ' i : E' →ₗ[F] E') = l := by
        ext y; simp
      rw [h2, hr, map_smul] at h1
      show Φ i (rightContract l w) ∈ U
      rw [← h1]
      exact U.smul_mem _ (hmem _)
    exact hle hv
  rcases hirr U hstab with hU | hU
  · exfalso
    apply hw
    apply eq_zero_of_rightContract
    intro l
    have := hmem l
    rwa [hU, Submodule.mem_bot] at this
  · have hle : U ≤ LinearMap.ker π := by
      apply Submodule.span_le.2
      rintro _ ⟨l, rfl⟩
      have h1 := rightContract_map l π LinearMap.id w
      rw [hπ, map_zero, LinearMap.comp_id] at h1
      exact h1.symm
    rw [hU, top_le_iff] at hle
    exact LinearMap.ker_eq_top.1 hle

end GlobalTheory
