import Mathlib
open TensorProduct

namespace GlobalTheory

/- English proof (translation)
Use `set C := Algebra.adjoin R ((algebraMap S B) '' (S' : Set S) ∪ Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b))) with hC`. Use `letI : Algebra A₀ S' := (Subalgebra.inclusion h).toRingHom.toAlgebra`. Set `ι : S' →ₐ[A₀] S` to `{ toRingHom := S'.val.toRingHom commutes' := fun _ => rfl }`. Set `Φ : S' ⊗[A₀] B₀ →ₐ[A₀] S ⊗[A₀] B₀` to `Algebra.TensorProduct.map ι (AlgHom.id A₀ B₀)`. Set `Ψ : S' ⊗[A₀] B₀ →+* B` to `(e.symm : S ⊗[A₀] B₀ →+* B).comp Φ.toRingHom`.

Use `haveI : Module.Flat A₀ B₀ := inferInstance`. Establish `hΦ : Function.Injective Φ`. Establish `hl : (Φ.toLinearMap : S' ⊗[A₀] B₀ →ₗ[A₀] S ⊗[A₀] B₀) = LinearMap.rTensor B₀ ι.toLinearMap`. Apply `TensorProduct.ext'` to reduce the goal to its premises. Introduce `x y`.

Both sides reduce to the same expression. Establish `: Function.Injective (LinearMap.rTensor B₀ ι.toLinearMap)` using `Module.Flat.rTensor_preserves_injective_linearMap _ (fun a b hab => Subtype.ext hab)`. Rewrite `this` using `[← hl]`. Conclude with `this`. Establish `hΨ : Function.Injective Ψ` using `e.symm.injective.comp hΦ`.

Establish `htmul : ∀ (s : S') (b : B₀), Ψ (s ⊗ₜ b) = algebraMap S B s * e.symm (1 ⊗ₜ b)`. Introduce `s b`. Establish `: ((s : S) ⊗ₜ[A₀] b : S ⊗[A₀] B₀) = algebraMap S (S ⊗[A₀] B₀) s * (1 ⊗ₜ b)`. Simplify using `[Algebra.TensorProduct.algebraMap_apply]`. Use `show e.symm ((s : S) ⊗ₜ[A₀] b) = _`.

Rewrite using `[this, map_mul, AlgEquiv.commutes]`. Establish `h1 : e.symm ((1 : S) ⊗ₜ[A₀] (1 : B₀)) = 1`. Rewrite using `[← Algebra.TensorProduct.one_def, map_one]`. Establish `hsub : ∀ x, Ψ x ∈ C`. Introduce `x`.

Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul s b`. Rewrite using `[htmul]`. Conclude with `C.mul_mem (Algebra.subset_adjoin (Or.inl ⟨s, s.2, rfl⟩)) (Algebra.subset_adjoin (Or.inr ⟨b, rfl⟩))`.

Consider the case `add x y hx hy => rw [map_add]`. Conclude with `C.add_mem hx hy`. Establish `hsurj : (C : Set B) ⊆ Set.range Ψ`. Use `Algebra.adjoin_eq_ring_closure (R := R) ((algebraMap S B) '' (S' : Set S) ∪ Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b)))` as an intermediate fact. Introduce `y hy`.

Establish `hy' : y ∈ (C.toSubring)` using `hy`. Rewrite `hy'` using `[hC, this]`. Establish `hle : Subring.closure (Set.range (algebraMap R B) ∪ ((algebraMap S B) '' (S' : Set S) ∪ Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b)))) ≤ Ψ.range`. Rewrite using `[Subring.closure_le]`. Introduce and unpack `z (⟨r, rfl⟩ | ⟨s, hs, rfl⟩ | ⟨b, rfl⟩)`.

Use `⟨(algebraMap R S' r) ⊗ₜ 1, ?_⟩` and prove the remaining obligations. Rewrite using `[htmul, h1, mul_one, IsScalarTower.algebraMap_apply R S B]`. Both sides reduce to the same expression. Use `⟨(⟨s, hs⟩ : S') ⊗ₜ 1, ?_⟩` and prove the remaining obligations. Rewrite using `[htmul, h1, mul_one]`.

Use `⟨1 ⊗ₜ b, ?_⟩` and prove the remaining obligations. Rewrite using `[htmul]`. Simplify using the standard rewrite rules. Conclude with `hle hy'`. Set `f : S' ⊗[A₀] B₀ →+* C` to `Ψ.codRestrict C.toSubring hsub`.

Establish `hf : Function.Bijective f`. Use `⟨fun x y hxy => hΨ (congrArg Subtype.val hxy), ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨y, hy⟩`. Take `⟨x, rfl⟩` from `hsurj hy`. Conclude with `⟨x, rfl⟩`.

Set `eqv : S' ⊗[A₀] B₀ ≃+* C` to `RingEquiv.ofBijective f hf`. Use `letI alg : Algebra S' C := (f.comp (algebraMap S' (S' ⊗[A₀] B₀))).toAlgebra`. Establish `tower : IsScalarTower R S' C`. Use `IsScalarTower.of_algebraMap_eq (fun r => ?_)` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show algebraMap R B r = Ψ (algebraMap S' (S' ⊗[A₀] B₀) (algebraMap R S' r))`. Rewrite using `[Algebra.TensorProduct.algebraMap_apply, htmul, h1, mul_one, IsScalarTower.algebraMap_apply R S B]`. Both sides reduce to the same expression. Use `⟨alg, tower, ?_⟩` and prove the remaining obligations. Set `eA : S' ⊗[A₀] B₀ ≃ₐ[S'] C` to `AlgEquiv.ofRingEquiv (f := eqv) (fun _ => rfl)`.

Use `haveI : Algebra.Etale S' (S' ⊗[A₀] B₀) := Algebra.Etale.baseChange A₀ B₀ S'`. Conclude with `Algebra.Etale.of_equiv eA`.
-/
theorem etale_adjoin_baseChange_image (R S B : Type) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra S B] [Algebra R B] [IsScalarTower R S B] (A₀ : Subalgebra R S)
    (B₀ : Type) [CommRing B₀] [Algebra A₀ B₀] [Algebra.Etale A₀ B₀] (e : B ≃ₐ[S] S ⊗[A₀] B₀)
    (S' : Subalgebra R S) (h : A₀ ≤ S') :
    ∃ (_ : Algebra S' ↥(Algebra.adjoin R ((algebraMap S B) '' (S' : Set S) ∪
        Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b)))))
      (_ : IsScalarTower R S' ↥(Algebra.adjoin R ((algebraMap S B) '' (S' : Set S) ∪
        Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b))))),
      Algebra.Etale S' ↥(Algebra.adjoin R ((algebraMap S B) '' (S' : Set S) ∪
        Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b)))) := by
  set C := Algebra.adjoin R ((algebraMap S B) '' (S' : Set S) ∪
        Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b))) with hC
  letI : Algebra A₀ S' := (Subalgebra.inclusion h).toRingHom.toAlgebra
  let ι : S' →ₐ[A₀] S :=
    { toRingHom := S'.val.toRingHom
      commutes' := fun _ => rfl }
  let Φ : S' ⊗[A₀] B₀ →ₐ[A₀] S ⊗[A₀] B₀ := Algebra.TensorProduct.map ι (AlgHom.id A₀ B₀)
  let Ψ : S' ⊗[A₀] B₀ →+* B := (e.symm : S ⊗[A₀] B₀ →+* B).comp Φ.toRingHom
  haveI : Module.Flat A₀ B₀ := inferInstance
  have hΦ : Function.Injective Φ := by
    have hl : (Φ.toLinearMap : S' ⊗[A₀] B₀ →ₗ[A₀] S ⊗[A₀] B₀) = LinearMap.rTensor B₀ ι.toLinearMap := by
      apply TensorProduct.ext'
      intro x y
      rfl
    have : Function.Injective (LinearMap.rTensor B₀ ι.toLinearMap) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (fun a b hab => Subtype.ext hab)
    rw [← hl] at this
    exact this
  have hΨ : Function.Injective Ψ := e.symm.injective.comp hΦ
  have htmul : ∀ (s : S') (b : B₀), Ψ (s ⊗ₜ b) = algebraMap S B s * e.symm (1 ⊗ₜ b) := by
    intro s b
    have : ((s : S) ⊗ₜ[A₀] b : S ⊗[A₀] B₀) = algebraMap S (S ⊗[A₀] B₀) s * (1 ⊗ₜ b) := by
      simp [Algebra.TensorProduct.algebraMap_apply]
    show e.symm ((s : S) ⊗ₜ[A₀] b) = _
    rw [this, map_mul, AlgEquiv.commutes]
  have h1 : e.symm ((1 : S) ⊗ₜ[A₀] (1 : B₀)) = 1 := by
    rw [← Algebra.TensorProduct.one_def, map_one]
  have hsub : ∀ x, Ψ x ∈ C := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s b =>
      rw [htmul]
      exact C.mul_mem (Algebra.subset_adjoin (Or.inl ⟨s, s.2, rfl⟩))
        (Algebra.subset_adjoin (Or.inr ⟨b, rfl⟩))
    | add x y hx hy => rw [map_add]; exact C.add_mem hx hy
  have hsurj : (C : Set B) ⊆ Set.range Ψ := by
    have := Algebra.adjoin_eq_ring_closure (R := R)
      ((algebraMap S B) '' (S' : Set S) ∪ Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b)))
    intro y hy
    have hy' : y ∈ (C.toSubring) := hy
    rw [hC, this] at hy'
    have hle : Subring.closure (Set.range (algebraMap R B) ∪
        ((algebraMap S B) '' (S' : Set S) ∪ Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b))))
        ≤ Ψ.range := by
      rw [Subring.closure_le]
      rintro z (⟨r, rfl⟩ | ⟨s, hs, rfl⟩ | ⟨b, rfl⟩)
      · refine ⟨(algebraMap R S' r) ⊗ₜ 1, ?_⟩
        rw [htmul, h1, mul_one, IsScalarTower.algebraMap_apply R S B]
        rfl
      · refine ⟨(⟨s, hs⟩ : S') ⊗ₜ 1, ?_⟩
        rw [htmul, h1, mul_one]
      · refine ⟨1 ⊗ₜ b, ?_⟩
        rw [htmul]; simp
    exact hle hy'
  let f : S' ⊗[A₀] B₀ →+* C := Ψ.codRestrict C.toSubring hsub
  have hf : Function.Bijective f := by
    refine ⟨fun x y hxy => hΨ (congrArg Subtype.val hxy), ?_⟩
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hsurj hy
    exact ⟨x, rfl⟩
  let eqv : S' ⊗[A₀] B₀ ≃+* C := RingEquiv.ofBijective f hf
  letI alg : Algebra S' C := (f.comp (algebraMap S' (S' ⊗[A₀] B₀))).toAlgebra
  have tower : IsScalarTower R S' C := by
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    apply Subtype.ext
    show algebraMap R B r = Ψ (algebraMap S' (S' ⊗[A₀] B₀) (algebraMap R S' r))
    rw [Algebra.TensorProduct.algebraMap_apply, htmul, h1, mul_one,
      IsScalarTower.algebraMap_apply R S B]
    rfl
  refine ⟨alg, tower, ?_⟩
  let eA : S' ⊗[A₀] B₀ ≃ₐ[S'] C := AlgEquiv.ofRingEquiv (f := eqv) (fun _ => rfl)
  haveI : Algebra.Etale S' (S' ⊗[A₀] B₀) := Algebra.Etale.baseChange A₀ B₀ S'
  exact Algebra.Etale.of_equiv eA

end GlobalTheory
