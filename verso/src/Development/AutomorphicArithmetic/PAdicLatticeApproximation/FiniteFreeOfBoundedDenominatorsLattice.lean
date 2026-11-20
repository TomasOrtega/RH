import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.WitSys
open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

/- English proof (translation)
Establish `hf : Function.Injective (Algebra.linearMap ℤ ℚ)` using `fun a b h => by simpa using h`. Establish `h` using `Module.Flat.rTensor_preserves_injective_linearMap (M := L) (Algebra.linearMap ℤ ℚ) hf`. Introduce `x y hxy`. Apply `(TensorProduct.lid ℤ L).symm.injective` to reduce the goal to its premises. Apply `h` to reduce the goal to its premises.

Simplify `hxy` using `[LinearMap.rTensor_tmul]`.
-/
private theorem UpperTheory.tensor_rat_injective_of_free {L : Type} [AddCommGroup L] [Module.Free ℤ L] :
    Function.Injective (TensorProduct.mk ℤ ℚ L (1 : ℚ)) := by
  have hf : Function.Injective (Algebra.linearMap ℤ ℚ) :=
    fun a b h => by simpa using h
  have h := Module.Flat.rTensor_preserves_injective_linearMap (M := L) (Algebra.linearMap ℤ ℚ) hf
  intro x y hxy
  apply (TensorProduct.lid ℤ L).symm.injective
  apply h
  simpa [LinearMap.rTensor_tmul] using hxy

/- English proof (translation)
Introduce `p _ D X ⟨d, hd, h⟩`. Use `haveI := D.freeLa`. Use `haveI := D.finLa`. Set `ι : D.La →ₗ[ℤ] VQ D` to `TensorProduct.mk ℤ ℚ D.La (1 : ℚ)`. Establish `hι : Function.Injective ι` using `UpperTheory.tensor_rat_injective_of_free`.

Set `g : X.lat →ₗ[ℤ] VQ D` to `(d : ℤ) • (X.lat.toIntSubmodule.subtype)`. Establish `hg : Function.Injective g`. Introduce `u v huv`. Establish `h1 : (d : ℤ) • (u : VQ D) = (d : ℤ) • (v : VQ D)` using `huv`. Establish `hq : ((d : ℚ)) • (u : VQ D) = (d : ℚ) • (v : VQ D)`.

Simplify `h1` using `[Nat.cast_smul_eq_nsmul]`. Establish `hd0 : (d : ℚ) ≠ 0` using `by exact_mod_cast hd.ne'`. Conclude with `Subtype.ext (smul_right_injective _ hd0 hq)`. Establish `hr : ∀ w, g w ∈ LinearMap.range ι`. Introduce `w`.

Take `⟨a, ha⟩` from `h w w.2`. Use `⟨a, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(1 : ℚ) ⊗ₜ[ℤ] a = (d : ℤ) • (w : VQ D)`. Rewrite using `[← ha]`. Conclude with `(natCast_zsmul (w : VQ D) d).symm`.

Set `f : X.lat →ₗ[ℤ] D.La` to `(LinearEquiv.ofInjective ι hι).symm.toLinearMap ∘ₗ g.codRestrict (LinearMap.range ι) hr`. Establish `hf : Function.Injective f`. Introduce `u v huv`. Apply `hg` to reduce the goal to its premises. Use `(LinearEquiv.ofInjective ι hι).symm.injective huv` as an intermediate fact.

Conclude with `congrArg Subtype.val this`. Use `⟨Module.Finite.of_injective f hf, ?_⟩` and prove the remaining obligations. Conclude with `Module.Free.of_equiv (LinearEquiv.ofInjective f hf).symm`.
-/
theorem UpperTheory.finite_free_of_bounded_denominators_lattice :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (X : UpperTheory.Gal.W2.Wit.Sys D), (∃ d : ℕ, 0 < d ∧ ∀ w ∈ X.lat, ∃ a : D.La, d • w = (1 : ℚ) ⊗ₜ[ℤ] a) → Module.Finite ℤ X.lat ∧ Module.Free ℤ X.lat := by
  intro p _ D X ⟨d, hd, h⟩
  haveI := D.freeLa
  haveI := D.finLa
  let ι : D.La →ₗ[ℤ] VQ D := TensorProduct.mk ℤ ℚ D.La (1 : ℚ)
  have hι : Function.Injective ι := UpperTheory.tensor_rat_injective_of_free
  let g : X.lat →ₗ[ℤ] VQ D := (d : ℤ) • (X.lat.toIntSubmodule.subtype)
  have hg : Function.Injective g := by
    intro u v huv
    have h1 : (d : ℤ) • (u : VQ D) = (d : ℤ) • (v : VQ D) := huv
    have hq : ((d : ℚ)) • (u : VQ D) = (d : ℚ) • (v : VQ D) := by
      simpa [Nat.cast_smul_eq_nsmul] using h1
    have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    exact Subtype.ext (smul_right_injective _ hd0 hq)
  have hr : ∀ w, g w ∈ LinearMap.range ι := by
    intro w
    obtain ⟨a, ha⟩ := h w w.2
    refine ⟨a, ?_⟩
    change (1 : ℚ) ⊗ₜ[ℤ] a = (d : ℤ) • (w : VQ D)
    rw [← ha]
    exact (natCast_zsmul (w : VQ D) d).symm
  let f : X.lat →ₗ[ℤ] D.La :=
    (LinearEquiv.ofInjective ι hι).symm.toLinearMap ∘ₗ g.codRestrict (LinearMap.range ι) hr
  have hf : Function.Injective f := by
    intro u v huv
    apply hg
    have := (LinearEquiv.ofInjective ι hι).symm.injective huv
    exact congrArg Subtype.val this
  refine ⟨Module.Finite.of_injective f hf, ?_⟩
  exact Module.Free.of_equiv (LinearEquiv.ofInjective f hf).symm
