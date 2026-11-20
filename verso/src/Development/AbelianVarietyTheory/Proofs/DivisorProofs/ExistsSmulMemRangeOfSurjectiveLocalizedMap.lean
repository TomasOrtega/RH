import Mathlib
open IsLocalRing TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `b`. Use `set L := Localization.AtPrime p`. Use `set N : Submodule R B := LinearMap.range ψ.toLinearMap`. Set `π` to `N.mkQ`. Set `g : L ⊗[R] B →ₗ[R] L ⊗[R] (B ⧸ N)` to `LinearMap.lTensor L π`.

Take `⟨z, hz⟩` from `hs ((1 : L) ⊗ₜ[R] b)`. Establish `key : ∀ w : L ⊗[R] A, g (Algebra.TensorProduct.map (AlgHom.id L L) ψ w) = 0`. Introduce `w`. Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul x y`. Rewrite using `[Algebra.TensorProduct.map_tmul]`. Simplify using `only [g, LinearMap.lTensor_tmul]`. Establish `: π (ψ y) = 0`. Simplify using `only [π, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`.

Conclude with `⟨y, rfl⟩`. Rewrite using `[this, TensorProduct.tmul_zero]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]`. Establish `h0 : (TensorProduct.mk R L (B ⧸ N) 1) (π b) = 0`. Use `key z` as an intermediate fact.

Rewrite `this` using `[hz]`. Simplify `this` using `[g]`. Establish `hloc : IsLocalizedModule p.primeCompl (TensorProduct.mk R L (B ⧸ N) 1)` using `(isLocalizedModule_iff_isBaseChange p.primeCompl L _).mpr (TensorProduct.isBaseChange R _ L)`. Take `⟨s, hs'⟩` from `(IsLocalizedModule.eq_zero_iff p.primeCompl _).mp h0`. Use `⟨s, s.2, ?_⟩` and prove the remaining obligations.

Establish `: π ((s : R) • b) = 0`. Rewrite using `[map_smul]`. Conclude with `hs'`. Simplify using `only [π, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, N] at this`. Take `⟨a, ha⟩` from `this`.

Conclude with `⟨a, ha⟩`.
-/
theorem exists_smul_mem_range_of_surjective_localization_map
    (R A B : Type) [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (p : Ideal R) [p.IsPrime] (ψ : A →ₐ[R] B)
    (hs : Function.Surjective (Algebra.TensorProduct.map
      (AlgHom.id (Localization.AtPrime p) (Localization.AtPrime p)) ψ)) :
    ∀ b : B, ∃ t ∉ p, t • b ∈ ψ.range := by
  intro b
  classical
  set L := Localization.AtPrime p
  set N : Submodule R B := LinearMap.range ψ.toLinearMap
  let π := N.mkQ
  let g : L ⊗[R] B →ₗ[R] L ⊗[R] (B ⧸ N) := LinearMap.lTensor L π
  obtain ⟨z, hz⟩ := hs ((1 : L) ⊗ₜ[R] b)
  have key : ∀ w : L ⊗[R] A, g (Algebra.TensorProduct.map
      (AlgHom.id L L) ψ w) = 0 := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      rw [Algebra.TensorProduct.map_tmul]
      simp only [g, LinearMap.lTensor_tmul]
      have : π (ψ y) = 0 := by
        simp only [π, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact ⟨y, rfl⟩
      rw [this, TensorProduct.tmul_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  have h0 : (TensorProduct.mk R L (B ⧸ N) 1) (π b) = 0 := by
    have := key z
    rw [hz] at this
    simpa [g] using this
  have hloc : IsLocalizedModule p.primeCompl (TensorProduct.mk R L (B ⧸ N) 1) :=
    (isLocalizedModule_iff_isBaseChange p.primeCompl L _).mpr (TensorProduct.isBaseChange R _ L)
  obtain ⟨s, hs'⟩ := (IsLocalizedModule.eq_zero_iff p.primeCompl _).mp h0
  refine ⟨s, s.2, ?_⟩
  have : π ((s : R) • b) = 0 := by
    rw [map_smul]; exact hs'
  simp only [π, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, N] at this
  obtain ⟨a, ha⟩ := this
  exact ⟨a, ha⟩

end GlobalTheory
