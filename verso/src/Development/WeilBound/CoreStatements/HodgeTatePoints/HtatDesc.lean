import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder

noncomputable section

namespace PositivityTheory.HtPt.Htat

open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

/- English proof (translation)
Introduce `R _ T _ R' _ φ A g`. Set `S : Submonoid (T → R')` to `{ carrier := {g : T → R' | ∃ f ∈ A, g = fun t => φ (f t)} one_mem' := ⟨1, one_mem A, funext fun t => by simp⟩ mul_mem' := by`. Introduce and unpack `_ _ ⟨f, hf, rfl⟩ ⟨f', hf', rfl⟩`. Conclude with `⟨f * f', mul_mem hf hf', funext fun t => by simp⟩ }`. Establish `h` using `Algebra.adjoin_eq_span R' (S : Set (T → R'))`.

Rewrite `h` using `[Submonoid.closure_eq]`. Conclude with `(Subalgebra.mem_toSubmodule _).symm.trans (h ▸ Iff.rfl)`.
-/
theorem ext_span : ∀ (R : Type) [CommRing R] (T : Type) [CommGroup T] (R' : Type) [CommRing R'] (φ : R →+* R') (A : Subalgebra R (T → R)) (g : T → R'), g ∈ extOrder φ A ↔ g ∈ Submodule.span R' {g : T → R' | ∃ f ∈ A, g = fun t => φ (f t)} := by
  intro R _ T _ R' _ φ A g
  let S : Submonoid (T → R') :=
    { carrier := {g : T → R' | ∃ f ∈ A, g = fun t => φ (f t)}
      one_mem' := ⟨1, one_mem A, funext fun t => by simp⟩
      mul_mem' := by
        rintro _ _ ⟨f, hf, rfl⟩ ⟨f', hf', rfl⟩
        exact ⟨f * f', mul_mem hf hf', funext fun t => by simp⟩ }
  have h := Algebra.adjoin_eq_span R' (S : Set (T → R'))
  rw [Submonoid.closure_eq] at h
  exact (Subalgebra.mem_toSubmodule _).symm.trans (h ▸ Iff.rfl)

/- English proof (translation)
Introduce `R _ ι _ N f h`. Set `_` to `Fintype.ofFinite ι`. Set `q : (ι → R) ⧸ N` to `N.mkQ f`. Set `I : Ideal R` to `LinearMap.ker (LinearMap.toSpanSingleton R _ q)`. Assume the negation of the conclusion as `hf`.

Establish `hI : I ≠ ⊤` using `fun hI => hf (by`. Establish `h1 : (1 : R) ∈ I` using `hI ▸ Submodule.mem_top`. Establish `h2 : (1 : R) • q = 0` using `h1`. Rewrite `h2` using `[one_smul]`. Conclude with `(Submodule.Quotient.mk_eq_zero N).1 h2)`.

Take `⟨P, hP, hle⟩` from `Ideal.exists_le_maximal I hI`. Take `⟨R', _, _, _, hflat, hc, hmem⟩` from `h P hP`. Set `ψ : (ι → R') →ₗ[R'] R' ⊗[R] ((ι → R) ⧸ N)` to `(N.mkQ.baseChange R') ∘ₗ (TensorProduct.piScalarRight R R' R' ι).symm.toLinearMap`. Establish `hψ : ∀ n : ι → R, ψ (fun i => algebraMap R R' (n i)) = 1 ⊗ₜ N.mkQ n` using `fun n => by`. Establish `: (TensorProduct.piScalarRight R R' R' ι).symm (fun i => algebraMap R R' (n i)) = 1 ⊗ₜ n`.

Rewrite using `[LinearEquiv.symm_apply_eq]`. Use function extensionality and compare the values at `i`. Simplify using `[Algebra.algebraMap_eq_smul_one]`. Use `show (N.mkQ.baseChange R') ((TensorProduct.piScalarRight R R' R' ι).symm _) = _`. Rewrite using `[this, LinearMap.baseChange_tmul]`.

Establish `h0 : (1 : R') ⊗ₜ[R] q = 0`. Rewrite using `[← hψ]`. Use `(Submodule.span_le (p := LinearMap.ker ψ)).2 ?_ hmem` and prove the remaining obligations. Introduce and unpack `_ ⟨n, hn, rfl⟩`. Use `show ψ _ = 0`.

Rewrite using `[hψ, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).2 hn, tmul_zero]`. Set `g : (R ⧸ I) →ₗ[R] ((ι → R) ⧸ N)` to `I.liftQ (LinearMap.toSpanSingleton R _ q) le_rfl`. Establish `hg : Function.Injective g` using `LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)`. Establish `h1 : (1 : R') ⊗ₜ[R] (Submodule.Quotient.mk 1 : R ⧸ I) = 0`. Apply `Module.Flat.lTensor_preserves_injective_linearMap (M := R') g hg` to reduce the goal to its premises.

Rewrite using `[LinearMap.lTensor_tmul, map_zero, ← h0]`. Use `congr 1`. Conclude with `one_smul R q`. Set `k` to `R' ⧸ IsLocalRing.maximalIdeal R'`. Set `a : (R ⧸ I) →ₗ[R] k` to `I.liftQ (Algebra.linearMap R k) fun r hr => by`.

Establish `: r ∈ (IsLocalRing.maximalIdeal R').comap (algebraMap R R')` using `hc ▸ hle hr`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 this`. Establish `h2` using `congrArg (LinearMap.mul' R k ∘ₗ TensorProduct.map (Ideal.Quotient.mkₐ R (IsLocalRing.maximalIdeal R')).toLinearMap a) h1`. Rewrite `h2` using `[map_zero, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply]`. Establish `h3 : a (Submodule.Quotient.mk 1) = 1` using `map_one (algebraMap R k)`.

Rewrite `h2` using `[h3, mul_one]`. Conclude with `(IsLocalRing.maximalIdeal.isMaximal R').ne_top ((Ideal.eq_top_iff_one _).2 (Ideal.Quotient.eq_zero_iff_mem.1 h2))`.
-/
theorem mem_descent : ∀ (R : Type) [CommRing R] (ι : Type) [Finite ι] (N : Submodule R (ι → R)) (f : ι → R), (∀ P : Ideal R, P.IsMaximal → ∃ (R' : Type) (_ : CommRing R') (_ : IsLocalRing R') (_ : Algebra R R'), Module.Flat R R' ∧ (IsLocalRing.maximalIdeal R').comap (algebraMap R R') = P ∧ (fun i => algebraMap R R' (f i)) ∈ Submodule.span R' {g : ι → R' | ∃ n ∈ N, g = fun i => algebraMap R R' (n i)}) → f ∈ N := by
  intro R _ ι _ N f h
  classical
  let _ := Fintype.ofFinite ι
  let q : (ι → R) ⧸ N := N.mkQ f
  let I : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R _ q)
  by_contra hf
  have hI : I ≠ ⊤ := fun hI => hf (by
    have h1 : (1 : R) ∈ I := hI ▸ Submodule.mem_top
    have h2 : (1 : R) • q = 0 := h1
    rw [one_smul] at h2
    exact (Submodule.Quotient.mk_eq_zero N).1 h2)
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨R', _, _, _, hflat, hc, hmem⟩ := h P hP
  let ψ : (ι → R') →ₗ[R'] R' ⊗[R] ((ι → R) ⧸ N) :=
    (N.mkQ.baseChange R') ∘ₗ (TensorProduct.piScalarRight R R' R' ι).symm.toLinearMap
  have hψ : ∀ n : ι → R, ψ (fun i => algebraMap R R' (n i)) = 1 ⊗ₜ N.mkQ n := fun n => by
    have : (TensorProduct.piScalarRight R R' R' ι).symm (fun i => algebraMap R R' (n i)) = 1 ⊗ₜ n := by
      rw [LinearEquiv.symm_apply_eq]
      funext i
      simp [Algebra.algebraMap_eq_smul_one]
    show (N.mkQ.baseChange R') ((TensorProduct.piScalarRight R R' R' ι).symm _) = _
    rw [this, LinearMap.baseChange_tmul]
  have h0 : (1 : R') ⊗ₜ[R] q = 0 := by
    rw [← hψ]
    refine (Submodule.span_le (p := LinearMap.ker ψ)).2 ?_ hmem
    rintro _ ⟨n, hn, rfl⟩
    show ψ _ = 0
    rw [hψ, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).2 hn, tmul_zero]
  let g : (R ⧸ I) →ₗ[R] ((ι → R) ⧸ N) := I.liftQ (LinearMap.toSpanSingleton R _ q) le_rfl
  have hg : Function.Injective g := LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)
  have h1 : (1 : R') ⊗ₜ[R] (Submodule.Quotient.mk 1 : R ⧸ I) = 0 := by
    apply Module.Flat.lTensor_preserves_injective_linearMap (M := R') g hg
    rw [LinearMap.lTensor_tmul, map_zero, ← h0]
    congr 1
    exact one_smul R q
  let k := R' ⧸ IsLocalRing.maximalIdeal R'
  let a : (R ⧸ I) →ₗ[R] k := I.liftQ (Algebra.linearMap R k) fun r hr => by
    have : r ∈ (IsLocalRing.maximalIdeal R').comap (algebraMap R R') := hc ▸ hle hr
    exact Ideal.Quotient.eq_zero_iff_mem.2 this
  have h2 := congrArg (LinearMap.mul' R k ∘ₗ
    TensorProduct.map (Ideal.Quotient.mkₐ R (IsLocalRing.maximalIdeal R')).toLinearMap a) h1
  rw [map_zero, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply] at h2
  have h3 : a (Submodule.Quotient.mk 1) = 1 := map_one (algebraMap R k)
  rw [h3, mul_one] at h2
  exact (IsLocalRing.maximalIdeal.isMaximal R').ne_top
    ((Ideal.eq_top_iff_one _).2 (Ideal.Quotient.eq_zero_iff_mem.1 h2))

end PositivityTheory.HtPt.Htat
