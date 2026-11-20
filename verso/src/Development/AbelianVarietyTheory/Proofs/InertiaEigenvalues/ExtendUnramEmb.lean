import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

/- English proof (translation)
Introduce `l _ K LL hK e`. Establish `hsurj : Function.Surjective (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)`. Introduce `y`. Use `⟨⟨y.1, ⟨y.2, hK y.2⟩⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises.

Both sides reduce to the same expression. Set `φ : ↥(K0 K) ≃ₐ[ℚ_[l]] ↥K.1` to `AlgEquiv.ofBijective (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) ⟨(IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1).toRingHom.injective, hsurj⟩`. Use `⟨e.comp φ.symm.toAlgHom, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Establish `: φ.symm (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1 x) = x` using `φ.symm_apply_apply x`.

Simplify using `only [AlgHom.comp_apply]`. Conclude with `congrArg (fun z => ((e z : ↥LL.1) : Om l)) this`. Introduce `τ' hτ'`. Use extensionality with `y`. Take `⟨x, rfl⟩` from `hsurj y`.

Establish `h1` using `congrArg (fun f : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1 => f x) hτ'`. Simplify using `only [AlgHom.comp_apply] at h1`. Rewrite using `[h1]`. Simplify using `only [AlgHom.comp_apply]`. Establish `: φ.symm (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1 x) = x` using `φ.symm_apply_apply x`.

Conclude with `(congrArg (fun z => ((e z : ↥LL.1) : Om l)) this).symm`.
-/
theorem GlobalTheory.UseLoc.extendUnramEmb : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), K.1 ≤ MaximalUnramifiedExtension l → ∀ e : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1, ∃ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) = e ∧ ∀ τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, τ'.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) = e → τ' = τ := by
  intro l _ K LL hK e
  have hsurj : Function.Surjective (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) := by
    intro y
    refine ⟨⟨y.1, ⟨y.2, hK y.2⟩⟩, ?_⟩
    apply Subtype.ext
    rfl
  let φ : ↥(K0 K) ≃ₐ[ℚ_[l]] ↥K.1 :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)
      ⟨(IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1).toRingHom.injective, hsurj⟩
  refine ⟨e.comp φ.symm.toAlgHom, ?_, ?_⟩
  · ext x
    have : φ.symm (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1 x) = x := φ.symm_apply_apply x
    simp only [AlgHom.comp_apply]
    exact congrArg (fun z => ((e z : ↥LL.1) : Om l)) this
  · intro τ' hτ'
    ext y
    obtain ⟨x, rfl⟩ := hsurj y
    have h1 := congrArg (fun f : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1 => f x) hτ'
    simp only [AlgHom.comp_apply] at h1
    rw [h1]
    simp only [AlgHom.comp_apply]
    have : φ.symm (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1 x) = x := φ.symm_apply_apply x
    exact (congrArg (fun z => ((e z : ↥LL.1) : Om l)) this).symm
