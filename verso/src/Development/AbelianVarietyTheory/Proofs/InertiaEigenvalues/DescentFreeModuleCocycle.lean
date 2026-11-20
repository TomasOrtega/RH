import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FaithfullyFlatDescentFreeModuleCocycleStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open CategoryTheory

namespace GlobalTheory

/- English proof (translation)
Introduce `A B D T _ _ _ _ _ p q q₁₂ q₂₃ q₁₃ q₃ hff hD hT h1 h2 h3 h4 d ε hε hcoc N hN`. Use `haveI : Module.FaithfullyFlat A B := RingHom.faithfullyFlat_algebraMap_iff.1 hff`. Establish `hTP` using `CommRingCat.isPushout_tensorProduct A B B`. Set `iso` to `hD.isoIsPushout _ _ hTP`. Set `e : D ≃+* B ⊗[A] B` to `iso.commRingCatIsoToRingEquiv`.

Set `ψ : D →+* B ⊗[A] B` to `e.toRingHom`. Establish `hψp : ∀ b, ψ (p b) = b ⊗ₜ[A] (1 : B)` using `fun b => congr($(hD.inl_isoIsPushout_hom _ _ hTP).hom b)`. Establish `hψq : ∀ b, ψ (q b) = (1 : B) ⊗ₜ[A] b` using `fun b => congr($(hD.inr_isoIsPushout_hom _ _ hTP).hom b)`. Set `L : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)` to `Algebra.TensorProduct.map (AlgHom.id A B) (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)`. Set `R : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)` to `(Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B))`.

Set `M : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)` to `Algebra.TensorProduct.map (AlgHom.id A B) (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)`. Set `c3 : B →+* B ⊗[A] (B ⊗[A] B)` to `(R.comp (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)).toRingHom`. Establish `w : CommRingCat.ofHom (algebraMap A B) ≫ CommRingCat.ofHom c3 = CommRingCat.ofHom (p.comp (algebraMap A B)) ≫ CommRingCat.ofHom (S` using `B ⊗[A] (B ⊗[A] B)) (L.toRingHom.comp ψ) := by`. Use extensionality with `a`. Express the relevant statement in the definitionally equal form `c3 (algebraMap A B a) = L (ψ (p (algebraMap A B a)))`.

Rewrite using `[hψp]`. Conclude with `((R.comp Algebra.TensorProduct.includeRight).commutes a).trans ((L.comp (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)).commutes a).symm`. Set `Φ` to `hT.desc _ _ w`. Set `φ : T →+* B ⊗[A] (B ⊗[A] B)` to `Φ.hom`. Establish `hφ3 : ∀ b, φ (q₃ b) = c3 b` using `fun b => congr($(hT.inl_desc _ _ w).hom b)`.

Establish `hφ12 : ∀ x, φ (q₁₂ x) = L (ψ x)` using `fun x => congr($(hT.inr_desc _ _ w).hom x)`. Establish `hext : ∀ {W : CommRingCat} (f g : CommRingCat.of D ⟶ W), (∀ b, f (p b) = g (p b)) → (∀ b, f (q b) = g (q b)) → f = g` using `fun f g hp hq => hD.hom_ext (by ext b; exact hp b) (by ext b; exact hq b)`. Establish `hφ23 : ∀ x, φ (q₂₃ x) = R (ψ x)`. Establish `key` using `hext (CommRingCat.ofHom q₂₃ ≫ Φ) (CommRingCat.ofHom (S := B ⊗[A] (B ⊗[A] B)) (R.toRingHom.comp ψ)) ?_ ?_`. Introduce `x`.

Conclude with `congr($(key).hom x)`. Introduce `b`. Express the relevant statement in the definitionally equal form `φ (q₂₃ (p b)) = R (ψ (p b))`. Rewrite using `[show q₂₃ (p b) = q₁₂ (q b) from congr($h1 b), hφ12, hψq, hψp]`. Simplify using `[L, R]`.

Introduce `b`. Express the relevant statement in the definitionally equal form `φ (q₂₃ (q b)) = R (ψ (q b))`. Rewrite using `[show q₂₃ (q b) = q₃ b from congr($h2 b), hφ3, hψq]`. Simplify using `[c3, R]`. Establish `hφ13 : ∀ x, φ (q₁₃ x) = M (ψ x)`.

Establish `key` using `hext (CommRingCat.ofHom q₁₃ ≫ Φ) (CommRingCat.ofHom (S := B ⊗[A] (B ⊗[A] B)) (M.toRingHom.comp ψ)) ?_ ?_`. Introduce `x`. Conclude with `congr($(key).hom x)`. Introduce `b`. Express the relevant statement in the definitionally equal form `φ (q₁₃ (p b)) = M (ψ (p b))`.

Rewrite using `[show q₁₃ (p b) = q₁₂ (p b) from congr($h3 b), hφ12, hψp]`. Simplify using `[L, M]`. Introduce `b`. Express the relevant statement in the definitionally equal form `φ (q₁₃ (q b)) = M (ψ (q b))`. Rewrite using `[show q₁₃ (q b) = q₃ b from congr($h4 b), hφ3, hψq]`.

Simplify using `[c3, R, M]`. Set `ε' : Matrix (Fin d) (Fin d) (B ⊗[A] B)` to `ε.map ψ`. Establish `hε' : IsUnit ε'` using `hε.map ψ.mapMatrix`. Establish `hcoc' : ε'.map L * ε'.map R = ε'.map M`. Establish `key` using `congrArg φ.mapMatrix hcoc`.

Rewrite `key` using `[map_mul]`. Establish `e12 : φ.mapMatrix (ε.map q₁₂) = ε'.map L`. Use extensionality with `i j`. Simplify using `[ε', hφ12]`. Establish `e23 : φ.mapMatrix (ε.map q₂₃) = ε'.map R`.

Use extensionality with `i j`. Simplify using `[ε', hφ23]`. Establish `e13 : φ.mapMatrix (ε.map q₁₃) = ε'.map M`. Use extensionality with `i j`. Simplify using `[ε', hφ13]`.

Rewrite `key` using `[e12, e23, e13]`. Conclude with `key`. Establish `hN' : ∀ z, z ∈ N ↔ (fun i => z i ⊗ₜ[A] (1 : B)) = ε'.mulVec fun i => (1 : B) ⊗ₜ[A] z i`. Introduce `z`. Rewrite using `[hN z]`.

Establish `hv : (ψ ∘ fun i => q (z i)) = fun i => (1 : B) ⊗ₜ[A] z i` using `funext fun k => hψq _`. Establish `hmv : ∀ i, ψ ((ε.mulVec fun i => q (z i)) i) = (ε'.mulVec fun i => (1 : B) ⊗ₜ[A] z i) i`. Introduce `i`. Rewrite using `[RingHom.map_mulVec, hv]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Use function extensionality and compare the values at `i`. Rewrite using `[← hmv i, ← h, hψp]`. Introduce `h`. Use function extensionality and compare the values at `i`.

Apply `e.injective` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `ψ (p (z i)) = ψ _`. Rewrite using `[hmv i, hψp]`. Conclude with `congrFun h i`. Conclude with `GlobalTheory.T.faithfullyFlat_descent_free_module_cocycle A B d ε' hε' hcoc' N hN'`.
-/
theorem descent_free_cocycle : ∀ (A B D T : Type) [CommRing A] [CommRing B] [CommRing D] [CommRing T] [Algebra A B] (p q : B →+* D) (q₁₂ q₂₃ q₁₃ : D →+* T) (q₃ : B →+* T), (algebraMap A B).FaithfullyFlat → CategoryTheory.IsPushout (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom p) (CommRingCat.ofHom q) → CategoryTheory.IsPushout (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (p.comp (algebraMap A B))) (CommRingCat.ofHom q₃) (CommRingCat.ofHom q₁₂) → q₂₃.comp p = q₁₂.comp q → q₂₃.comp q = q₃ → q₁₃.comp p = q₁₂.comp p → q₁₃.comp q = q₃ → ∀ (d : ℕ) (ε : Matrix (Fin d) (Fin d) D), IsUnit ε → ε.map q₁₂ * ε.map q₂₃ = ε.map q₁₃ → ∀ N : Submodule A (Fin d → B), (∀ z, z ∈ N ↔ (fun i => p (z i)) = ε.mulVec fun i => q (z i)) → Module.Finite A ↥N ∧ Module.Projective A ↥N ∧ IsBaseChange B N.subtype := by
  intro A B D T _ _ _ _ _ p q q₁₂ q₂₃ q₁₃ q₃ hff hD hT h1 h2 h3 h4 d ε hε hcoc N hN
  haveI : Module.FaithfullyFlat A B := RingHom.faithfullyFlat_algebraMap_iff.1 hff
  have hTP := CommRingCat.isPushout_tensorProduct A B B
  let iso := hD.isoIsPushout _ _ hTP
  let e : D ≃+* B ⊗[A] B := iso.commRingCatIsoToRingEquiv
  let ψ : D →+* B ⊗[A] B := e.toRingHom
  have hψp : ∀ b, ψ (p b) = b ⊗ₜ[A] (1 : B) := fun b =>
    congr($(hD.inl_isoIsPushout_hom _ _ hTP).hom b)
  have hψq : ∀ b, ψ (q b) = (1 : B) ⊗ₜ[A] b := fun b =>
    congr($(hD.inr_isoIsPushout_hom _ _ hTP).hom b)
  let L : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B) :=
    Algebra.TensorProduct.map (AlgHom.id A B) (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)
  let R : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B) :=
    (Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B))
  let M : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B) :=
    Algebra.TensorProduct.map (AlgHom.id A B) (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)
  let c3 : B →+* B ⊗[A] (B ⊗[A] B) :=
    (R.comp (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)).toRingHom
  have w : CommRingCat.ofHom (algebraMap A B) ≫ CommRingCat.ofHom c3 =
      CommRingCat.ofHom (p.comp (algebraMap A B)) ≫
        CommRingCat.ofHom (S := B ⊗[A] (B ⊗[A] B)) (L.toRingHom.comp ψ) := by
    ext a
    change c3 (algebraMap A B a) = L (ψ (p (algebraMap A B a)))
    rw [hψp]
    exact ((R.comp Algebra.TensorProduct.includeRight).commutes a).trans
      ((L.comp (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)).commutes a).symm
  let Φ := hT.desc _ _ w
  let φ : T →+* B ⊗[A] (B ⊗[A] B) := Φ.hom
  have hφ3 : ∀ b, φ (q₃ b) = c3 b := fun b => congr($(hT.inl_desc _ _ w).hom b)
  have hφ12 : ∀ x, φ (q₁₂ x) = L (ψ x) := fun x => congr($(hT.inr_desc _ _ w).hom x)
  have hext : ∀ {W : CommRingCat} (f g : CommRingCat.of D ⟶ W), (∀ b, f (p b) = g (p b)) →
      (∀ b, f (q b) = g (q b)) → f = g := fun f g hp hq =>
    hD.hom_ext (by ext b; exact hp b) (by ext b; exact hq b)
  have hφ23 : ∀ x, φ (q₂₃ x) = R (ψ x) := by
    have key := hext (CommRingCat.ofHom q₂₃ ≫ Φ)
      (CommRingCat.ofHom (S := B ⊗[A] (B ⊗[A] B)) (R.toRingHom.comp ψ)) ?_ ?_
    · intro x; exact congr($(key).hom x)
    · intro b
      change φ (q₂₃ (p b)) = R (ψ (p b))
      rw [show q₂₃ (p b) = q₁₂ (q b) from congr($h1 b), hφ12, hψq, hψp]
      simp [L, R]
    · intro b
      change φ (q₂₃ (q b)) = R (ψ (q b))
      rw [show q₂₃ (q b) = q₃ b from congr($h2 b), hφ3, hψq]
      simp [c3, R]
  have hφ13 : ∀ x, φ (q₁₃ x) = M (ψ x) := by
    have key := hext (CommRingCat.ofHom q₁₃ ≫ Φ)
      (CommRingCat.ofHom (S := B ⊗[A] (B ⊗[A] B)) (M.toRingHom.comp ψ)) ?_ ?_
    · intro x; exact congr($(key).hom x)
    · intro b
      change φ (q₁₃ (p b)) = M (ψ (p b))
      rw [show q₁₃ (p b) = q₁₂ (p b) from congr($h3 b), hφ12, hψp]
      simp [L, M]
    · intro b
      change φ (q₁₃ (q b)) = M (ψ (q b))
      rw [show q₁₃ (q b) = q₃ b from congr($h4 b), hφ3, hψq]
      simp [c3, R, M]
  let ε' : Matrix (Fin d) (Fin d) (B ⊗[A] B) := ε.map ψ
  have hε' : IsUnit ε' := hε.map ψ.mapMatrix
  have hcoc' : ε'.map L * ε'.map R = ε'.map M := by
    have key := congrArg φ.mapMatrix hcoc
    rw [map_mul] at key
    have e12 : φ.mapMatrix (ε.map q₁₂) = ε'.map L := by
      ext i j; simp [ε', hφ12]
    have e23 : φ.mapMatrix (ε.map q₂₃) = ε'.map R := by
      ext i j; simp [ε', hφ23]
    have e13 : φ.mapMatrix (ε.map q₁₃) = ε'.map M := by
      ext i j; simp [ε', hφ13]
    rw [e12, e23, e13] at key
    exact key
  have hN' : ∀ z, z ∈ N ↔ (fun i => z i ⊗ₜ[A] (1 : B)) = ε'.mulVec fun i => (1 : B) ⊗ₜ[A] z i := by
    intro z
    rw [hN z]
    have hv : (ψ ∘ fun i => q (z i)) = fun i => (1 : B) ⊗ₜ[A] z i := funext fun k => hψq _
    have hmv : ∀ i, ψ ((ε.mulVec fun i => q (z i)) i) = (ε'.mulVec fun i => (1 : B) ⊗ₜ[A] z i) i := by
      intro i; rw [RingHom.map_mulVec, hv]
    constructor
    · intro h; funext i
      rw [← hmv i, ← h, hψp]
    · intro h; funext i
      apply e.injective
      change ψ (p (z i)) = ψ _
      rw [hmv i, hψp]
      exact congrFun h i
  exact GlobalTheory.T.faithfullyFlat_descent_free_module_cocycle A B d ε' hε' hcoc' N hN'

end GlobalTheory
