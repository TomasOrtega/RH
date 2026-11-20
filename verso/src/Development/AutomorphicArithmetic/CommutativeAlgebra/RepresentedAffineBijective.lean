import Mathlib
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.BothToSecondRelation
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut UpperTheory.Aff

/- English proof (translation)
Rewrite using `[specOf, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc, Iso.inv_hom_id, Category.comp_id]`.
-/
private theorem specOf_appTop {B : Type} [CommRing B] {T : Scheme.{0}} (ψ : B →+* Γ(T, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (specOf ψ).appTop = CommRingCat.ofHom ψ := by
  rw [specOf, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/- English proof (translation)
Establish `h1` using `specOf_appTop ψ`. Rewrite `h1` using `[h, specOf_appTop ψ']`. Conclude with `(congrArg CommRingCat.Hom.hom h1).symm`.
-/
private theorem specOf_injective {B : Type} [CommRing B] {T : Scheme.{0}} {ψ ψ' : B →+* Γ(T, ⊤)}
    (h : specOf ψ = specOf ψ') : ψ = ψ' := by
  have h1 := specOf_appTop ψ
  rw [h, specOf_appTop ψ'] at h1
  exact (congrArg CommRingCat.Hom.hom h1).symm

/- English proof (translation)
Use `⟨((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ g.appTop).hom, ?_⟩` and prove the remaining obligations. Rewrite using `[specOf, CommRingCat.ofHom_hom, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]`.
-/
private theorem specOf_surjective {B : Type} [CommRing B] {T : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of B)) : ∃ ψ : B →+* Γ(T, ⊤), specOf ψ = g := by
  refine ⟨((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ g.appTop).hom, ?_⟩
  rw [specOf, CommRingCat.ofHom_hom, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality,
    Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/- English proof (translation)
Use `Prod.ext (RingHom.ext fun c => ?_) (funext fun j => ?_)` and prove the remaining obligations. Simplify `congrArg (fun φ : MvPolynomial (Fin N) D →+* A => φ (MvPolynomial.C c)) h` using `[ringOf]`. Simplify `congrArg (fun φ : MvPolynomial (Fin N) D →+* A => φ (MvPolynomial.X j)) h` using `[ringOf]`.
-/
private theorem ringOf_injective {D : Type} [CommRing D] {N : ℕ} {A : Type} [CommRing A]
    {x y : (Aff D N).obj A} (h : ringOf x = ringOf y) : x = y := by
  refine Prod.ext (RingHom.ext fun c => ?_) (funext fun j => ?_)
  · simpa [ringOf] using congrArg (fun φ : MvPolynomial (Fin N) D →+* A => φ (MvPolynomial.C c)) h
  · simpa [ringOf] using congrArg (fun φ : MvPolynomial (Fin N) D →+* A => φ (MvPolynomial.X j)) h

/- English proof (translation)
Use `⟨(φ.comp MvPolynomial.C, fun j => φ (MvPolynomial.X j)), ?_⟩` and prove the remaining obligations. Apply the tactic sequence `refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_) <;> simp [ringOf]`.
-/
private theorem ringOf_surjective {D : Type} [CommRing D] {N : ℕ} {A : Type} [CommRing A]
    (φ : MvPolynomial (Fin N) D →+* A) : ∃ x : (Aff D N).obj A, ringOf x = φ := by
  refine ⟨(φ.comp MvPolynomial.C, fun j => φ (MvPolynomial.X j)), ?_⟩
  refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_) <;> simp [ringOf]

/- English proof (translation)
Introduce `D _ N T`. Prove the components needed by the constructor for the conclusion. Introduce `x y h`. Conclude with `ringOf_injective (specOf_injective (show specOf (ringOf x) = specOf (ringOf y) from h))`. Introduce `g`.

Take `⟨ψ, rfl⟩` from `specOf_surjective g`. Take `⟨x, rfl⟩` from `ringOf_surjective ψ`. Conclude with `⟨x, rfl⟩`.
-/
theorem UpperTheory.represented_affine_bijective :
    ∀ (D : Type) [CommRing D] (N : ℕ) (T : Scheme.{0}), Function.Bijective ((repA D N).app (op T)) := by
  intro D _ N T
  constructor
  · intro x y h
    exact ringOf_injective (specOf_injective (show specOf (ringOf x) = specOf (ringOf y) from h))
  · intro g
    obtain ⟨ψ, rfl⟩ := specOf_surjective g
    obtain ⟨x, rfl⟩ := ringOf_surjective ψ
    exact ⟨x, rfl⟩
