import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLtTopOfEssFiniteType
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.HInvIso

/- English proof (translation)
Simplify using `only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]`.
-/
theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

/- English proof (translation)
Simplify using `only [spMap, CommRingCat.ofHom_id, Spec.map_id]`. Conclude with `CategoryTheory.Functor.map_id _ _`.
-/
theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]
  exact CategoryTheory.Functor.map_id _ _

/- English proof (translation)
Establish `h1 : ∀ x, pull R (spMap (e : A →+* B)) F n (pull R (spMap (e.symm : B →+* A)) F n x) = x`. Introduce `x`. Rewrite using `[← pull_comp, ← spMap_comp']`. Establish `: (e : A →+* B).comp (e.symm : B →+* A) = RingHom.id B` using `by ext a; simp`. Rewrite using `[this, spMap_id', pull_id]`.

Establish `h2 : ∀ x, pull R (spMap (e.symm : B →+* A)) F n (pull R (spMap (e : A →+* B)) F n x) = x`. Introduce `x`. Rewrite using `[← pull_comp, ← spMap_comp']`. Establish `: (e.symm : B →+* A).comp (e : A →+* B) = RingHom.id A` using `by ext a; simp`. Rewrite using `[this, spMap_id', pull_id]`.

Conclude with `⟨Function.LeftInverse.injective h2, Function.RightInverse.surjective h1⟩`.
-/
theorem pull_spMap_bij {R : Type} [CommRing R] {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) (F : Shv R) (n : ℤ) :
    Function.Bijective (pull R (spMap (e : A →+* B)) F n) := by
  have h1 : ∀ x, pull R (spMap (e : A →+* B)) F n (pull R (spMap (e.symm : B →+* A)) F n x) = x := by
    intro x
    rw [← pull_comp, ← spMap_comp']
    have : (e : A →+* B).comp (e.symm : B →+* A) = RingHom.id B := by ext a; simp
    rw [this, spMap_id', pull_id]
  have h2 : ∀ x, pull R (spMap (e.symm : B →+* A)) F n (pull R (spMap (e : A →+* B)) F n x) = x := by
    intro x
    rw [← pull_comp, ← spMap_comp']
    have : (e.symm : B →+* A).comp (e : A →+* B) = RingHom.id A := by ext a; simp
    rw [this, spMap_id', pull_id]
  exact ⟨Function.LeftInverse.injective h2, Function.RightInverse.surjective h1⟩

end GlobalTheory.EtC.HInvIso

namespace GlobalTheory.EtC

open HInvIso in

/- English proof (translation)
Introduce `q _ A B _ _ e hA i n`. Establish `hsq : (Polynomial.C : B →+* Polynomial B).comp (e : A →+* B) = ((Polynomial.mapEquiv e : Polynomial A ≃+* Polynomial B) : Polynomial A →+* Polynomial B).comp Polynomial.C`. Use extensionality with `a`. Simplify using the standard rewrite rules. Establish `hpull : ∀ x, pull (ZMod q) (spMap (Polynomial.C : B →+* Polynomial B)) (tw q i) n (pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n x) = pull (ZMod q) (spMap ((Polynomial.mapEquiv e : Polynomial A ≃+* Polynomial B) : Polynomial A →+* Polynomial B)) (tw q i) n (pull (ZMod q) (spMap …`.

Introduce `x`. Rewrite using `[← pull_comp, ← pull_comp, ← spMap_comp', ← spMap_comp', hsq]`. Establish `hc : Function.Bijective ((pull (ZMod q) (spMap (Polynomial.C : B →+* Polynomial B)) (tw q i) n) ∘ (pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n))`. Establish `: ((pull (ZMod q) (spMap (Polynomial.C : B →+* Polynomial B)) (tw q i) n) ∘ (pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n)) = (pull (ZMod q) (spMap ((Polynomial.mapEquiv e : Polynomial A ≃+* Polynomial B) : Polynomial A →+* Polynomial B)) (tw q i) n) ∘ (pull (ZMod q) (spMap (Po …` using `funext hpull`. Rewrite using `[this]`.

Conclude with `(pull_spMap_bij _ _ n).comp (hA i n)`. Conclude with `(Function.Bijective.of_comp_iff _ (pull_spMap_bij e _ n)).1 hc`.
-/
theorem hInv_of_ringEquiv : ∀ (q : ℕ) [NeZero q] (A B : Type) [CommRing A] [CommRing B], (A ≃+* B) → HInv q A → HInv q B := by
  intro q _ A B _ _ e hA i n
  have hsq : (Polynomial.C : B →+* Polynomial B).comp (e : A →+* B) =
      ((Polynomial.mapEquiv e : Polynomial A ≃+* Polynomial B) : Polynomial A →+* Polynomial B).comp Polynomial.C := by
    ext a; simp
  have hpull : ∀ x, pull (ZMod q) (spMap (Polynomial.C : B →+* Polynomial B)) (tw q i) n
      (pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n x) =
      pull (ZMod q) (spMap ((Polynomial.mapEquiv e : Polynomial A ≃+* Polynomial B) : Polynomial A →+* Polynomial B)) (tw q i) n
        (pull (ZMod q) (spMap (Polynomial.C : A →+* Polynomial A)) (tw q i) n x) := by
    intro x
    rw [← pull_comp, ← pull_comp, ← spMap_comp', ← spMap_comp', hsq]
  have hc : Function.Bijective ((pull (ZMod q) (spMap (Polynomial.C : B →+* Polynomial B)) (tw q i) n) ∘
      (pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n)) := by
    have : ((pull (ZMod q) (spMap (Polynomial.C : B →+* Polynomial B)) (tw q i) n) ∘
      (pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n)) =
      (pull (ZMod q) (spMap ((Polynomial.mapEquiv e : Polynomial A ≃+* Polynomial B) : Polynomial A →+* Polynomial B)) (tw q i) n) ∘
        (pull (ZMod q) (spMap (Polynomial.C : A →+* Polynomial A)) (tw q i) n) := funext hpull
    rw [this]
    exact (pull_spMap_bij _ _ n).comp (hA i n)
  exact (Function.Bijective.of_comp_iff _ (pull_spMap_bij e _ n)).1 hc

end GlobalTheory.EtC
