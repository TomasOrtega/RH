import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem

noncomputable section

namespace GlobalTheory.UnitLemma.Orbit

open GlobalTheory.UnitLemma

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.
-/
theorem coe_mulLat_of_coe_eq {O O' A : Type} [CommRing O] [CommRing O'] [CommRing A] [Algebra O A]
    [Algebra O' A] (L : Submodule O A) (L' : Submodule O' A) (h : (L' : Set A) = L) (t : Aˣ) :
    (mulLat O' (t : A) L' : Set A) = mulLat O (t : A) L := by
  ext y
  rw [SetLike.mem_coe, SetLike.mem_coe, mem_mulLat, mem_mulLat, ← SetLike.mem_coe, h, SetLike.mem_coe]

/- English proof (translation)
By extensionality, compare the relevant components. Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules.
-/
theorem stabLat_of_coe_eq {O O' A : Type} [CommRing O] [CommRing O'] [CommRing A] [Algebra O A]
    [Algebra O' A] (L : Submodule O A) (L' : Submodule O' A) (h : (L' : Set A) = L) :
    stabLat O' L' = stabLat O L := by
  ext t
  change (∀ y, y ∈ L' ↔ (t : A) * y ∈ L') ↔ ∀ y, y ∈ L ↔ (t : A) * y ∈ L
  simp only [← SetLike.mem_coe, h]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact.

Introduce a local definition for the expression. Introduce a local definition for the expression. Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Proceed by induction.

Treat this case separately. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem orbSum_congr_coe {O O' A : Type} [CommRing O] [CommRing O'] [CommRing A] [Algebra O A] [Algebra O' A]
    (G : Subgroup Aˣ) (X : Set (Submodule O A)) (X' : Set (Submodule O' A))
    (hX : ∀ L ∈ X, ∃ L' ∈ X', (L' : Set A) = L) (hX' : ∀ L' ∈ X', ∃ L ∈ X, (L : Set A) = L')
    (hG : intUnits O A ⊓ G = intUnits O' A ⊓ G) :
    orbSum O' G X' (fun _ => 1) = orbSum O G X (fun _ => 1) := by
  classical
  rw [orbSum_eq, orbSum_eq]
  let f : X → X' := fun L => ⟨Classical.choose (hX L.1 L.2), (Classical.choose_spec (hX L.1 L.2)).1⟩
  have hf : ∀ L : X, ((f L).1 : Set A) = L.1 := fun L => (Classical.choose_spec (hX L.1 L.2)).2
  let g : X' → X := fun L => ⟨Classical.choose (hX' L.1 L.2), (Classical.choose_spec (hX' L.1 L.2)).1⟩
  have hg : ∀ L : X', ((g L).1 : Set A) = L.1 := fun L => (Classical.choose_spec (hX' L.1 L.2)).2
  let e : X ≃ X' :=
    { toFun := f
      invFun := g
      left_inv := fun L => Subtype.ext (SetLike.coe_injective (by rw [hg, hf]))
      right_inv := fun L => Subtype.ext (SetLike.coe_injective (by rw [hf, hg])) }
  let q : Orb O G X ≃ Orb O' G X' := Quot.congr e (by
    intro L M
    constructor
    · rintro ⟨t, ht, h⟩
      refine ⟨t, ht, SetLike.coe_injective ?_⟩
      change ((f M).1 : Set A) = (mulLat O' (t : A) (f L).1 : Set A)
      rw [hf M, coe_mulLat_of_coe_eq L.1 (f L).1 (hf L) t, h]
    · rintro ⟨t, ht, h⟩
      refine ⟨t, ht, SetLike.coe_injective ?_⟩
      have h' : ((f M).1 : Set A) = (mulLat O' (t : A) (f L).1 : Set A) := congrArg SetLike.coe h
      rw [hf M, coe_mulLat_of_coe_eq L.1 (f L).1 (hf L) t] at h'
      exact h')
  rw [← finsum_comp_equiv q]
  refine finsum_congr fun o => ?_
  induction o using Quot.ind with
  | mk L =>
    change (((stabLat O' (f L).1 ⊓ G).relIndex (intUnits O' A ⊓ G) : ℕ) : ℚ) =
      (((stabLat O L.1 ⊓ G).relIndex (intUnits O A ⊓ G) : ℕ) : ℚ)
    rw [stabLat_of_coe_eq L.1 (f L).1 (hf L), hG]

end GlobalTheory.UnitLemma.Orbit
