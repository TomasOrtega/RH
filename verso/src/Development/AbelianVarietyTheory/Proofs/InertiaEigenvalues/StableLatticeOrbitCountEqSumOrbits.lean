import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComapInlMemStLat
open GlobalTheory.UnitLemma Polynomial

noncomputable section

namespace GlobalTheory.UnitLemma

section Bridge

variable {O E A : Type} [CommRing O] [Field E] [CommRing A] [Algebra O A] [Algebra E A]

/- English proof (translation)
Use extensionality with `t`. Rewrite using `[MulAction.mem_stabilizer_iff, Subtype.ext_iff, stLat_smul_val]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use extensionality with `x`.

Rewrite using `[mem_mulLat_iff]`. Use `h (((t⁻¹ : Aˣ) : A) * x)` as an intermediate fact. Rewrite `this` using `[← mul_assoc, Units.mul_inv, one_mul]`. Conclude with `this`. Introduce `h y`.

Use `SetLike.ext_iff.mp h ((t : A) * y)` as an intermediate fact. Rewrite `this` using `[mem_mulLat_iff, ← mul_assoc, Units.inv_mul, one_mul]`. Conclude with `this`.
-/
theorem stabLat_eq_stabilizer (g : A) (L : stLat O E g) :
    stabLat O (L : Submodule O A) = MulAction.stabilizer Aˣ L := by
  ext t
  rw [MulAction.mem_stabilizer_iff, Subtype.ext_iff, stLat_smul_val]
  constructor
  · intro h
    ext x
    rw [mem_mulLat_iff]
    have := h (((t⁻¹ : Aˣ) : A) * x)
    rw [← mul_assoc, Units.mul_inv, one_mul] at this
    exact this
  · intro h y
    have := SetLike.ext_iff.mp h ((t : A) * y)
    rw [mem_mulLat_iff, ← mul_assoc, Units.inv_mul, one_mul] at this
    exact this

def orbEquiv (g : A) : Orb O (⊤ : Subgroup Aˣ) (stLat O E g) ≃ MulAction.orbitRel.Quotient Aˣ (stLat O E g) where
  toFun := Quot.lift (fun L => (Quotient.mk _ L : MulAction.orbitRel.Quotient Aˣ (stLat O E g)))
    (by
      rintro L M ⟨t, -, h⟩
      exact (Quotient.sound (show M ∈ MulAction.orbit Aˣ L from ⟨t, Subtype.ext (by rw [stLat_smul_val]; exact h.symm)⟩)).symm)
  invFun := Quotient.lift (fun L => (Quot.mk _ L : Orb O (⊤ : Subgroup Aˣ) (stLat O E g)))
    (by
      rintro a b ⟨t, ht⟩
      exact (Quot.sound ⟨t, Subgroup.mem_top t, by rw [← ht, stLat_smul_val]⟩).symm)
  left_inv := by
    intro o
    induction o using Quot.ind
    rfl
  right_inv := by
    intro o
    induction o using Quotient.inductionOn
    rfl

/- English proof (translation)
Take `⟨t, rfl⟩` from `h`. Use extensionality with `s`. Rewrite using `[MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, smul_smul, mul_comm, ← smul_smul, smul_left_cancel_iff]`.
-/
theorem stabilizer_eq_of_mem_orbit (g : A) {x y : stLat O E g} (h : y ∈ MulAction.orbit Aˣ x) :
    MulAction.stabilizer Aˣ y = MulAction.stabilizer Aˣ x := by
  obtain ⟨t, rfl⟩ := h
  ext s
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, smul_smul, mul_comm, ← smul_smul,
    smul_left_cancel_iff]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `orbSum O ⊤ (stLat O E g) (fun _ => 1) = _`. Unfold `orbSum`. Rewrite using `[← finsum_comp_equiv (orbEquiv (O := O) (E := E) g)]`. Use `finsum_congr fun o => ?_` and prove the remaining obligations. Establish `h1 : (Quotient.mk _ (Quot.out o) : MulAction.orbitRel.Quotient Aˣ (stLat O E g)) = orbEquiv g o` using `by conv_rhs => rw [← Quot.out_eq o]`.

Both sides reduce to the same expression. Establish `h2` using `Quotient.out_eq (orbEquiv (O := O) (E := E) g o)`. Establish `h3` using `Quotient.exact (h2.trans h1.symm)`. Rewrite using `[one_mul, inf_top_eq, inf_top_eq, stabLat_eq_stabilizer g (Quot.out o), stabilizer_eq_of_mem_orbit g h3]`.
-/
theorem countGL_eq_sum_orbits (O E A : Type) [CommRing O] [Field E] [CommRing A] [Algebra O A] [Algebra E A]
    (g : A) : countGL O E g = ∑ᶠ o : MulAction.orbitRel.Quotient Aˣ (stLat O E g),
      ((MulAction.stabilizer Aˣ (Quotient.out o)).relIndex (intUnits O A) : ℚ) := by
  change orbSum O ⊤ (stLat O E g) (fun _ => 1) = _
  unfold orbSum
  rw [← finsum_comp_equiv (orbEquiv (O := O) (E := E) g)]
  refine finsum_congr fun o => ?_
  have h1 : (Quotient.mk _ (Quot.out o) : MulAction.orbitRel.Quotient Aˣ (stLat O E g)) = orbEquiv g o := by
    conv_rhs => rw [← Quot.out_eq o]
    rfl
  have h2 := Quotient.out_eq (orbEquiv (O := O) (E := E) g o)
  have h3 := Quotient.exact (h2.trans h1.symm)
  rw [one_mul, inf_top_eq, inf_top_eq, stabLat_eq_stabilizer g (Quot.out o),
    stabilizer_eq_of_mem_orbit g h3]

end Bridge

end GlobalTheory.UnitLemma
