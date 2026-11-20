import Mathlib

noncomputable section

namespace MassDataIdxRed

open Matrix

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem isUnit_of_map {R S : Type} [CommRing R] [IsLocalRing R] [Field S] (π : R →+* S)
    (hπ : Function.Surjective π) (r : R) (h : IsUnit (π r)) : IsUnit r := by
  by_contra hr
  have hk : RingHom.ker π = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective π hπ)
  have hm : r ∈ RingHom.ker π := by
    rw [hk]; exact (IsLocalRing.mem_maximalIdeal r).2 hr
  rw [RingHom.mem_ker] at hm
  rw [hm] at h
  exact not_isUnit_zero h

def glRed {ι R S : Type} [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing S] (π : R →+* S) :
    GL ι R →* GL ι S :=
  Units.map (π.mapMatrix : Matrix ι ι R →+* Matrix ι ι S).toMonoidHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem glRed_coe {ι R S : Type} [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing S] (π : R →+* S)
    (A : GL ι R) : ((glRed π A : GL ι S) : Matrix ι ι S) = (A : Matrix ι ι R).map π := rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem glRed_surjective {ι R S : Type} [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing S]
    (π : R →+* S) (hπ : Function.Surjective π) (hloc : ∀ r, IsUnit (π r) → IsUnit r) :
    Function.Surjective (glRed (ι := ι) π) := by
  intro B
  choose f hf using hπ
  set A0 : Matrix ι ι R := (B : Matrix ι ι S).map f with hA0def
  have hA0 : A0.map π = (B : Matrix ι ι S) := by
    ext i j; simp [A0, hf]
  have hdet : IsUnit A0.det := by
    apply hloc
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hA0]
    exact (Matrix.isUnit_iff_isUnit_det _).1 B.isUnit
  refine ⟨Matrix.nonsingInvUnit A0 hdet, ?_⟩
  apply Units.ext
  rw [glRed_coe]
  exact hA0

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem glRed_eq_one_iff {ι R S : Type} [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing S]
    (π : R →+* S) (A : GL ι R) :
    glRed π A = 1 ↔ ∀ i j, ((A : Matrix ι ι R) - 1) i j ∈ RingHom.ker π := by
  rw [← Units.val_inj, glRed_coe, Units.val_one]
  constructor
  · intro h i j
    have hij := congrFun (congrFun h i) j
    rw [Matrix.map_apply] at hij
    rw [RingHom.mem_ker, Matrix.sub_apply, map_sub, hij, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  · intro h
    ext i j
    have hij := h i j
    rw [RingHom.mem_ker, Matrix.sub_apply, map_sub, sub_eq_zero] at hij
    rw [Matrix.map_apply, hij, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

end MassDataIdxRed
