import Mathlib

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Proceed by induction. Treat this case separately. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Proceed by induction.

Treat this case separately. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem UpperTheory.Reformulated.B.JointEigenvalueBoundsFromAnyDatum.length_chain :
    ∀ {O X : Type} [inst : CommRing O] [inst_1 : AddCommGroup X]
    [inst_2 : _root_.Module O X] {A B C : Submodule O X},
    A ≤ B →
      B ≤ C →
        Module.length O (↥C ⧸ Submodule.comap C.subtype A) =
          Module.length O (↥B ⧸ Submodule.comap B.subtype A) + Module.length O (↥C ⧸ Submodule.comap C.subtype B) := by
  intro O X _ _ _ A B C hAB hBC
  let f : (↥B ⧸ Submodule.comap B.subtype A) →ₗ[O] (↥C ⧸ Submodule.comap C.subtype A) :=
    Submodule.mapQ _ _ (Submodule.inclusion hBC) (fun x hx => hx)
  let g : (↥C ⧸ Submodule.comap C.subtype A) →ₗ[O] (↥C ⧸ Submodule.comap C.subtype B) :=
    Submodule.mapQ _ _ LinearMap.id (fun x hx => hAB hx)
  refine Module.length_eq_add_of_exact f g ?_ ?_ ?_
  · rw [injective_iff_map_eq_zero]
    intro y
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      intro h
      have h' : Submodule.Quotient.mk (p := Submodule.comap C.subtype A)
          (Submodule.inclusion hBC x) = 0 := h
      rw [Submodule.Quotient.mk_eq_zero] at h' ⊢
      exact h'
  · intro y
    induction y using Submodule.Quotient.induction_on with
    | H x => exact ⟨Submodule.Quotient.mk x, rfl⟩
  · intro y
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      constructor
      · intro h
        have h' : Submodule.Quotient.mk (p := Submodule.comap C.subtype B) x = 0 := h
        rw [Submodule.Quotient.mk_eq_zero] at h'
        exact ⟨Submodule.Quotient.mk ⟨x.1, h'⟩, rfl⟩
      · rintro ⟨z, hz⟩
        rw [← hz]
        induction z using Submodule.Quotient.induction_on with
        | H w =>
          have : Submodule.Quotient.mk (p := Submodule.comap C.subtype B)
              (Submodule.inclusion hBC w) = 0 :=
            (Submodule.Quotient.mk_eq_zero _).2 w.2
          exact this
