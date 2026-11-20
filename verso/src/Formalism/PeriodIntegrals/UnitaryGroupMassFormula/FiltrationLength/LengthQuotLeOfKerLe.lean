import Mathlib
import Formalism.PeriodIntegrals.FiltLen

namespace PI.FiltrationLength

open Submodule

variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]

noncomputable def ell (B A : Submodule R W) : ℕ∞ :=
  Module.length R (↥B ⧸ A.comap B.subtype)

/- English proof (translation)
Replace the relevant objects with their definitions. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Proceed by induction.

Treat this case separately. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem ell_add {A B C : Submodule R W} (hAC : A ≤ C) (hCB : C ≤ B) :
    ell B A = ell C A + ell B C := by
  unfold ell
  let f : (↥C ⧸ A.comap C.subtype) →ₗ[R] (↥B ⧸ A.comap B.subtype) :=
    Submodule.mapQ _ _ (Submodule.inclusion hCB) (fun x hx => by simpa using hx)
  let g : (↥B ⧸ A.comap B.subtype) →ₗ[R] (↥B ⧸ C.comap B.subtype) :=
    Submodule.mapQ _ _ LinearMap.id (fun x hx => by simpa using hAC hx)
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro y hy
    induction y using Submodule.Quotient.induction_on with
    | _ c =>
      rw [LinearMap.mem_ker] at hy
      simp only [f, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
        Submodule.coe_subtype, Submodule.coe_inclusion] at hy
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      exact hy
  have hg : Function.Surjective g := by
    intro y
    induction y using Submodule.Quotient.induction_on with
    | _ b => exact ⟨Submodule.Quotient.mk b, by simp [g]⟩
  have H : Function.Exact f g := by
    intro y
    induction y using Submodule.Quotient.induction_on with
    | _ b =>
      constructor
      · intro hb
        simp only [g, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero,
          Submodule.mem_comap, Submodule.coe_subtype] at hb
        exact ⟨Submodule.Quotient.mk ⟨b, hb⟩, by simp [f]; rfl⟩
      · rintro ⟨z, hz⟩
        induction z using Submodule.Quotient.induction_on with
        | _ c =>
          simp only [f, Submodule.mapQ_apply] at hz
          rw [Submodule.Quotient.eq] at hz
          simp only [Submodule.mem_comap, Submodule.coe_subtype, AddSubgroupClass.coe_sub,
            Submodule.coe_inclusion] at hz
          simp only [g, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero,
            Submodule.mem_comap, Submodule.coe_subtype]
          have h1 : (c : W) ∈ C := c.2
          have h2 : (c : W) - (b : W) ∈ C := hAC hz
          have := C.sub_mem h1 h2
          simpa using this
  exact Module.length_eq_add_of_exact f g hf hg H

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Establish an intermediate fact.

Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem length_quot_le_of_ker_le {X Y : Type} [AddCommGroup X] [Module R X] [AddCommGroup Y]
    [Module R Y] (g : X →ₗ[R] Y) (K : Submodule R X) (hK : LinearMap.ker g ≤ K) :
    Module.length R (X ⧸ K) ≤ Module.length R Y := by
  have h1 : Module.length R (X ⧸ K) ≤ Module.length R (X ⧸ LinearMap.ker g) :=
    Module.length_le_of_surjective (Submodule.mapQ _ _ LinearMap.id (by simpa using hK))
      (by
        intro y
        induction y using Submodule.Quotient.induction_on with
        | _ x => exact ⟨Submodule.Quotient.mk x, by simp⟩)
  have h2 : Module.length R (X ⧸ LinearMap.ker g) = Module.length R (LinearMap.range g) :=
    (g.quotKerEquivRange).length_eq
  have h3 : Module.length R (LinearMap.range g) ≤ Module.length R Y :=
    Module.length_le_of_injective (LinearMap.range g).subtype (Submodule.subtype_injective _)
  exact h1.trans (h2.le.trans h3)

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ell_sup_le {A C D : Submodule R W} (hDA : D ≤ A) :
    ell (A ⊔ C) A ≤ ell C D := by
  unfold ell
  refine Module.length_le_of_surjective
    (Submodule.mapQ (D.comap C.subtype) (A.comap (A ⊔ C).subtype)
      (Submodule.inclusion (le_sup_right : C ≤ A ⊔ C)) (fun x hx => by simpa using hDA hx)) ?_
  intro y
  induction y using Submodule.Quotient.induction_on with
  | _ z =>
    obtain ⟨a, ha, c, hc, hz⟩ := Submodule.mem_sup.mp z.2
    refine ⟨Submodule.Quotient.mk ⟨c, hc⟩, ?_⟩
    simp only [Submodule.mapQ_apply]
    rw [Submodule.Quotient.eq]
    simp only [Submodule.mem_comap, Submodule.coe_subtype, AddSubgroupClass.coe_sub,
      Submodule.coe_inclusion]
    have : (c : W) - (z : W) = -a := by rw [← hz]; abel
    rw [this]
    exact A.neg_mem ha

end PI.FiltrationLength
