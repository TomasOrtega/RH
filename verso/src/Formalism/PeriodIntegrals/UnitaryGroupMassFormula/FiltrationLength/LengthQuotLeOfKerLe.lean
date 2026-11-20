import Mathlib
import Formalism.PeriodIntegrals.FiltLen

namespace PI.FiltrationLength

open Submodule

variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]

noncomputable def ell (B A : Submodule R W) : ℕ∞ :=
  Module.length R (↥B ⧸ A.comap B.subtype)

/- English proof (translation)
Unfold `ell`. Set `f : (↥C ⧸ A.comap C.subtype) →ₗ[R] (↥B ⧸ A.comap B.subtype)` to `Submodule.mapQ _ _ (Submodule.inclusion hCB) (fun x hx => by simpa using hx)`. Set `g : (↥B ⧸ A.comap B.subtype) →ₗ[R] (↥B ⧸ C.comap B.subtype)` to `Submodule.mapQ _ _ LinearMap.id (fun x hx => by simpa using hAC hx)`. Establish `hf : Function.Injective f`. Rewrite using `[← LinearMap.ker_eq_bot, eq_bot_iff]`.

Introduce `y hy`. Proceed by induction on `y using Submodule.Quotient.induction_on with`. Consider the case `_ c`. Rewrite `hy` using `[LinearMap.mem_ker]`. Simplify using `only [f, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_inclusion] at hy`.

Rewrite using `[Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]`. Conclude with `hy`. Establish `hg : Function.Surjective g`. Introduce `y`. Proceed by induction on `y using Submodule.Quotient.induction_on with`.

Consider the case `_ b => exact ⟨Submodule.Quotient.mk b, by simp [g]⟩`. Establish `H : Function.Exact f g`. Introduce `y`. Proceed by induction on `y using Submodule.Quotient.induction_on with`. Consider the case `_ b`.

Prove the components needed by the constructor for the conclusion. Introduce `hb`. Simplify using `only [g, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype] at hb`. Conclude with `⟨Submodule.Quotient.mk ⟨b, hb⟩, by simp [f]; rfl⟩`. Introduce and unpack `⟨z, hz⟩`.

Proceed by induction on `z using Submodule.Quotient.induction_on with`. Consider the case `_ c`. Simplify using `only [f, Submodule.mapQ_apply] at hz`. Rewrite `hz` using `[Submodule.Quotient.eq]`. Simplify using `only [Submodule.mem_comap, Submodule.coe_subtype, AddSubgroupClass.coe_sub, Submodule.coe_inclusion] at hz`.

Simplify using `only [g, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype]`. Establish `h1 : (c : W) ∈ C` using `c.2`. Establish `h2 : (c : W) - (b : W) ∈ C` using `hAC hz`. Use `C.sub_mem h1 h2` as an intermediate fact. Simplify using `using this`.

Conclude with `Module.length_eq_add_of_exact f g hf hg H`.
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
Establish `h1 : Module.length R (X ⧸ K) ≤ Module.length R (X ⧸ LinearMap.ker g)` using `Module.length_le_of_surjective (Submodule.mapQ _ _ LinearMap.id (by simpa using hK)) (by`. Introduce `y`. Proceed by induction on `y using Submodule.Quotient.induction_on with`. Consider the case `_ x => exact ⟨Submodule.Quotient.mk x, by simp⟩)`. Establish `h2 : Module.length R (X ⧸ LinearMap.ker g) = Module.length R (LinearMap.range g)` using `(g.quotKerEquivRange).length_eq`.

Establish `h3 : Module.length R (LinearMap.range g) ≤ Module.length R Y` using `Module.length_le_of_injective (LinearMap.range g).subtype (Submodule.subtype_injective _)`. Conclude with `h1.trans (h2.le.trans h3)`.
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
Unfold `ell`. Use `Module.length_le_of_surjective (Submodule.mapQ (D.comap C.subtype) (A.comap (A ⊔ C).subtype) (Submodule.inclusion (le_sup_right : C ≤ A ⊔ C)) (fun x hx => by simpa using hDA hx)) ?_` and prove the remaining obligations. Introduce `y`. Proceed by induction on `y using Submodule.Quotient.induction_on with`. Consider the case `_ z`.

Take `⟨a, ha, c, hc, hz⟩` from `Submodule.mem_sup.mp z.2`. Use `⟨Submodule.Quotient.mk ⟨c, hc⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [Submodule.mapQ_apply]`. Rewrite using `[Submodule.Quotient.eq]`. Simplify using `only [Submodule.mem_comap, Submodule.coe_subtype, AddSubgroupClass.coe_sub, Submodule.coe_inclusion]`.

Establish `: (c : W) - (z : W) = -a` using `by rw [← hz]; abel`. Rewrite using `[this]`. Conclude with `A.neg_mem ha`.
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
