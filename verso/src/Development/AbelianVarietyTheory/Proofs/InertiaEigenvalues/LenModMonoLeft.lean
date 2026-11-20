import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocMulVec

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory

/- English proof (translation)
Introduce `O M _ _ _ S S' H hS`. Establish `hle : S ⊔ H ≤ S' ⊔ H` using `sup_le_sup_right hS H`. Set `f` to `Submodule.mapQ (H.comap (S ⊔ H).subtype) (H.comap (S' ⊔ H).subtype) (Submodule.inclusion hle) (fun x hx => by simpa using hx)`. Establish `hf : Function.Injective f`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`.

Introduce `x hx`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Rewrite `hx` using `[Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Simplify using `using hx`.

Conclude with `Module.length_le_of_injective f hf`.
-/
theorem lenMod_mono_left : ∀ {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (S S' H : Submodule O M), S ≤ S' → BlochKatoDuality.lenMod S H ≤ BlochKatoDuality.lenMod S' H := by
  intro O M _ _ _ S S' H hS

  have hle : S ⊔ H ≤ S' ⊔ H := sup_le_sup_right hS H
  let f := Submodule.mapQ (H.comap (S ⊔ H).subtype) (H.comap (S' ⊔ H).subtype)
    (Submodule.inclusion hle) (fun x hx => by simpa using hx)
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    rw [Submodule.Quotient.mk_eq_zero]
    simpa using hx
  exact Module.length_le_of_injective f hf

end GlobalTheory
