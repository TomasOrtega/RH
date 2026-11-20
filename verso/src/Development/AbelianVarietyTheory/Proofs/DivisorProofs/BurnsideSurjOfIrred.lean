import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfIrreducible

namespace GlobalTheory.CompanionTheory.Burnside

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.IrreducibleMembership.mem_of_irreducible`. Consider the case `exact _root_.GlobalTheory.IrreducibleMembership.mem_of_irreducible`. Consider the case `(apply _root_.GlobalTheory.IrreducibleMembership.mem_of_irreducible <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.IrreducibleMembership.mem_of_irreducible <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.IrreducibleMembership.mem_of_irreducible <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.IrreducibleMembership.mem_of_irreducible ..)`.
-/
theorem mem_of_irred {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : Subalgebra K (Module.End K V))
    (hirr : ∀ N : Submodule K V, (∀ f ∈ S, ∀ v ∈ N, f v ∈ N) → N = ⊥ ∨ N = ⊤)
    (f : Module.End K V) : f ∈ S := by
  first
  | exact @_root_.GlobalTheory.IrreducibleMembership.mem_of_irreducible
  | exact _root_.GlobalTheory.IrreducibleMembership.mem_of_irreducible
  | (apply _root_.GlobalTheory.IrreducibleMembership.mem_of_irreducible <;> assumption)
  | (intros; apply _root_.GlobalTheory.IrreducibleMembership.mem_of_irreducible <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IrreducibleMembership.mem_of_irreducible <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IrreducibleMembership.mem_of_irreducible ..)

/- English proof (translation)
Introduce `f`. Establish `h` using `mem_of_irred ρ.range (fun N hN => hirr N fun a w hw => hN (ρ a) ⟨a, rfl⟩ w hw) f`. Take `⟨a, ha⟩` from `h`. Conclude with `⟨a, ha⟩`.
-/
theorem burnside_surj_of_irred {A V : Type} [Ring A] [Algebra ℂ A] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : A →ₐ[ℂ] Module.End ℂ V) (hirr : ∀ W : Submodule ℂ V, (∀ h, ∀ w ∈ W, ρ h w ∈ W) → W = ⊥ ∨ W = ⊤) :
    Function.Surjective ρ := by
  intro f
  have h := mem_of_irred ρ.range (fun N hN => hirr N fun a w hw => hN (ρ a) ⟨a, rfl⟩ w hw) f
  obtain ⟨a, ha⟩ := h
  exact ⟨a, ha⟩

end GlobalTheory.CompanionTheory.Burnside
