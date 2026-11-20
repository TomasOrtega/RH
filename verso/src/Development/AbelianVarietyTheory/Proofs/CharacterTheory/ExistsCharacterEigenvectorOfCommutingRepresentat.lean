import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Imports

namespace GlobalTheory

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.UnimodularLatticeLemma.main`. Consider the case `exact _root_.GlobalTheory.UnimodularLatticeLemma.main`. Consider the case `(apply _root_.GlobalTheory.UnimodularLatticeLemma.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.UnimodularLatticeLemma.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.UnimodularLatticeLemma.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.UnimodularLatticeLemma.main ..)`.
-/
theorem exists_common_eigenvector_of_commute {L : Type} [Field L] [IsAlgClosed L] {ι : Type}
    {V : Type} [AddCommGroup V] [Module L V] [FiniteDimensional L V] [Nontrivial V]
    (f : ι → Module.End L V) (hf : ∀ a b, f a * f b = f b * f a) :
    ∃ v : V, v ≠ 0 ∧ ∀ b, ∃ μ : L, f b v = μ • v := by
  first
  | exact @_root_.GlobalTheory.UnimodularLatticeLemma.main
  | exact _root_.GlobalTheory.UnimodularLatticeLemma.main
  | (apply _root_.GlobalTheory.UnimodularLatticeLemma.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnimodularLatticeLemma.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnimodularLatticeLemma.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnimodularLatticeLemma.main ..)

/- English proof (translation)
Introduce `L _ _ B _ V _ _ _ _ ρ h`. Take `⟨v, hv0, hv⟩` from `exists_common_eigenvector_of_commute (fun b => ρ b) h`. Use `choose μ hμ using hv`. Establish `hinj : Function.Injective fun c : L => c • v` using `smul_left_injective L hv0`. Set `χ : B →* L` to `{ toFun := μ map_one' := hinj (by`.

Use `hμ 1` as an intermediate fact. Simplify using `only [map_one, Module.End.one_apply] at this`. Simplify using `using this.symm)`. Use the proof step `map_mul' := fun a b => hinj (by`. Establish `h1` using `hμ (a * b)`.

Simplify using `only [map_mul, Module.End.mul_apply] at h1`. Establish `h2` using `hμ a`. Establish `h3` using `hμ b`. Simplify using `only at h2 h3 ⊢`. Rewrite using `[← h1, h3, map_smul, h2, smul_smul, mul_comm]) }`.

Conclude with `⟨χ.toHomUnits, v, hv0, fun b => hμ b⟩`.
-/
theorem exists_character_eigenvector_of_commute :
    ∀ (L : Type) [Field L] [IsAlgClosed L] (B : Type) [Group B] (V : Type) [AddCommGroup V] [Module L V] [FiniteDimensional L V] [Nontrivial V] (ρ : Representation L B V), (∀ a b, ρ a * ρ b = ρ b * ρ a) → ∃ (lam : B →* Lˣ) (v : V), v ≠ 0 ∧ ∀ b, ρ b v = (lam b : L) • v := by
  intro L _ _ B _ V _ _ _ _ ρ h
  obtain ⟨v, hv0, hv⟩ := exists_common_eigenvector_of_commute (fun b => ρ b) h
  choose μ hμ using hv
  have hinj : Function.Injective fun c : L => c • v := smul_left_injective L hv0
  let χ : B →* L :=
    { toFun := μ
      map_one' := hinj (by
        have := hμ 1
        simp only [map_one, Module.End.one_apply] at this
        simpa using this.symm)
      map_mul' := fun a b => hinj (by
        have h1 := hμ (a * b)
        simp only [map_mul, Module.End.mul_apply] at h1
        have h2 := hμ a
        have h3 := hμ b
        simp only at h2 h3 ⊢
        rw [← h1, h3, map_smul, h2, smul_smul, mul_comm]) }
  exact ⟨χ.toHomUnits, v, hv0, fun b => hμ b⟩

end GlobalTheory
