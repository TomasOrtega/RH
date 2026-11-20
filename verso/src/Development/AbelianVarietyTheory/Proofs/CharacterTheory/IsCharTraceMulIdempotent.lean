import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldOfRepresentation
open GlobalTheory.BI
noncomputable section
namespace GlobalTheory.BI

/- English proof (translation)
Introduce `L _ T _ V _ _ _ ρ e he hc`. Establish `hfix : ∀ v ∈ LinearMap.range e, e v = v`. Introduce and unpack `_ ⟨w, rfl⟩`. Rewrite using `[← Module.End.mul_apply, he]`. Set `W : Subrepresentation ρ` to `⟨LinearMap.range e, fun t v hv => by`.

Take `⟨w, rfl⟩` from `hv`. Conclude with `⟨ρ t w, by rw [← Module.End.mul_apply e, ← hc t, Module.End.mul_apply]⟩⟩`. Establish `key` using `(_root_.GlobalTheory.BI.isChar_and_isIrrChar_of_rep L L T _ W.toRepresentation).1`. Use `key using 2 with t` and compare the differences between its conclusion and the goal. Rewrite using `[Algebra.algebraMap_self, RingHom.id_apply, Representation.character, ← LinearMap.trace_restrict_eq_of_forall_mem (LinearMap.range e) (ρ t * e) (fun x => ⟨ρ t x, by rw [hc t]; rfl⟩)]`.

Use `congr 1`. Use extensionality with `⟨v, hv⟩`. Express the relevant statement in the definitionally equal form `(ρ t * e) v = ρ t v`. Rewrite using `[Module.End.mul_apply, hfix v hv]`.
-/
theorem _root_.GlobalTheory.BI.isChar_trace_mul_idempotent :
    ∀ (L : Type) [Field L] (T : Type) [Group T] (V : Type) [AddCommGroup V] [Module L V] [FiniteDimensional L V] (ρ : Representation L T V) (e : Module.End L V), e * e = e → (∀ t, ρ t * e = e * ρ t) → _root_.GlobalTheory.BI.IsChar L L (fun t => LinearMap.trace L V (ρ t * e)) := by
  intro L _ T _ V _ _ _ ρ e he hc
  have hfix : ∀ v ∈ LinearMap.range e, e v = v := by
    rintro _ ⟨w, rfl⟩
    rw [← Module.End.mul_apply, he]
  let W : Subrepresentation ρ :=
    ⟨LinearMap.range e, fun t v hv => by
      obtain ⟨w, rfl⟩ := hv
      exact ⟨ρ t w, by rw [← Module.End.mul_apply e, ← hc t, Module.End.mul_apply]⟩⟩
  have key := (_root_.GlobalTheory.BI.isChar_and_isIrrChar_of_rep L L T _ W.toRepresentation).1
  convert key using 2 with t
  rw [Algebra.algebraMap_self, RingHom.id_apply, Representation.character,
    ← LinearMap.trace_restrict_eq_of_forall_mem (LinearMap.range e) (ρ t * e)
      (fun x => ⟨ρ t x, by rw [hc t]; rfl⟩)]
  congr 1
  ext ⟨v, hv⟩
  change (ρ t * e) v = ρ t v
  rw [Module.End.mul_apply, hfix v hv]

end GlobalTheory.BI
