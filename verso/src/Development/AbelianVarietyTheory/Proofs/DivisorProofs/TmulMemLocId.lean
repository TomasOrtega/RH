import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

noncomputable section

namespace GlobalTheory.LocIdeal

open scoped TensorProduct nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def locId (v : Pl F) (𝔞 : FractionalIdeal (𝓞 E)⁰ E) : AddSubgroup (Fv F v ⊗[F] E) :=
  AddSubgroup.closure {z | ∃ a ∈ v.adicCompletionIntegers F, ∃ x ∈ 𝔞, z = a ⊗ₜ[F] x}

/- English proof (translation)
The claim follows from `AddSubgroup.subset_closure ⟨a, ha, x, hx, rfl⟩`.
-/
theorem tmul_mem_locId {v : Pl F} {𝔞 : FractionalIdeal (𝓞 E)⁰ E} {a : Fv F v} (ha : a ∈ v.adicCompletionIntegers F)
    {x : E} (hx : x ∈ 𝔞) : a ⊗ₜ[F] x ∈ locId v 𝔞 :=
  AddSubgroup.subset_closure ⟨a, ha, x, hx, rfl⟩

/- English proof (translation)
Rewrite using `[locId, AddSubgroup.closure_eq_bot_iff]`. Introduce and unpack `_ ⟨a, -, x, hx, rfl⟩`. Rewrite using `[(FractionalIdeal.mem_zero_iff _).1 hx, TensorProduct.tmul_zero]`. Both sides reduce to the same expression.
-/
example (v : Pl F) : locId v (0 : FractionalIdeal (𝓞 E)⁰ E) = ⊥ := by
  rw [locId, AddSubgroup.closure_eq_bot_iff]
  rintro _ ⟨a, -, x, hx, rfl⟩
  rw [(FractionalIdeal.mem_zero_iff _).1 hx, TensorProduct.tmul_zero]
  rfl

/- English proof (translation)
The claim follows from `tmul_mem_locId (one_mem _) (FractionalIdeal.one_mem_one _)`.
-/
example (v : Pl F) : (1 : Fv F v ⊗[F] E) ∈ locId v (1 : FractionalIdeal (𝓞 E)⁰ E) :=
  tmul_mem_locId (one_mem _) (FractionalIdeal.one_mem_one _)

end GlobalTheory.LocIdeal

end
