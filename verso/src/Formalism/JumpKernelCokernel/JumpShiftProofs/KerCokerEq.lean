import Formalism.JumpKernelCokernel.KerCokerEq

namespace Formalism.KernelCokernelLengths.KernelCokernelEqualityLemmas

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Put the expressions in a common number system so they can be compared. Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem main (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M]
    (hM : Module.length O M ≠ ⊤) (f : Module.End O M) :
    Module.length O (LinearMap.ker f) = Module.length O (M ⧸ LinearMap.range f) := by
  have h1 : Module.length O M =
      Module.length O (LinearMap.ker f) + Module.length O (M ⧸ LinearMap.ker f) :=
    Module.length_eq_add_of_exact _ _ (LinearMap.ker f).injective_subtype
      (LinearMap.ker f).mkQ_surjective (LinearMap.exact_subtype_mkQ _)
  have h2 : Module.length O (M ⧸ LinearMap.ker f) = Module.length O (LinearMap.range f) :=
    (f.quotKerEquivRange).length_eq
  have h3 : Module.length O M =
      Module.length O (LinearMap.range f) + Module.length O (M ⧸ LinearMap.range f) :=
    Module.length_eq_add_of_exact _ _ (LinearMap.range f).injective_subtype
      (LinearMap.range f).mkQ_surjective (LinearMap.exact_subtype_mkQ _)
  rw [h2] at h1
  have hk : Module.length O (LinearMap.ker f) ≠ ⊤ := by
    intro h; apply hM; rw [h1, h]; exact top_add _
  have hr : Module.length O (LinearMap.range f) ≠ ⊤ := by
    intro h; apply hM; rw [h1, h]; exact add_top _
  have hc : Module.length O (M ⧸ LinearMap.range f) ≠ ⊤ := by
    intro h; apply hM; rw [h3, h]; exact add_top _
  lift Module.length O M to ℕ using hM with m hm
  lift Module.length O (LinearMap.ker f) to ℕ using hk with a ha
  lift Module.length O (LinearMap.range f) to ℕ using hr with b hb
  lift Module.length O (M ⧸ LinearMap.range f) to ℕ using hc with c hc'
  norm_cast at h1 h3 ⊢
  omega

/- English proof (translation)
Establish an intermediate fact. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem coker (O : Type) [CommRing O] (M M' : Type) [AddCommGroup M] [Module O M]
    [AddCommGroup M'] [Module O M'] (f : Module.End O M) (f' : Module.End O M')
    (g : M →ₗ[O] M') (hg : Function.Surjective g) (hc : g ∘ₗ f = f' ∘ₗ g) :
    Module.length O (M' ⧸ LinearMap.range f') ≤ Module.length O (M ⧸ LinearMap.range f) := by
  have hle : LinearMap.range f ≤ (LinearMap.range f').comap g := by
    rintro _ ⟨m, rfl⟩
    exact ⟨g m, (LinearMap.congr_fun hc m).symm⟩
  have hs : Function.Surjective (Submodule.mapQ (LinearMap.range f) (LinearMap.range f') g hle) := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H y =>
      obtain ⟨m, rfl⟩ := hg y
      exact ⟨Submodule.Quotient.mk m, rfl⟩
  exact Module.length_le_of_surjective _ hs

end Formalism.KernelCokernelLengths.KernelCokernelEqualityLemmas

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem Formalism.KernelCokernelLengths.endKernelCokernelLengthEq : Formalism.KernelCokernelLengths.KerCokerEq :=
  fun O _ M _ _ hM f => Formalism.KernelCokernelLengths.KernelCokernelEqualityLemmas.main O M hM f

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem Formalism.KernelCokernelLengths.cokernelLengthLeOfSurjective : Formalism.KernelCokernelLengths.CokerSurj :=
  fun O _ M M' _ _ _ _ f f' g hg hc => Formalism.KernelCokernelLengths.KernelCokernelEqualityLemmas.coker O M M' f f' g hg hc
