import Mathlib

namespace Formalism.L2.GlobalTheoryTheory.LemB

/- English proof (translation)
Introduce a local definition for the expression. Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem len_equiv_semilinear {R R' M M' : Type*} [Ring R] [Ring R'] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R' M'] {σ : R →+* R'} {σ' : R' →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (e : M ≃ₛₗ[σ] M') : Module.length R M = Module.length R' M' := by
  let e' : Submodule R M ≃o Submodule R' M' := Submodule.orderIsoMapComap e
  unfold Module.length
  congr 1
  exact Order.krullDim_eq_of_orderIso e'

noncomputable def quotEquivSL {R R' M M' : Type*} [Ring R] [Ring R'] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R' M'] {σ : R →+* R'} {σ' : R' →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (e : M ≃ₛₗ[σ] M') (P : Submodule R M) (Q : Submodule R' M') (h : P.map (e : M →ₛₗ[σ] M') = Q) :
    (M ⧸ P) ≃ₛₗ[σ] (M' ⧸ Q) :=
  LinearEquiv.ofLinearMap
    (P.mapQ Q (e : M →ₛₗ[σ] M') (by rw [← h]; exact Submodule.le_comap_map _ _))
    (Q.mapQ P (e.symm : M' →ₛₗ[σ'] M) (by
      rw [← h]; rintro _ ⟨x, hx, rfl⟩
      show e.symm (e x) ∈ P
      rw [e.symm_apply_apply]; exact hx))
    (by ext x; simp) (by ext x; simp)

/- English proof (translation)
Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Substitute using the available equality. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. A detailed English derivation is pending.
-/
theorem len_quot_semilinear {R R' M M' : Type*} [Ring R] [Ring R'] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R' M'] {σ : R →+* R'} {σ' : R' →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (f : M →ₛₗ[σ] M') (hf : Function.Injective f) (A B : Submodule R M) :
    Module.length R (A ⧸ B.comap A.subtype) =
      Module.length R' (A.map f ⧸ (B.map f).comap (A.map f).subtype) := by
  let eA : A ≃ₛₗ[σ] A.map f := Submodule.equivMapOfInjective f hf A
  refine len_equiv_semilinear (quotEquivSL eA _ _ ?_)
  ext ⟨y, hy⟩
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨⟨x, hxA⟩, hxB, hxy⟩
    exact ⟨x, hxB, congrArg Subtype.val hxy⟩
  · rintro ⟨x, hxB, hfx⟩
    obtain ⟨x', hx'A, hx'⟩ := hy
    have hxx : x = x' := hf (hfx.trans hx'.symm)
    subst hxx
    refine ⟨⟨x, hx'A⟩, hxB, ?_⟩
    apply Subtype.ext
    exact hfx

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities. Treat this case separately. Treat this case separately. Treat this case separately.

A detailed English derivation is pending.
-/
theorem len_pi_sum {R : Type*} [CommRing R] {G : Type*} [Fintype G] [DecidableEq G] {M : G → Type*}
    [∀ g, AddCommGroup (M g)] [∀ g, Module R (M g)] (A B : ∀ g, Submodule R (M g)) :
    Module.length R ((Submodule.pi Set.univ A) ⧸
        (Submodule.pi Set.univ B).comap (Submodule.pi Set.univ A).subtype) =
      ∑ g, Module.length R (A g ⧸ (B g).comap (A g).subtype) := by
  classical
  let φ : (Submodule.pi Set.univ A) →ₗ[R] (∀ g, A g ⧸ (B g).comap (A g).subtype) :=
    LinearMap.pi (fun g => ((B g).comap (A g).subtype).mkQ ∘ₗ
      (((LinearMap.proj g).comp (Submodule.pi Set.univ A).subtype).codRestrict (A g)
        (fun x => x.2 g (Set.mem_univ g))))
  have hφ : Function.Surjective φ := by
    intro y
    choose x hx using fun g => Submodule.Quotient.mk_surjective _ (y g)
    refine ⟨⟨fun g => (x g : M g), fun g _ => (x g).2⟩, ?_⟩
    funext g
    rw [← hx g]
    rfl
  have hker : LinearMap.ker φ =
      (Submodule.pi Set.univ B).comap (Submodule.pi Set.univ A).subtype := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_pi,
      Set.mem_univ, true_implies]
    rw [funext_iff]
    refine forall_congr' (fun g => ?_)
    change Submodule.Quotient.mk _ = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    rfl
  let e := (Submodule.quotEquivOfEq _ _ hker.symm).trans (φ.quotKerEquivOfSurjective hφ)
  rw [len_equiv_semilinear e]
  first
  | exact Module.length_pi
  | exact Module.length_pi_of_fintype _
  | simp [Module.length_pi]

end Formalism.L2.GlobalTheoryTheory.LemB
