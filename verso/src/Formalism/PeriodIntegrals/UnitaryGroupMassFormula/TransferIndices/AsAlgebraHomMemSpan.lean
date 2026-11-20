import Mathlib

noncomputable section

namespace PI.Dv.TIW

section Span

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction.

A detailed English derivation is pending.
-/
theorem exists_dual_one (w : W) (hw : w ≠ 0) : ∃ φ : Module.Dual K W, φ w = 1 := by
  by_contra h
  push_neg at h
  apply hw
  rw [← Module.forall_dual_apply_eq_zero_iff K w]
  intro φ
  by_contra hφ
  exact h ((φ w)⁻¹ • φ) (by simp [inv_mul_cancel₀ hφ])

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem asAlgebraHom_mem_span (τ : Representation K G W) (z : MonoidAlgebra K G) (w : W) :
    τ.asAlgebraHom z w ∈ Submodule.span K (Set.range fun x => τ x w) := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, LinearMap.add_apply]; exact add_mem ha hb
  | single x r =>
    rw [Representation.asAlgebraHom_single, LinearMap.smul_apply]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem exists_end_map (w u : W) (hw : w ≠ 0) : ∃ M : Module.End K W, M w = u := by
  obtain ⟨φ, hφ⟩ := exists_dual_one (K := K) w hw
  exact ⟨φ.smulRight u, by rw [LinearMap.smulRight_apply, hφ, one_smul]⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem span_orbit (τ : Representation K G W) (hirr : Function.Surjective τ.asAlgebraHom) (w : W) (hw : w ≠ 0) :
    Submodule.span K (Set.range fun x => τ x w) = ⊤ := by
  rw [eq_top_iff]
  intro u _
  obtain ⟨M, hM⟩ := exists_end_map (K := K) w u hw
  obtain ⟨z, hz⟩ := hirr M
  have := asAlgebraHom_mem_span τ z w
  rwa [hz, hM] at this

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem finrank_le_card (τ : Representation K G W) (hirr : Function.Surjective τ.asAlgebraHom)
    [Nontrivial W] : Module.finrank K W ≤ Fintype.card G := by
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  rw [← finrank_top, ← span_orbit τ hirr w hw]
  exact finrank_range_le_card _

end Span

section Select

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Introduce a local definition for the expression. Equip the data with the indicated structure. Establish an intermediate fact.

Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem select_li {ι : Type} (F : ι → V) (hF : Submodule.span K (Set.range F) = ⊤) :
    ∃ g : Fin (Module.finrank K V) → ι, LinearIndependent K (F ∘ g) := by
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent'.{0} K F
  rw [hF] at hsp
  let b := Module.Basis.mk hli (by rw [hsp])
  letI := FiniteDimensional.fintypeBasisIndex b
  have hc : Fintype.card κ = Module.finrank K V := (Module.finrank_eq_card_basis b).symm
  let e := Fintype.equivFinOfCardEq hc
  refine ⟨a ∘ e.symm, ?_⟩
  have := hli.comp e.symm e.symm.injective
  simpa [Function.comp_assoc] using this

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem li_span_top {n : ℕ} (u : Fin n → V) (hu : LinearIndependent K u) (hn : n = Module.finrank K V) :
    Submodule.span K (Set.range u) = ⊤ := by
  have h := linearIndependent_iff_card_eq_finrank_span.mp hu
  apply Submodule.eq_top_of_finrank_eq
  show Set.finrank K (Set.range u) = _
  rw [← h, Fintype.card_fin, hn]

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem dual_span {ι : Type} (ψ : ι → Module.Dual K V) (h : ∀ v, (∀ i, ψ i v = 0) → v = 0) :
    Submodule.span K (Set.range ψ) = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hle⟩ := (Submodule.span K (Set.range ψ)).exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hne)
  set v := (Module.evalEquiv K V).symm f with hvd
  have hv : ∀ φ : Module.Dual K V, f φ = φ v := by
    intro φ
    have : Module.evalEquiv K V v = f := by rw [hvd, LinearEquiv.apply_symm_apply]
    rw [← this]
    rfl
  have hv0 : v = 0 := h v (fun i => by rw [← hv]; exact hle (Submodule.subset_span ⟨i, rfl⟩))
  apply hf0
  ext φ
  rw [hv, hv0, map_zero]
  rfl

end Select

end PI.Dv.TIW
