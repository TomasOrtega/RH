import Mathlib

noncomputable section

namespace PI.Dv.TIW

section Span

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Apply `hw` to reduce the goal to its premises. Rewrite using `[← Module.forall_dual_apply_eq_zero_iff K w]`. Introduce `φ`.

Assume the negation of the conclusion as `hφ`. Conclude with `h ((φ w)⁻¹ • φ) (by simp [inv_mul_cancel₀ hφ])`.
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
Proceed by induction on `z using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => rw [map_add, LinearMap.add_apply]`. Conclude with `add_mem ha hb`. Consider the case `single x r`.

Rewrite using `[Representation.asAlgebraHom_single, LinearMap.smul_apply]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)`.
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
Take `⟨φ, hφ⟩` from `exists_dual_one (K := K) w hw`. Conclude with `⟨φ.smulRight u, by rw [LinearMap.smulRight_apply, hφ, one_smul]⟩`.
-/
theorem exists_end_map (w u : W) (hw : w ≠ 0) : ∃ M : Module.End K W, M w = u := by
  obtain ⟨φ, hφ⟩ := exists_dual_one (K := K) w hw
  exact ⟨φ.smulRight u, by rw [LinearMap.smulRight_apply, hφ, one_smul]⟩

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce `u _`. Take `⟨M, hM⟩` from `exists_end_map (K := K) w u hw`. Take `⟨z, hz⟩` from `hirr M`. Use `asAlgebraHom_mem_span τ z w` as an intermediate fact.

Rewrite `this` using `[hz, hM]`. Then use the resulting hypothesis.
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
Take `⟨w, hw⟩` from `exists_ne (0 : W)`. Rewrite using `[← finrank_top, ← span_orbit τ hirr w hw]`. Conclude with `finrank_range_le_card _`.
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
Take `⟨κ, a, -, hsp, hli⟩` from `exists_linearIndependent'.{0} K F`. Rewrite `hsp` using `[hF]`. Set `b` to `Module.Basis.mk hli (by rw [hsp])`. Use `letI := FiniteDimensional.fintypeBasisIndex b`. Establish `hc : Fintype.card κ = Module.finrank K V` using `(Module.finrank_eq_card_basis b).symm`.

Set `e` to `Fintype.equivFinOfCardEq hc`. Use `⟨a ∘ e.symm, ?_⟩` and prove the remaining obligations. Use `hli.comp e.symm e.symm.injective` as an intermediate fact. Simplify `this` using `[Function.comp_assoc]`.
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
Establish `h` using `linearIndependent_iff_card_eq_finrank_span.mp hu`. Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Use `show Set.finrank K (Set.range u) = _`. Rewrite using `[← h, Fintype.card_fin, hn]`.
-/
theorem li_span_top {n : ℕ} (u : Fin n → V) (hu : LinearIndependent K u) (hn : n = Module.finrank K V) :
    Submodule.span K (Set.range u) = ⊤ := by
  have h := linearIndependent_iff_card_eq_finrank_span.mp hu
  apply Submodule.eq_top_of_finrank_eq
  show Set.finrank K (Set.range u) = _
  rw [← h, Fintype.card_fin, hn]

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨f, hf0, hle⟩` from `(Submodule.span K (Set.range ψ)).exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hne)`. Use `set v := (Module.evalEquiv K V).symm f with hvd`. Establish `hv : ∀ φ : Module.Dual K V, f φ = φ v`. Introduce `φ`.

Establish `: Module.evalEquiv K V v = f` using `by rw [hvd, LinearEquiv.apply_symm_apply]`. Rewrite using `[← this]`. Both sides reduce to the same expression. Establish `hv0 : v = 0` using `h v (fun i => by rw [← hv]; exact hle (Submodule.subset_span ⟨i, rfl⟩))`. Apply `hf0` to reduce the goal to its premises.

Use extensionality with `φ`. Rewrite using `[hv, hv0, map_zero]`. Both sides reduce to the same expression.
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
