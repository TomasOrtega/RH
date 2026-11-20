import Mathlib

/- English proof (translation)
Introduce `R E _ _ _ _ _ _ _ T F hF`. Take `⟨I, hI, hmax⟩` from `exists_maximal_linearIndepOn R (Subtype.val : T → E)`. Use `set S : Submodule R E := Submodule.span R ((Subtype.val : T → E) '' I) with hS`. Establish `hT : ∀ y ∈ Submodule.span R T, ∃ b : R, b ≠ 0 ∧ b • y ∈ S`. Introduce `y hy`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Distinguish the cases in `h : (⟨x, hx⟩ : T) ∈ I`. Conclude with `⟨1, one_ne_zero, by`. Rewrite using `[one_smul]`.

Conclude with `Submodule.subset_span ⟨⟨x, hx⟩, h, rfl⟩⟩`. Conclude with `hmax ⟨x, hx⟩ h`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha, hax⟩` from `hx`.

Take `⟨b, hb, hby⟩` from `hy`. Use `⟨a * b, mul_ne_zero ha hb, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `S.add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`.

Conclude with `S.smul_mem _ hax`. Rewrite using `[mul_smul]`. Conclude with `S.smul_mem _ hby`. Consider the case `smul c x _ hx`. Take `⟨a, ha, hax⟩` from `hx`.

Use `⟨a, ha, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_comm]`. Conclude with `S.smul_mem _ hax`. Set `N : Submodule R F` to `S.comap F.subtype`. Establish `h0 : Module.rank R (F ⧸ N) = 0`.

Rewrite using `[rank_eq_zero_iff]`. Introduce `q`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective N q`. Take `⟨a, ha, hax⟩` from `(hF x).1 x.2`. Take `⟨b, hb, hbx⟩` from `hT _ hax`.

Use `⟨b * a, mul_ne_zero hb ha, ?_⟩` and prove the remaining obligations. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Express the relevant statement in the definitionally equal form `(b * a) • (x : E) ∈ S`. Rewrite using `[mul_smul]` and apply the resulting hypothesis. Establish `h1 : Module.rank R F = Module.rank R N`.

Rewrite using `[← rank_quotient_add_rank_of_isDomain N, h0, zero_add]`. Establish `h2 : Module.rank R N ≤ Module.rank R S`. Set `g : N →ₗ[R] S` to `(F.subtype.comp N.subtype).codRestrict S (fun x => x.2)`. Use `LinearMap.rank_le_of_injective g ?_` and prove the remaining obligations. Introduce `x y hxy`.

Establish `h : ((g x : S) : E) = ((g y : S) : E)` using `congrArg Subtype.val hxy`. Conclude with `Subtype.ext (Subtype.ext h)`. Establish `h3 : Module.rank R S ≤ Cardinal.mk I` using `(rank_span_le _).trans Cardinal.mk_image_le`. Establish `h4 : Cardinal.mk (Fin (Module.finrank R F)) ≤ Cardinal.mk I`. Rewrite using `[Cardinal.mk_fin, Module.finrank_eq_rank, h1]`.

Conclude with `h2.trans h3`. Take `⟨e⟩` from `(Cardinal.le_def _ _).1 h4`. Conclude with `⟨fun j => ((e j : T) : E), fun j => (e j : T).2, LinearIndependent.comp hI e e.injective⟩`.
-/
theorem UpperTheory.Reformulated.B.Ud9.exists_indep_of_sat :
    ∀ {R E : Type} [inst : CommRing R] [IsDomain R] [IsNoetherianRing R]
    [inst_3 : AddCommGroup E] [inst_4 : _root_.Module R E] [Module.Finite R E] [Module.IsTorsionFree R E] (T : Set E)
    (F : Submodule R E),
    (∀ (x : E), x ∈ F ↔ ∃ (a : R), a ≠ (0 : R) ∧ a • x ∈ Submodule.span R T) →
      ∃ (f : Fin (Module.finrank R ↥F) → E), (∀ (j : Fin (Module.finrank R ↥F)), f j ∈ T) ∧ LinearIndependent R f := by
  intro R E _ _ _ _ _ _ _ T F hF
  obtain ⟨I, hI, hmax⟩ := exists_maximal_linearIndepOn R (Subtype.val : T → E)
  set S : Submodule R E := Submodule.span R ((Subtype.val : T → E) '' I) with hS
  have hT : ∀ y ∈ Submodule.span R T, ∃ b : R, b ≠ 0 ∧ b • y ∈ S := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      by_cases h : (⟨x, hx⟩ : T) ∈ I
      · exact ⟨1, one_ne_zero, by
          rw [one_smul]; exact Submodule.subset_span ⟨⟨x, hx⟩, h, rfl⟩⟩
      · exact hmax ⟨x, hx⟩ h
    | zero => exact ⟨1, one_ne_zero, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, hax⟩ := hx
      obtain ⟨b, hb, hby⟩ := hy
      refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
      rw [smul_add]
      refine S.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact S.smul_mem _ hax
      · rw [mul_smul]; exact S.smul_mem _ hby
    | smul c x _ hx =>
      obtain ⟨a, ha, hax⟩ := hx
      refine ⟨a, ha, ?_⟩
      rw [smul_comm]; exact S.smul_mem _ hax
  let N : Submodule R F := S.comap F.subtype
  have h0 : Module.rank R (F ⧸ N) = 0 := by
    rw [rank_eq_zero_iff]
    intro q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N q
    obtain ⟨a, ha, hax⟩ := (hF x).1 x.2
    obtain ⟨b, hb, hbx⟩ := hT _ hax
    refine ⟨b * a, mul_ne_zero hb ha, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    change (b * a) • (x : E) ∈ S
    rwa [mul_smul]
  have h1 : Module.rank R F = Module.rank R N := by
    rw [← rank_quotient_add_rank_of_isDomain N, h0, zero_add]
  have h2 : Module.rank R N ≤ Module.rank R S := by
    let g : N →ₗ[R] S := (F.subtype.comp N.subtype).codRestrict S (fun x => x.2)
    refine LinearMap.rank_le_of_injective g ?_
    intro x y hxy
    have h : ((g x : S) : E) = ((g y : S) : E) := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h)
  have h3 : Module.rank R S ≤ Cardinal.mk I :=
    (rank_span_le _).trans Cardinal.mk_image_le
  have h4 : Cardinal.mk (Fin (Module.finrank R F)) ≤ Cardinal.mk I := by
    rw [Cardinal.mk_fin, Module.finrank_eq_rank, h1]
    exact h2.trans h3
  obtain ⟨e⟩ := (Cardinal.le_def _ _).1 h4
  exact ⟨fun j => ((e j : T) : E), fun j => (e j : T).2, LinearIndependent.comp hI e e.injective⟩
