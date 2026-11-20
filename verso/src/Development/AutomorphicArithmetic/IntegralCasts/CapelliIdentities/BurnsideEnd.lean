import Mathlib

/- English proof (translation)
Introduce `K V _ _ _ _ _ S h f`. Break down `subsingleton_or_nontrivial V with hV | hV` into its components or cases. Establish `: f = 0` using `by ext v; exact Subsingleton.elim _ _`. Rewrite using `[this]`. Conclude with `S.zero_mem`.

Use `haveI : IsSimpleModule S V := by`. Use `{ eq_bot_or_eq_top := fun N => ?_ }` and prove the remaining obligations. Break down `h (N.restrictScalars K) (fun g hg v hv => N.smul_mem (⟨g, hg⟩ : S) hv) with h1 | h1` into its components or cases. Use `left`. Conclude with `(Submodule.restrictScalars_eq_bot_iff _ _ _).1 h1`.

Use `right`. Conclude with `(Submodule.restrictScalars_eq_top_iff _ _ _).1 h1`. Establish `hs` using `(IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed K (A := S) (V := V)).2`. Set `F : Module.End (Module.End S V) V` to `{ toFun := f map_add' := f.map_add map_smul' := fun φ v => by`. Take `⟨c, rfl⟩` from `hs φ`.

Simplify using `[Module.End.smul_def, Module.algebraMap_end_apply] }`. Set `b` to `Module.finBasis K V`. Take `⟨r, hr⟩` from `jacobson_density (R := S) F (Finset.univ.image b)`. Establish `: f = (r : Module.End K V)`. Use `b.ext fun i => ?_` and prove the remaining obligations.

Conclude with `hr (b i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))`. Rewrite using `[this]`. Conclude with `r.2`.
-/
theorem UpperTheory.Reformulated.B.Qj3.burnside_end.{u_3, u_4} :
    ∀ {K : Type u_3} {V : Type u_4} [inst : Field K] [IsAlgClosed K] [inst_2 : AddCommGroup V]
    [inst_3 : _root_.Module K V] [FiniteDimensional K V] (S : Subalgebra K (Module.End K V)),
    (∀ (N : Submodule K V), (∀ f ∈ S, ∀ v ∈ N, (f : V → V) v ∈ N) → N = ⊥ ∨ N = ⊤) → ∀ (f : Module.End K V), f ∈ S := by
  intro K V _ _ _ _ _ S h f
  rcases subsingleton_or_nontrivial V with hV | hV
  · have : f = 0 := by ext v; exact Subsingleton.elim _ _
    rw [this]; exact S.zero_mem
  haveI : IsSimpleModule S V := by
    refine { eq_bot_or_eq_top := fun N => ?_ }
    rcases h (N.restrictScalars K) (fun g hg v hv => N.smul_mem (⟨g, hg⟩ : S) hv) with h1 | h1
    · left
      exact (Submodule.restrictScalars_eq_bot_iff _ _ _).1 h1
    · right
      exact (Submodule.restrictScalars_eq_top_iff _ _ _).1 h1
  have hs := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed K (A := S) (V := V)).2
  let F : Module.End (Module.End S V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun φ v => by
        obtain ⟨c, rfl⟩ := hs φ
        simp [Module.End.smul_def, Module.algebraMap_end_apply] }
  classical
  let b := Module.finBasis K V
  obtain ⟨r, hr⟩ := jacobson_density (R := S) F (Finset.univ.image b)
  have : f = (r : Module.End K V) := by
    refine b.ext fun i => ?_
    exact hr (b i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  rw [this]; exact r.2
