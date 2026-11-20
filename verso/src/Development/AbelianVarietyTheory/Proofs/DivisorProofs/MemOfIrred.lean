import Mathlib

universe u v

namespace GlobalTheory.CompanionTheory.BurnsideU

/- English proof (translation)
Break down `subsingleton_or_nontrivial V with hV | hV` into its components or cases. Establish `hf : f = 0` using `LinearMap.ext fun v => Subsingleton.elim _ _`. Rewrite using `[hf]`. Conclude with `S.zero_mem`. Establish `: IsScalarTower K S V` using `⟨fun _ _ _ => rfl⟩`.

Establish `: Nontrivial (Submodule S V)` using `(Submodule.nontrivial_iff S).mpr hV`. Establish `: IsSimpleModule S V` using `{ eq_bot_or_eq_top := fun N => by`. Break down `hirr (N.restrictScalars K) (fun g hg v hv => N.smul_mem ⟨g, hg⟩ hv) with h | h` into its components or cases. Conclude with `Or.inl ((Submodule.restrictScalars_eq_bot_iff K S V).mp h)`. Conclude with `Or.inr ((Submodule.restrictScalars_eq_top_iff K S V).mp h) }`.

Establish `hschur` using `IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := S) (V := V) K`. Set `F : Module.End (Module.End S V) V` to `{ toFun := f map_add' := f.map_add map_smul' := fun g v => by`. Take `⟨c, rfl⟩` from `hschur.2 g`. Express the relevant statement in the definitionally equal form `f ((algebraMap K (Module.End S V) c) v) = (algebraMap K (Module.End S V) c) (f v)`. Simplify using `[Module.algebraMap_end_apply, f.map_smul] }`.

Take `⟨s, hs⟩` from `Module.Finite.fg_top (R := K) (M := V)`. Take `⟨r, hr⟩` from `jacobson_density F s`. Establish `hfr : f = (r : Module.End K V)`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `m`.

Establish `hm : m ∈ Submodule.span K (s : Set V)` using `hs ▸ Submodule.mem_top`. Proceed by induction on `hm using Submodule.span_induction with`. Consider the case `mem m hm => exact hr m hm`. Consider the case `zero => simp`. Consider the case `add _ _ _ _ h₁ h₂ => rw [map_add, map_add, h₁, h₂]`.

Consider the case `smul c _ _ h => rw [map_smul, map_smul, h]`. Rewrite using `[hfr]`. Conclude with `r.2`.
-/
theorem mem_of_irred {K : Type u} {V : Type v} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : Subalgebra K (Module.End K V))
    (hirr : ∀ N : Submodule K V, (∀ f ∈ S, ∀ v ∈ N, f v ∈ N) → N = ⊥ ∨ N = ⊤)
    (f : Module.End K V) : f ∈ S := by
  classical
  rcases subsingleton_or_nontrivial V with hV | hV
  · have hf : f = 0 := LinearMap.ext fun v => Subsingleton.elim _ _
    rw [hf]
    exact S.zero_mem

  have : IsScalarTower K S V := ⟨fun _ _ _ => rfl⟩
  have : Nontrivial (Submodule S V) := (Submodule.nontrivial_iff S).mpr hV

  have : IsSimpleModule S V :=
    { eq_bot_or_eq_top := fun N => by
        rcases hirr (N.restrictScalars K) (fun g hg v hv => N.smul_mem ⟨g, hg⟩ hv) with h | h
        · exact Or.inl ((Submodule.restrictScalars_eq_bot_iff K S V).mp h)
        · exact Or.inr ((Submodule.restrictScalars_eq_top_iff K S V).mp h) }

  have hschur := IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := S) (V := V) K

  let F : Module.End (Module.End S V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun g v => by
        obtain ⟨c, rfl⟩ := hschur.2 g
        change f ((algebraMap K (Module.End S V) c) v) = (algebraMap K (Module.End S V) c) (f v)
        simp [Module.algebraMap_end_apply, f.map_smul] }

  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := K) (M := V)
  obtain ⟨r, hr⟩ := jacobson_density F s
  have hfr : f = (r : Module.End K V) := by
    apply LinearMap.ext
    intro m
    have hm : m ∈ Submodule.span K (s : Set V) := hs ▸ Submodule.mem_top
    induction hm using Submodule.span_induction with
    | mem m hm => exact hr m hm
    | zero => simp
    | add _ _ _ _ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
    | smul c _ _ h => rw [map_smul, map_smul, h]
  rw [hfr]
  exact r.2

/- English proof (translation)
Introduce `f`. Establish `hf : f ∈ ρ.range` using `mem_of_irred ρ.range (fun W hW => hirr W fun h w hw => hW (ρ h) ⟨h, rfl⟩ w hw) f`. Take `⟨h, rfl⟩` from `(AlgHom.mem_range ρ).mp hf`. Conclude with `⟨h, rfl⟩`.
-/
theorem burnside_surj_of_irred {A : Type u} {V : Type v} [Ring A] [Algebra ℂ A] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : A →ₐ[ℂ] Module.End ℂ V)
    (hirr : ∀ W : Submodule ℂ V, (∀ h, ∀ w ∈ W, ρ h w ∈ W) → W = ⊥ ∨ W = ⊤) :
    Function.Surjective ρ :=
    by
    intro f
    have hf : f ∈ ρ.range :=
      mem_of_irred ρ.range (fun W hW => hirr W fun h w hw => hW (ρ h) ⟨h, rfl⟩ w hw) f
    obtain ⟨h, rfl⟩ := (AlgHom.mem_range ρ).mp hf
    exact ⟨h, rfl⟩

end GlobalTheory.CompanionTheory.BurnsideU
