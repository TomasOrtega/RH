import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace GlobalTheory

/- English proof (translation)
Introduce `a b hab`. Rewrite using `[← sub_eq_zero, ← basicOpen_eq_bot_iff]`. Establish `h0 : j ⁻¹ᵁ Z.basicOpen (a - b) = ⊥`. Rewrite using `[Scheme.preimage_basicOpen, map_sub, hab, sub_self, Scheme.basicOpen_zero]`. Assume the negation of the conclusion as `hne`.

Take `⟨z, hz⟩` from `(Opens.ne_bot_iff_nonempty _).mp hne`. Take `⟨x, hx1, ⟨y, rfl⟩⟩` from `hj.inter_open_nonempty _ (Z.basicOpen (a - b)).isOpen ⟨z, hz⟩`. Establish `: y ∈ j ⁻¹ᵁ Z.basicOpen (a - b)` using `hx1`. Rewrite `this` using `[h0]`. Conclude with `this`.
-/
theorem app_injective_of_dense_range {T Z : Scheme.{0}} [IsReduced Z] (j : T ⟶ Z) [IsOpenImmersion j]
    (hj : Dense (Set.range j)) (W : Z.Opens) : Function.Injective (j.app W).hom := by
  intro a b hab
  rw [← sub_eq_zero, ← basicOpen_eq_bot_iff]
  have h0 : j ⁻¹ᵁ Z.basicOpen (a - b) = ⊥ := by
    rw [Scheme.preimage_basicOpen, map_sub, hab, sub_self, Scheme.basicOpen_zero]
  by_contra hne
  obtain ⟨z, hz⟩ := (Opens.ne_bot_iff_nonempty _).mp hne
  obtain ⟨x, hx1, ⟨y, rfl⟩⟩ := hj.inter_open_nonempty _ (Z.basicOpen (a - b)).isOpen ⟨z, hz⟩
  have : y ∈ j ⁻¹ᵁ Z.basicOpen (a - b) := hx1
  rw [h0] at this
  exact this

/- English proof (translation)
Take `rfl : i' = (Opens.map j.base).map i` from `Subsingleton.elim _ _`. Use `congrArg (fun f => f.hom a) (j.naturality i.op)` as an intermediate fact. Simplify using `using this`.
-/
theorem app_res_eq {T Z : Scheme.{0}} (j : T ⟶ Z) {V W : Z.Opens} (i : V ⟶ W)
    (i' : j ⁻¹ᵁ V ⟶ j ⁻¹ᵁ W) (a : Γ(Z, W)) :
    j.app V (Z.presheaf.map i.op a) = T.presheaf.map i'.op (j.app W a) := by
  obtain rfl : i' = (Opens.map j.base).map i := Subsingleton.elim _ _
  have := congrArg (fun f => f.hom a) (j.naturality i.op)
  simpa using this

/- English proof (translation)
Introduce `T Z _ j _ hj U s hloc`. Use `choose W hWU hmem h hh using hloc`. Set `Wf : U → Z.Opens` to `fun u => W u.1 u.2`. Establish `hcover : U ≤ iSup Wf` using `fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, hmem x hx⟩`. Take `⟨g, hg, -⟩` from `Z.sheaf.existsUnique_gluing' Wf U (fun u => homOfLE (hWU u.1 u.2)) hcover (fun u => h u.1 u.2) (by`.

Introduce `u v`. Apply `app_injective_of_dense_range j hj` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `j.app _ (Z.presheaf.map _ (h u.1 u.2)) = j.app _ (Z.presheaf.map _ (h v.1 v.2))`. Rewrite using `[app_res_eq j _ (homOfLE (j.preimage_mono inf_le_left)), app_res_eq j _ (homOfLE (j.preimage_mono inf_le_right)), hh, hh]`. Simplify using `only [← ConcreteCategory.comp_apply, ← Functor.map_comp]`.

Use the proof step `rfl)`. Set `g' : Γ(Z, U)` to `g`. Establish `hg' : ∀ u : U, Z.presheaf.map (homOfLE (hWU u.1 u.2)).op g' = h u.1 u.2` using `hg`. Use `⟨g', ?_⟩` and prove the remaining obligations. Use `T.sheaf.eq_of_locally_eq' (fun u : U => j ⁻¹ᵁ Wf u) (j ⁻¹ᵁ U) (fun u => homOfLE (j.preimage_mono (hWU u.1 u.2))) ?_ _ _ ?_` and prove the remaining obligations.

Introduce `x hx`. Conclude with `Opens.mem_iSup.2 ⟨⟨j x, hx⟩, hmem _ hx⟩`. Introduce `u`. Establish `key : T.presheaf.map (homOfLE (j.preimage_mono (hWU u.1 u.2))).op (j.app U g') = T.presheaf.map (homOfLE (j.preimage_mono (hWU u.1 u.2))).op s`. Rewrite using `[← app_res_eq j (homOfLE (hWU u.1 u.2)), hg' u, hh]`.

Conclude with `key`.
-/
theorem glue_of_dense_openImmersion : ∀ {T Z : Scheme.{0}} [IsReduced Z] (j : T ⟶ Z) [IsOpenImmersion j], Dense (Set.range j) →
    ∀ (U : Z.Opens) (s : Γ(T, j ⁻¹ᵁ U)), (∀ u ∈ U, ∃ (W : Z.Opens) (hWU : W ≤ U), u ∈ W ∧
      ∃ h : Γ(Z, W), j.app W h = T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s) →
    ∃ h : Γ(Z, U), j.app U h = s := by
  intro T Z _ j _ hj U s hloc
  choose W hWU hmem h hh using hloc
  let Wf : U → Z.Opens := fun u => W u.1 u.2
  have hcover : U ≤ iSup Wf := fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, hmem x hx⟩
  obtain ⟨g, hg, -⟩ := Z.sheaf.existsUnique_gluing' Wf U (fun u => homOfLE (hWU u.1 u.2)) hcover
    (fun u => h u.1 u.2) (by
      intro u v
      apply app_injective_of_dense_range j hj
      change j.app _ (Z.presheaf.map _ (h u.1 u.2)) = j.app _ (Z.presheaf.map _ (h v.1 v.2))
      rw [app_res_eq j _ (homOfLE (j.preimage_mono inf_le_left)),
        app_res_eq j _ (homOfLE (j.preimage_mono inf_le_right)), hh, hh]
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl)
  let g' : Γ(Z, U) := g
  have hg' : ∀ u : U, Z.presheaf.map (homOfLE (hWU u.1 u.2)).op g' = h u.1 u.2 := hg
  refine ⟨g', ?_⟩
  refine T.sheaf.eq_of_locally_eq' (fun u : U => j ⁻¹ᵁ Wf u) (j ⁻¹ᵁ U)
    (fun u => homOfLE (j.preimage_mono (hWU u.1 u.2))) ?_ _ _ ?_
  · intro x hx
    exact Opens.mem_iSup.2 ⟨⟨j x, hx⟩, hmem _ hx⟩
  · intro u
    have key : T.presheaf.map (homOfLE (j.preimage_mono (hWU u.1 u.2))).op (j.app U g') =
        T.presheaf.map (homOfLE (j.preimage_mono (hWU u.1 u.2))).op s := by
      rw [← app_res_eq j (homOfLE (hWU u.1 u.2)), hg' u, hh]
    exact key

end GlobalTheory
