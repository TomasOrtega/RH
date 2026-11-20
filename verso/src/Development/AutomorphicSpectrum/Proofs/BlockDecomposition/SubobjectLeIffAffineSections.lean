import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE

/- English proof (translation)
Apply `Scheme.Modules.hom_ext` to reduce the goal to its premises. Introduce `U`. Rewrite using `[Scheme.Modules.Hom.zero_app]`. Set `F : TopCat.Sheaf Ab X` to `⟨N.presheaf, N.isSheaf⟩`. Establish `key : ∀ s : Γ(M, U), φ.app U s = 0`.

Introduce `s`. Use `TopCat.Sheaf.eq_of_locally_eq' F (fun i : {V : X.affineOpens // (V : X.Opens) ≤ U} => (i.1 : X.Opens)) U (fun i => homOfLE i.2) ?_ _ _ ?_` and prove the remaining obligations. Use `fun x (hx : x ∈ U) => ?_` and prove the remaining obligations. Take `⟨W, hW, hxW, hWU⟩` from `exists_isAffineOpen_mem_and_subset hx`. Conclude with `TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWU⟩, hxW⟩`.

Introduce `i`. Establish `hnat` using `ConcreteCategory.congr_hom ((Scheme.Modules.Hom.mapPresheaf φ).naturality (homOfLE i.2).op) s`. Simplify using `only [ConcreteCategory.comp_apply] at hnat`. Establish `h2 : N.presheaf.map (homOfLE i.2).op (φ.app U s) = 0`. Rewrite using `[← h i.1 (M.presheaf.map (homOfLE i.2).op s)]`.

Conclude with `hnat.symm`. Conclude with `h2.trans (map_zero _).symm`. Use extensionality with `s`. Simplify using `[key s]`.
-/
theorem hom_eq_zero_of_affineOpens {X : Scheme.{0}} {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ (U : X.affineOpens) (s : Γ(M, (U : X.Opens))), φ.app (U : X.Opens) s = 0) : φ = 0 := by
  apply Scheme.Modules.hom_ext
  intro U
  rw [Scheme.Modules.Hom.zero_app]
  let F : TopCat.Sheaf Ab X := ⟨N.presheaf, N.isSheaf⟩
  have key : ∀ s : Γ(M, U), φ.app U s = 0 := by
    intro s
    refine TopCat.Sheaf.eq_of_locally_eq' F
      (fun i : {V : X.affineOpens // (V : X.Opens) ≤ U} => (i.1 : X.Opens)) U
      (fun i => homOfLE i.2) ?_ _ _ ?_
    · refine fun x (hx : x ∈ U) => ?_
      obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset hx
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWU⟩, hxW⟩
    · intro i
      have hnat := ConcreteCategory.congr_hom
        ((Scheme.Modules.Hom.mapPresheaf φ).naturality (homOfLE i.2).op) s
      simp only [ConcreteCategory.comp_apply] at hnat
      have h2 : N.presheaf.map (homOfLE i.2).op (φ.app U s) = 0 := by
        rw [← h i.1 (M.presheaf.map (homOfLE i.2).op s)]
        exact hnat.symm
      exact h2.trans (map_zero _).symm
  ext s
  simp [key s]

/- English proof (translation)
Unfold `GlobalTheory.CompanionTheory.GE.secs`. Prove the components needed by the constructor for the conclusion. Introduce `hST U x hx`. Take `⟨s, rfl⟩` from `hx`. Use `⟨(Subobject.ofLE S T hST).app (U : X.Opens) s, ?_⟩` and prove the remaining obligations.

Rewrite using `[← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Subobject.ofLE_arrow]`. Introduce `h`. Establish `hzero : S.arrow ≫ cokernel.π T.arrow = 0`. Apply `GlobalTheory.CompanionTheory.GE.hom_eq_zero_of_affineOpens` to reduce the goal to its premises. Introduce `U s`.

Take `⟨t, ht⟩` from `h U (Set.mem_range_self s)`. Rewrite using `[Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, ← ht, ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, cokernel.condition, Scheme.Modules.Hom.zero_app, AddCommGrpCat.zero_apply]`. Conclude with `Subobject.le_of_comm (Abelian.monoLift T.arrow S.arrow hzero) (Abelian.monoLift_comp _ _ _)`.
-/
theorem le_iff_secs_subset {X : Scheme.{0}} {E : X.Modules} (S T : Subobject E) :
    S ≤ T ↔ ∀ U : X.affineOpens, secs S (U : X.Opens) ⊆ secs T (U : X.Opens) := by
  unfold GlobalTheory.CompanionTheory.GE.secs
  constructor
  · intro hST U x hx
    obtain ⟨s, rfl⟩ := hx
    refine ⟨(Subobject.ofLE S T hST).app (U : X.Opens) s, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Subobject.ofLE_arrow]
  · intro h
    have hzero : S.arrow ≫ cokernel.π T.arrow = 0 := by
      apply GlobalTheory.CompanionTheory.GE.hom_eq_zero_of_affineOpens
      intro U s
      obtain ⟨t, ht⟩ := h U (Set.mem_range_self s)
      rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, ← ht,
        ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, cokernel.condition,
        Scheme.Modules.Hom.zero_app, AddCommGrpCat.zero_apply]
    exact Subobject.le_of_comm (Abelian.monoLift T.arrow S.arrow hzero)
      (Abelian.monoLift_comp _ _ _)

end GlobalTheory.CompanionTheory.GE
