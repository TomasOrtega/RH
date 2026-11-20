import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.SheafH

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory Limits Opposite Abelian TopologicalSpace

universe w' v u

section Site

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}]

instance freeSheafMap_mono {U V : C} (f : U ⟶ V) [Mono f] : Mono (freeSheafMap J f) := by
  have : ∀ X, Mono ((yoneda.map f).app X) := fun X =>
    (mono_iff_injective _).2 (fun a b h => (cancel_mono f).1 h)
  have : Mono (Functor.whiskerRight (yoneda.map f) AddCommGrpCat.free) :=
    NatTrans.mono_of_mono_app _
  exact (presheafToSheaf J AddCommGrpCat.{v}).map_mono _

/- English proof (translation)
Introduce `s`. Use `⟨freeSheafHomAddEquiv V I (Injective.factorThru ((freeSheafHomAddEquiv U I).symm s) (freeSheafMap J f)), ?_⟩` and prove the remaining obligations. Rewrite using `[← freeSheafHomAddEquiv_naturality_left, Injective.comp_factorThru, AddEquiv.apply_symm_apply]`.
-/
theorem surjective_map_of_injective (I : Sheaf J AddCommGrpCat.{v}) [Injective I] {U V : C}
    (f : U ⟶ V) [Mono f] : Function.Surjective (I.obj.map f.op) := by
  intro s
  refine ⟨freeSheafHomAddEquiv V I
    (Injective.factorThru ((freeSheafHomAddEquiv U I).symm s) (freeSheafMap J f)), ?_⟩
  rw [← freeSheafHomAddEquiv_naturality_left, Injective.comp_factorThru,
    AddEquiv.apply_symm_apply]

end Site

section Space

variable {X : TopCat.{u}}

/- English proof (translation)
Establish `: Mono i.unop` using `⟨fun _ _ _ => Subsingleton.elim _ _⟩`. Rewrite using `[AddCommGrpCat.epi_iff_surjective]`. Conclude with `surjective_map_of_injective I i.unop`.
-/
theorem isFlasque_of_injective (I : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [Injective I] : TopCat.Presheaf.IsFlasque I.obj where
  epi {U V} i := by
    have : Mono i.unop := ⟨fun _ _ _ => Subsingleton.elim _ _⟩
    rw [AddCommGrpCat.epi_iff_surjective]
    exact surjective_map_of_injective I i.unop

variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `F _ U x`. Set `S` to `ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)`. Establish `hS : S.ShortExact` using `{ exact := ShortComplex.exact_cokernel (Injective.ι F) }`.

Establish `: TopCat.Presheaf.IsFlasque S.X₁.obj` using `inferInstanceAs (TopCat.Presheaf.IsFlasque F.obj)`. Establish `: TopCat.Presheaf.IsFlasque S.X₂.obj` using `isFlasque_of_injective (Injective.under F)`. Take `⟨y, rfl⟩` from `Ext.covariant_sequence_exact₁ (freeSheaf _ U) hS x (by`. Establish `: Injective S.X₂` using `inferInstanceAs (Injective (Injective.under F))`. Conclude with `Ext.eq_zero_of_injective _) (zero_add 1)`.

Establish `hsurj : Function.Surjective (S.g.hom.app (op U))` using `(AddCommGrpCat.epi_iff_surjective _).1 (TopCat.Sheaf.IsFlasque.epi_of_shortExact (X := X) (U := U) hS)`. Take `⟨z, hz⟩` from `hsurj (H'.equiv₀ S.X₃ U y)`. Take `⟨w, rfl⟩` from `(H'.equiv₀ S.X₂ U).surjective z`. Establish `: y = (show Ext (freeSheaf _ U) S.X₂ 0 from w).comp (Ext.mk₀ S.g) (add_zero 0)`. Apply `(H'.equiv₀ S.X₃ U).injective` to reduce the goal to its premises.

Rewrite using `[← hz, ← H'.equiv₀_naturality]`. Both sides reduce to the same expression. Rewrite using `[this, Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]`. Consider the case `succ n ih`. Introduce `F _ U x`.

Set `S` to `ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)`. Establish `hS : S.ShortExact` using `{ exact := ShortComplex.exact_cokernel (Injective.ι F) }`. Establish `: TopCat.Presheaf.IsFlasque S.X₁.obj` using `inferInstanceAs (TopCat.Presheaf.IsFlasque F.obj)`. Establish `: TopCat.Presheaf.IsFlasque S.X₂.obj` using `isFlasque_of_injective (Injective.under F)`. Establish `: TopCat.Presheaf.IsFlasque S.X₃.obj` using `TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ (X := X) hS`.

Take `⟨y, rfl⟩` from `Ext.covariant_sequence_exact₁ (freeSheaf _ U) hS x (by`. Establish `: Injective S.X₂` using `inferInstanceAs (Injective (Injective.under F))`. Conclude with `Ext.eq_zero_of_injective _) (n₀ := n + 1) rfl`. Rewrite using `[ih S.X₃ U y, Ext.zero_comp]`.
-/
theorem ext_freeSheaf_eq_zero_of_isFlasque (n : ℕ) :
    ∀ (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      [TopCat.Presheaf.IsFlasque F.obj] (U : Opens X)
      (x : Ext (freeSheaf (Opens.grothendieckTopology X) U) F (n + 1)), x = 0 := by
  induction n with
  | zero =>
    intro F _ U x
    let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
      (cokernel.condition _)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel (Injective.ι F) }
    have : TopCat.Presheaf.IsFlasque S.X₁.obj := inferInstanceAs (TopCat.Presheaf.IsFlasque F.obj)
    have : TopCat.Presheaf.IsFlasque S.X₂.obj := isFlasque_of_injective (Injective.under F)
    obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₁ (freeSheaf _ U) hS x
      (by
        have : Injective S.X₂ := inferInstanceAs (Injective (Injective.under F))
        exact Ext.eq_zero_of_injective _) (zero_add 1)

    have hsurj : Function.Surjective (S.g.hom.app (op U)) :=
      (AddCommGrpCat.epi_iff_surjective _).1
        (TopCat.Sheaf.IsFlasque.epi_of_shortExact (X := X) (U := U) hS)
    obtain ⟨z, hz⟩ := hsurj (H'.equiv₀ S.X₃ U y)
    obtain ⟨w, rfl⟩ := (H'.equiv₀ S.X₂ U).surjective z
    have : y = (show Ext (freeSheaf _ U) S.X₂ 0 from w).comp (Ext.mk₀ S.g) (add_zero 0) := by
      apply (H'.equiv₀ S.X₃ U).injective
      rw [← hz, ← H'.equiv₀_naturality]
      rfl
    rw [this, Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]
  | succ n ih =>
    intro F _ U x
    let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
      (cokernel.condition _)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel (Injective.ι F) }
    have : TopCat.Presheaf.IsFlasque S.X₁.obj := inferInstanceAs (TopCat.Presheaf.IsFlasque F.obj)
    have : TopCat.Presheaf.IsFlasque S.X₂.obj := isFlasque_of_injective (Injective.under F)
    have : TopCat.Presheaf.IsFlasque S.X₃.obj :=
      TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ (X := X) hS
    obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₁ (freeSheaf _ U) hS x
      (by
        have : Injective S.X₂ := inferInstanceAs (Injective (Injective.under F))
        exact Ext.eq_zero_of_injective _) (n₀ := n + 1) rfl
    rw [ih S.X₃ U y, Ext.zero_comp]

/- English proof (translation)
The claim follows from `ext_freeSheaf_eq_zero_of_isFlasque n F U x`.
-/
theorem H'_eq_zero_of_isFlasque (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [TopCat.Presheaf.IsFlasque F.obj] (n : ℕ) (U : Opens X) (x : F.H' (n + 1) U) : x = 0 :=
  ext_freeSheaf_eq_zero_of_isFlasque n F U x

/- English proof (translation)
Apply `(cohomologyPresheafTerminalAddEquiv F (n + 1) (T := ⊤) isTerminalTop).symm.injective` to reduce the goal to its premises. Rewrite using `[map_zero]`. Conclude with `H'_eq_zero_of_isFlasque F n ⊤ _`.
-/
theorem H_eq_zero_of_isFlasque (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [TopCat.Presheaf.IsFlasque F.obj] (n : ℕ) (x : Sheaf.H F (n + 1)) : x = 0 := by
  apply (cohomologyPresheafTerminalAddEquiv F (n + 1) (T := ⊤) isTerminalTop).symm.injective
  rw [map_zero]
  exact H'_eq_zero_of_isFlasque F n ⊤ _

instance subsingleton_H_of_isFlasque (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [TopCat.Presheaf.IsFlasque F.obj] (n : ℕ) : Subsingleton (Sheaf.H F (n + 1)) :=
  subsingleton_of_forall_eq 0 (H_eq_zero_of_isFlasque F n)

end Space

end GroundTheory.Arith.SchemeCoh
