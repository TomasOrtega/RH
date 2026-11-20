import Development.EtaleCohomology.CohomologicalPurity.LeafFreeCokPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

variable {R : Type} [CommRing R]

/- English proof (translation)
Introduce and unpack `V g ⟨⟨t₁, h₁⟩, ⟨t₂, h₂⟩⟩`. Conclude with `⟨t₁ + t₂, by rw [map_add, map_add, h₁, h₂]⟩`.
-/
theorem imageSieve_add' {F G : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (f : F ⟶ G) {T : Scheme.{0}}
    (s₁ s₂ : G.obj (op T)) :
    Presheaf.imageSieve f s₁ ⊓ Presheaf.imageSieve f s₂ ≤ Presheaf.imageSieve f (s₁ + s₂) := by
  rintro V g ⟨⟨t₁, h₁⟩, ⟨t₂, h₂⟩⟩
  exact ⟨t₁ + t₂, by rw [map_add, map_add, h₁, h₂]⟩

/- English proof (translation)
Introduce and unpack `V g ⟨t, h⟩`. Conclude with `⟨r • t, by rw [map_smul, map_smul, h]⟩`.
-/
theorem imageSieve_smul' {F G : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (f : F ⟶ G) {T : Scheme.{0}}
    (r : ULift.{1} R) (s : G.obj (op T)) :
    Presheaf.imageSieve f s ≤ Presheaf.imageSieve f (r • s) := by
  rintro V g ⟨t, h⟩
  exact ⟨r • t, by rw [map_smul, map_smul, h]⟩

/- English proof (translation)
Use extensionality with `V g`. Simplify using `only [Sieve.top_apply, iff_true]`. Conclude with `⟨0, by rw [map_zero, map_zero]⟩`.
-/
theorem imageSieve_zero' {F G : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (f : F ⟶ G) {T : Scheme.{0}} :
    Presheaf.imageSieve f (0 : G.obj (op T)) = ⊤ := by
  ext V g
  simp only [Sieve.top_apply, iff_true]
  exact ⟨0, by rw [map_zero, map_zero]⟩

/- English proof (translation)
Establish `e : cokernel.π ((freeP R).map i') ≫ pcok R i' i a b w = (freeP R).map b ≫ cokernel.π _`. Simplify using `[pcok]`. Use `ConcreteCategory.congr_hom (NatTrans.congr_app e V) m` as an intermediate fact. Simplify `this` using `only [NatTrans.comp_app, ConcreteCategory.comp_apply]`.
-/
theorem pcok_π_apply (R : Type) [CommRing R] {A' B' A B : PSh} (i' : A' ⟶ B') (i : A ⟶ B) (a : A' ⟶ A)
    (b : B' ⟶ B) (w : i' ≫ b = a ≫ i) (V : Scheme.{0}ᵒᵖ) (m : ((freeP R).obj B').obj V) :
    (pcok R i' i a b w).app V ((cokernel.π ((freeP R).map i')).app V m) =
      (cokernel.π ((freeP R).map i)).app V (((freeP R).map b).app V m) := by
  have e : cokernel.π ((freeP R).map i') ≫ pcok R i' i a b w = (freeP R).map b ≫ cokernel.π _ := by
    simp [pcok]
  have := ConcreteCategory.congr_hom (NatTrans.congr_app e V) m
  simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply] using this

/- English proof (translation)
Use `ConcreteCategory.congr_hom (NatTrans.congr_app (cokernel.condition ((freeP R).map i)) V) m` as an intermediate fact. Simplify using `only [NatTrans.comp_app, ConcreteCategory.comp_apply] at this`. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem π_freeP_apply (R : Type) [CommRing R] {A B : PSh} (i : A ⟶ B) (V : Scheme.{0}ᵒᵖ)
    (m : ((freeP R).obj A).obj V) :
    (cokernel.π ((freeP R).map i)).app V (((freeP R).map i).app V m) = 0 := by
  have := ConcreteCategory.congr_hom (NatTrans.congr_app (cokernel.condition ((freeP R).map i)) V) m
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at this
  rw [this]; rfl

/- English proof (translation)
Conclude with `ModuleCat.free_map_apply _ _`.
-/
theorem freePresheaf_map_freeMk (R : Type) [CommRing R] {A B : PSh} (i : A ⟶ B) (V : Scheme.{0}ᵒᵖ) (x : A.obj V) :
    ((freeP R).map i).app V (ModuleCat.freeMk (ULift.up x)) = ModuleCat.freeMk (ULift.up (i.app V x)) := by
  exact ModuleCat.free_map_apply _ _

/- English proof (translation)
Conclude with `ModuleCat.free_map_apply _ _`.
-/
theorem freePresheaf_obj_map_freeMk (R : Type) [CommRing R] (B : PSh) {V W : Scheme.{0}ᵒᵖ} (g : V ⟶ W) (x : B.obj V) :
    ((freeP R).obj B).map g (ModuleCat.freeMk (ULift.up x)) = ModuleCat.freeMk (ULift.up (B.map g x)) := by
  exact ModuleCat.free_map_apply _ _

/- English proof (translation)
Establish `: Epi ((cokernel.π ((freeP R).map i)).app V)` using `inferInstance`. Conclude with `(ModuleCat.epi_iff_surjective _).1 this`.
-/
theorem π_app_surj (R : Type) [CommRing R] {A B : PSh} (i : A ⟶ B) (V : Scheme.{0}ᵒᵖ) :
    Function.Surjective ((cokernel.π ((freeP R).map i)).app V) := by
  have : Epi ((cokernel.π ((freeP R).map i)).app V) := inferInstance
  exact (ModuleCat.epi_iff_surjective _).1 this

/- English proof (translation)
Set `J` to `Scheme.etaleTopology.{0}`. Set `N : Submodule (ULift.{1} R) (((freeP R).obj B).obj (op T))` to `{ carrier := {v | Presheaf.imageSieve (pcok R i' i a b w) ((cokernel.π ((freeP R).map i)).app (op T) v) ∈ J T} zero_mem' := by`. Simplify using `only [Set.mem_setOf_eq]`. Rewrite using `[map_zero, imageSieve_zero']`. Conclude with `J.top_mem T`.

Use the proof step `add_mem' := fun {v₁ v₂} h₁ h₂ => by`. Simplify using `only [Set.mem_setOf_eq] at *`. Rewrite using `[map_add]`. Conclude with `J.superset_covering (imageSieve_add' _ _ _) (J.intersection_covering h₁ h₂)`. Use the proof step `smul_mem' := fun r v h => by`.

Simplify using `only [Set.mem_setOf_eq] at *`. Rewrite using `[map_smul]`. Conclude with `J.superset_covering (imageSieve_smul' _ _ _) h }`. Establish `gen : ∀ x, ModuleCat.freeMk x ∈ N`. Introduce and unpack `⟨y⟩`.

Use `show Presheaf.imageSieve _ _ ∈ J T`. Take `⟨S, hS, hS'⟩` from `h2 T y`. Use `J.superset_covering ?_ hS` and prove the remaining obligations. Introduce `V g hg`. Establish `nat` using `NatTrans.naturality_apply (cokernel.π ((freeP R).map i)) g.op (ModuleCat.freeMk (ULift.up y))`.

Break down `hS' g hg with ⟨x₀, hx₀⟩ | ⟨y', hy'⟩` into its components or cases. Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[map_zero]`. Use `erw [← nat]`. Rewrite using `[freePresheaf_obj_map_freeMk]`.

Use `erw [← hx₀]`. Rewrite using `[← freePresheaf_map_freeMk R i (op V) x₀]`. Conclude with `(π_freeP_apply R i (op V) _).symm`. Use `⟨_, (pcok_π_apply R i' i a b w (op V) (ModuleCat.freeMk (ULift.up y'))).trans ?_⟩` and prove the remaining obligations. Rewrite using `[freePresheaf_map_freeMk R b (op V) y']`.

Use `erw [hy', ← freePresheaf_obj_map_freeMk R B g.op y]`. Conclude with `nat`. Use `show v ∈ N`. Proceed by induction on `v using Finsupp.induction_linear with`. Consider the case `zero => exact N.zero_mem`.

Consider the case `add v₁ v₂ h₁ h₂ => exact N.add_mem h₁ h₂`. Consider the case `single x r`. Use `N.smul_mem r (gen x)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use `first`.

Consider the case `exact (Finsupp.smul_single_one x r).symm`. Consider the case `(unfold ModuleCat.freeMk; erw [Finsupp.smul_single_one])`.
-/
theorem exists_finset_adjoin_laurent_preimage (R : Type) [CommRing R] {A' B' A B : PSh} (i' : A' ⟶ B') (i : A ⟶ B) (a : A' ⟶ A)
    (b : B' ⟶ B) (w : i' ≫ b = a ≫ i)
    (h2 : ∀ (T : Scheme.{0}) (y : B.obj (op T)), ∃ S ∈ Scheme.etaleTopology T, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g →
      (∃ x : A.obj (op V), i.app (op V) x = B.map g.op y) ∨ ∃ y' : B'.obj (op V), b.app (op V) y' = B.map g.op y)
    (T : Scheme.{0}) (v : ((freeP R).obj B).obj (op T)) :
    Presheaf.imageSieve (pcok R i' i a b w) ((cokernel.π ((freeP R).map i)).app (op T) v) ∈
      Scheme.etaleTopology T := by
  let J := Scheme.etaleTopology.{0}
  let N : Submodule (ULift.{1} R) (((freeP R).obj B).obj (op T)) :=
    { carrier := {v | Presheaf.imageSieve (pcok R i' i a b w) ((cokernel.π ((freeP R).map i)).app (op T) v) ∈ J T}
      zero_mem' := by
        simp only [Set.mem_setOf_eq]; rw [map_zero, imageSieve_zero']; exact J.top_mem T
      add_mem' := fun {v₁ v₂} h₁ h₂ => by
        simp only [Set.mem_setOf_eq] at *
        rw [map_add]; exact J.superset_covering (imageSieve_add' _ _ _) (J.intersection_covering h₁ h₂)
      smul_mem' := fun r v h => by
        simp only [Set.mem_setOf_eq] at *
        rw [map_smul]; exact J.superset_covering (imageSieve_smul' _ _ _) h }
  have gen : ∀ x, ModuleCat.freeMk x ∈ N := by
    rintro ⟨y⟩
    show Presheaf.imageSieve _ _ ∈ J T
    obtain ⟨S, hS, hS'⟩ := h2 T y
    refine J.superset_covering ?_ hS
    intro V g hg
    have nat := NatTrans.naturality_apply (cokernel.π ((freeP R).map i)) g.op (ModuleCat.freeMk (ULift.up y))
    rcases hS' g hg with ⟨x₀, hx₀⟩ | ⟨y', hy'⟩
    · refine ⟨0, ?_⟩
      rw [map_zero]; erw [← nat]
      rw [freePresheaf_obj_map_freeMk]; erw [← hx₀]; rw [← freePresheaf_map_freeMk R i (op V) x₀]; exact (π_freeP_apply R i (op V) _).symm
    · refine ⟨_, (pcok_π_apply R i' i a b w (op V) (ModuleCat.freeMk (ULift.up y'))).trans ?_⟩
      rw [freePresheaf_map_freeMk R b (op V) y']; erw [hy', ← freePresheaf_obj_map_freeMk R B g.op y]; exact nat
  show v ∈ N
  induction v using Finsupp.induction_linear with
  | zero => exact N.zero_mem
  | add v₁ v₂ h₁ h₂ => exact N.add_mem h₁ h₂
  | single x r =>
    have := N.smul_mem r (gen x)
    convert this using 1
    first
    | exact (Finsupp.smul_single_one x r).symm
    | (unfold ModuleCat.freeMk; erw [Finsupp.smul_single_one])

/- English proof (translation)
Introduce `R _ A' B' A B i' i a b w h2`. Prove the components needed by the constructor for the conclusion. Introduce `T s`. Take `⟨v, rfl⟩` from `π_app_surj R i (op T) s`. Conclude with `exists_finset_adjoin_laurent_preimage R i' i a b w h2 T v`.
-/
theorem leafFreeCokSurj : LeafFreeCokSurj := by
  intro R _ A' B' A B i' i a b w h2
  constructor
  intro T s
  obtain ⟨v, rfl⟩ := π_app_surj R i (op T) s
  exact exists_finset_adjoin_laurent_preimage R i' i a b w h2 T v

/- English proof (translation)
The claim follows from `LeafFreeCok_of leafFreeCokSurj hI`.
-/
theorem LeafFreeCok_of_inj (hI : LeafFreeCokInj) : LeafFreeCok := LeafFreeCok_of leafFreeCokSurj hI

end LateralTheory.CohomologicalPurity
