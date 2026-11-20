import Development.EtaleCohomology.CohomologicalPurity.LeafTailPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `a b`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[← sub_eq_zero]`.

Use `set s : Γ(U, ⊤) := (a.1 : Γ(U, ⊤)) - b.1 with hs_def`. Establish `hs : ∀ i, s * w.1 i = 0` using `fun i => by rw [hs_def, sub_mul, ← a.2 i, ← b.2 i, sub_self]`. Establish `hcov : (⊤ : U.Opens) ≤ iSup fun i => U.basicOpen (w.1 i)`. Introduce `p _`. Take `⟨i, -, hp⟩` from `w.2 p`.

Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨i, hp⟩`. Use `U.sheaf.eq_of_locally_eq' (fun i => U.basicOpen (w.1 i)) ⊤ (fun i => homOfLE le_top) hcov s 0 fun i => ?_` and prove the remaining obligations. Establish `hu : IsUnit (U.presheaf.map (homOfLE (U.basicOpen_le (w.1 i))).op (w.1 i))` using `U.toRingedSpace.isUnit_res_basicOpen (w.1 i)`. Establish `h0` using `congrArg (U.presheaf.map (homOfLE (U.basicOpen_le (w.1 i))).op) (hs i)`. Rewrite `h0` using `[map_mul, map_zero]`.

Express the relevant statement in the definitionally equal form `U.presheaf.map _ s = U.presheaf.map _ 0`. Rewrite using `[map_zero]`. Conclude with `(hu.mul_left_eq_zero).1 h0`.
-/
theorem Vec.hom_subsingleton (N k : ℕ) (U : Scheme.{0}) (v w : Vec N k U) : Subsingleton (v ⟶ w) := by
  constructor
  intro a b
  apply Subtype.ext; apply Units.ext
  rw [← sub_eq_zero]
  set s : Γ(U, ⊤) := (a.1 : Γ(U, ⊤)) - b.1 with hs_def
  have hs : ∀ i, s * w.1 i = 0 := fun i => by rw [hs_def, sub_mul, ← a.2 i, ← b.2 i, sub_self]
  have hcov : (⊤ : U.Opens) ≤ iSup fun i => U.basicOpen (w.1 i) := by
    intro p _
    obtain ⟨i, -, hp⟩ := w.2 p
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hp⟩
  refine U.sheaf.eq_of_locally_eq' (fun i => U.basicOpen (w.1 i)) ⊤ (fun i => homOfLE le_top) hcov s 0 fun i => ?_
  have hu : IsUnit (U.presheaf.map (homOfLE (U.basicOpen_le (w.1 i))).op (w.1 i)) :=
    U.toRingedSpace.isUnit_res_basicOpen (w.1 i)
  have h0 := congrArg (U.presheaf.map (homOfLE (U.basicOpen_le (w.1 i))).op) (hs i)
  rw [map_mul, map_zero] at h0
  change U.presheaf.map _ s = U.presheaf.map _ 0
  rw [map_zero]
  exact (hu.mul_left_eq_zero).1 h0

/- English proof (translation)
Introduce `p hp`. Simplify using `only [off, Scheme.Hom.mem_preimage] at hp ⊢`. Introduce `hI`. Apply `hp` to reduce the goal to its premises. Establish `hI' : ∀ x ∈ I, Polynomial.C x ∈ p.asIdeal` using `fun x hx => hI hx`.

Use `show ((Ideal.map Polynomial.C I : Ideal (Polynomial A)) : Set (Polynomial A)) ⊆ p.asIdeal`. Conclude with `Ideal.map_le_iff_le_comap.2 (fun x hx => hI' x hx)`.
-/
theorem off_le_C (A : Type) [CommRing A] (I : Ideal A) : off (Polynomial A) (I.map Polynomial.C) ≤
    Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A I := by
  intro p hp
  simp only [off, Scheme.Hom.mem_preimage] at hp ⊢
  intro hI
  apply hp
  have hI' : ∀ x ∈ I, Polynomial.C x ∈ p.asIdeal := fun x hx => hI hx
  show ((Ideal.map Polynomial.C I : Ideal (Polynomial A)) : Set (Polynomial A)) ⊆ p.asIdeal
  exact Ideal.map_le_iff_le_comap.2 (fun x hx => hI' x hx)

def LeafTailNerve : Prop := ∀ (d : ℕ) (R : Type) [CommRing R] (n : SimplexCategoryᵒᵖ),
  ∃ (R' : Type) (_ : CommRing R') (_ : R →+* R')
    (e₁ : (PR (d + 1) 1 R).obj n ≅ (PR (d + 1) 1 R').obj (op (SimplexCategory.mk 0)))
    (e₂ : (PR d 0 R).obj n ≅ (PR d 0 R').obj (op (SimplexCategory.mk 0))),
    (prod.map (Pj.tail d) (𝟙 _) : PR (d + 1) 1 R ⟶ PR d 0 R).app n ≫ e₂.hom =
      e₁.hom ≫ (prod.map (Pj.tail d) (𝟙 _) : PR (d + 1) 1 R' ⟶ PR d 0 R').app (op (SimplexCategory.mk 0))

def LeafTailRep0 : Prop := ∀ (d : ℕ) (R : Type) [CommRing R],
  ∃ (A : Type) (_ : CommRing A) (I : Ideal A) (_ : R →+* A),
    I.FG ∧ ∃ (h : off (Polynomial A) (I.map Polynomial.C) ≤
        Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A I)
      (e₁ : (PR (d + 1) 1 R).obj (op (SimplexCategory.mk 0)) ≅ yoneda.obj (off (Polynomial A) (I.map Polynomial.C)).toScheme)
      (e₂ : (PR d 0 R).obj (op (SimplexCategory.mk 0)) ≅ yoneda.obj (off A I).toScheme),
      (prod.map (Pj.tail d) (𝟙 _) : PR (d + 1) 1 R ⟶ PR d 0 R).app (op (SimplexCategory.mk 0)) ≫ e₂.hom =
        e₁.hom ≫ yoneda.map ((Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).resLE _ _ h)

/- English proof (translation)
Introduce `d R _ n`. Take `⟨R', _, ψ, e₁, e₂, w₁⟩` from `hN d R n`. Take `⟨A, _, I, φ, hI, h, f₁, f₂, w₂⟩` from `h0 d R'`. Use `⟨A, inferInstance, I, φ.comp ψ, hI, h, disc.mapIso (e₁ ≪≫ f₁), disc.mapIso (e₂ ≪≫ f₂), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `disc.map _ ≫ disc.map (e₂.hom ≫ f₂.hom) = disc.map (e₁.hom ≫ f₁.hom) ≫ disc.map (yoneda.map _)`.

Rewrite using `[← Functor.map_comp, ← Functor.map_comp, ← Category.assoc, w₁, Category.assoc, w₂, Category.assoc]`.
-/
theorem LeafTailRep_of (hN : LeafTailNerve) (h0 : LeafTailRep0) : LeafTailRep := by
  intro d R _ n
  obtain ⟨R', _, ψ, e₁, e₂, w₁⟩ := hN d R n
  obtain ⟨A, _, I, φ, hI, h, f₁, f₂, w₂⟩ := h0 d R'
  refine ⟨A, inferInstance, I, φ.comp ψ, hI, h, disc.mapIso (e₁ ≪≫ f₁), disc.mapIso (e₂ ≪≫ f₂), ?_⟩
  change disc.map _ ≫ disc.map (e₂.hom ≫ f₂.hom) = disc.map (e₁.hom ≫ f₁.hom) ≫ disc.map (yoneda.map _)
  rw [← Functor.map_comp, ← Functor.map_comp, ← Category.assoc, w₁, Category.assoc, w₂, Category.assoc]

end LateralTheory.CohomologicalPurity.Thom
