import Development.EtaleCohomology.EtaleSheaves.CoverPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.EmptyVan₂

/- English proof (translation)
Establish `h` using `Sheaf.isTerminalOfBotCover G X (Scheme.bot_mem_grothendieckTopology X)`. Prove the components needed by the constructor for the conclusion. Introduce `a b`. Establish `e` using `h.hom_ext (ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift.{1} R) _ a)) (ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift.{1} R) _ b))`. Use `congrArg (fun f => f.hom (1 : ULift.{1} R)) e` as an intermediate fact.

Simplify using `using this`.
-/
theorem sec_subsingleton {R : Type} [CommRing R] (G : Shv R) (X : Scheme.{0}) [IsEmpty X] :
    Subsingleton (G.obj.obj (op X)) := by
  have h := Sheaf.isTerminalOfBotCover G X (Scheme.bot_mem_grothendieckTopology X)
  constructor
  intro a b
  have e := h.hom_ext (ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift.{1} R) _ a))
    (ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift.{1} R) _ b))
  have := congrArg (fun f => f.hom (1 : ULift.{1} R)) e
  simpa using this

/- English proof (translation)
Rewrite using `[IsZero.iff_id_eq_zero]`. Apply `((sheafificationAdjunction Scheme.etaleTopology _).homEquiv _ _).injective` to reduce the goal to its premises. Use extensionality with `U x`. Break down `isEmpty_or_nonempty U.unop with hU | hU` into its components or cases. Use `sec_subsingleton (R := R) ((free R).obj (yoneda.obj X)) U.unop` as an intermediate fact.

Conclude with `@Subsingleton.elim _ this _ _`. Establish `: IsEmpty ((yoneda.obj X).obj U)` using `⟨fun (f : U.unop ⟶ X) => IsEmpty.false (f.base (Classical.arbitrary U.unop))⟩`. Establish `hx : x = 0` using `Subsingleton.elim (α := ULift.{1} ((yoneda.obj X).obj U) →₀ ULift.{1} R) x 0`. Rewrite using `[hx, map_zero, map_zero]`.
-/
theorem free_isZero {R : Type} [CommRing R] (X : Scheme.{0}) [IsEmpty X] :
    IsZero ((free R).obj (yoneda.obj X)) := by
  rw [IsZero.iff_id_eq_zero]
  apply ((sheafificationAdjunction Scheme.etaleTopology _).homEquiv _ _).injective
  ext U x
  rcases isEmpty_or_nonempty U.unop with hU | hU
  · have := sec_subsingleton (R := R) ((free R).obj (yoneda.obj X)) U.unop
    exact @Subsingleton.elim _ this _ _
  · have : IsEmpty ((yoneda.obj X).obj U) := ⟨fun (f : U.unop ⟶ X) => IsEmpty.false (f.base (Classical.arbitrary U.unop))⟩
    have hx : x = 0 := Subsingleton.elim (α := ULift.{1} ((yoneda.obj X).obj U) →₀ ULift.{1} R) x 0
    rw [hx, map_zero, map_zero]

/- English proof (translation)
Break down `le_or_gt m 0 with h | h` into its components or cases. Take `⟨p, rfl⟩ : ∃ p : ℕ, m = -(p : ℤ)` from `⟨(-m).toNat, by omega⟩`. Conclude with `(free_isZero (R := R) X).of_iso (chainsXIso R _ p)`. Conclude with `HomologicalComplex.isZero_extend_X _ _ m (fun i => by`. Express the relevant statement in the definitionally equal form `-(i : ℤ) ≠ m`.

Use the proof step `omega)`.
-/
theorem chains_X_isZero {R : Type} [CommRing R] (X : Scheme.{0}) [IsEmpty X] (m : ℤ) :
    IsZero (((chains R).obj (sch.obj X)).X m) := by
  rcases le_or_gt m 0 with h | h
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, m = -(p : ℤ) := ⟨(-m).toNat, by omega⟩
    exact (free_isZero (R := R) X).of_iso (chainsXIso R _ p)
  · exact HomologicalComplex.isZero_extend_X _ _ m (fun i => by
      change -(i : ℤ) ≠ m; omega)

/- English proof (translation)
Establish `: Subsingleton (Cochain K L n)` using `⟨fun a b => Cochain.ext _ _ fun p q hpq => (hK p).eq_of_src _ _⟩`. Establish `: Subsingleton (Cocycle K L n)` using `⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩`. Prove the components needed by the constructor for the conclusion. Introduce `a b`. Take `⟨a, rfl⟩` from `QuotientAddGroup.mk_surjective a`.

Take `⟨b, rfl⟩` from `QuotientAddGroup.mk_surjective b`. Rewrite using `[Subsingleton.elim a b]`.
-/
theorem cc_subsingleton {C : Type*} [Category C] [Preadditive C] {K L : CochainComplex C ℤ}
    (hK : ∀ m, IsZero (K.X m)) (n : ℤ) : Subsingleton (CohomologyClass K L n) := by
  have : Subsingleton (Cochain K L n) :=
    ⟨fun a b => Cochain.ext _ _ fun p q hpq => (hK p).eq_of_src _ _⟩
  have : Subsingleton (Cocycle K L n) := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  constructor
  intro a b
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective b
  rw [Subsingleton.elim a b]

/- English proof (translation)
Introduce `_ q _ i n S _ hS x`. Establish `: IsEmpty (Spec (CommRingCat.of S))` using `⟨fun p => (p : PrimeSpectrum S).isPrime.ne_top (Subsingleton.elim _ _)⟩`. Use `cc_subsingleton (L := res (ZMod q) (tw q i)) (chains_X_isZero (R := ZMod q) (Spec (CommRingCat.of S))) (n + 1)` as an intermediate fact. Conclude with `Subsingleton.elim _ _`.
-/
theorem EmptyVan_of : LateralTheory.E.CoverPf.EmptyVan := by
  intro _ q _ i n S _ hS x
  have : IsEmpty (Spec (CommRingCat.of S)) :=
    ⟨fun p => (p : PrimeSpectrum S).isPrime.ne_top (Subsingleton.elim _ _)⟩
  have := cc_subsingleton (L := res (ZMod q) (tw q i)) (chains_X_isZero (R := ZMod q) (Spec (CommRingCat.of S))) (n + 1)
  exact Subsingleton.elim _ _

end LateralTheory.E.EmptyVan₂
